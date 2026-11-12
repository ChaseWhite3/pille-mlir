// Lowers selected functions of a verified MLIR module into SMT dialect queries.
//
// The pass is driven entirely by a JSON manifest generated from Rhombus
// declarations: it has no built-in knowledge of any custom operation. For every
// instance of a modeled operation it instantiates the declared semantic
// expression at the instance's actual operand and result types, so supporting a
// new operation never requires editing or rebuilding this file.
//
// Build against the same LLVM installation that supplies mlir-opt.
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SMT/IR/SMTDialect.h"
#include "mlir/Dialect/SMT/IR/SMTOps.h"
#include "mlir/Dialect/SMT/IR/SMTTypes.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Pass/PassRegistry.h"
#include "mlir/Tools/Plugins/PassPlugin.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <optional>
#include <string>
#include <vector>

using namespace mlir;
namespace json = llvm::json;

namespace {

/// The integer widths of the supported fragment. Each maps to an SMT bitvector
/// of exactly the same width; nothing is widened, narrowed, or reinterpreted.
bool isSupportedWidth(uint64_t width) {
  return width == 1 || width == 8 || width == 16 || width == 32 || width == 64;
}

/// Width of a supported signless integer type, or 0.
unsigned supportedWidth(Type type) {
  auto integer = llvm::dyn_cast<IntegerType>(type);
  if (!integer || !integer.isSignless() || !isSupportedWidth(integer.getWidth()))
    return 0;
  return integer.getWidth();
}

unsigned bitvectorWidth(Value value) {
  return llvm::cast<smt::BitVectorType>(value.getType()).getWidth();
}

/// One modeled operation, as described by the manifest. The JSON pointers stay
/// valid for the lifetime of the parsed manifest document.
struct OperationModel {
  std::vector<std::string> operands;
  std::string result;
  std::vector<std::pair<std::string, const json::Value *>> locals;
  const json::Value *value = nullptr;
  /// Predicates over the operands and locals that every use must satisfy.
  const json::Array *requirements = nullptr;
};

/// The references an expression may use. Semantic expressions see an
/// operation's operands and locals; properties see function inputs and the
/// returned value. A tag outside its scope is a malformed manifest.
struct Scope {
  StringRef description;
  ArrayRef<Value> operands;
  ArrayRef<Value> locals;
  unsigned resultWidth = 0; // semantic scope: width of the modeled result
  ArrayRef<Value> inputs;
  Value result; // property scope: the lowered return value
  bool semantic = false;
};

// The first query for a function owns these operations. Later queries clone
// this already-lowered body, renaming declarations for their display names.
// Every query has its own SolverOp, so none of its assertions can affect any
// other query. The cache is local to one manifest and therefore one model.
struct LoweredFunction {
  SmallVector<Operation *> operations;
  SmallVector<Value> inputs;
  Value returned;
  SmallVector<Value> obligations;
};

using FunctionCache = llvm::StringMap<LoweredFunction>;

class QueryBuilder {
public:
  QueryBuilder(ModuleOp module, const json::Object &manifest,
               const json::Object &specification, FunctionCache &cache,
               std::optional<unsigned> index = std::nullopt)
      : module(module), manifest(manifest), specification(specification),
        cache(cache), index(index), builder(module.getContext()) {}

  LogicalResult run();
  LogicalResult checkResult();

private:
  InFlightDiagnostic malformed(const Twine &message) {
    auto diagnostic = module.emitError();
    if (index)
      diagnostic << "SMT batch spec " << *index << ": ";
    diagnostic << "malformed SMT query manifest: " << message;
    return diagnostic;
  }
  InFlightDiagnostic error(Location location, const Twine &message) {
    auto diagnostic = emitError(location);
    if (index)
      diagnostic << "SMT batch spec " << *index << ": ";
    diagnostic << message;
    return diagnostic;
  }

  LogicalResult readManifest();
  LogicalResult checkFunction();
  LogicalResult lowerBody();
  LogicalResult lowerModeled(Operation *op, const OperationModel &model);
  LogicalResult lowerConstant(arith::ConstantOp op);

  Value lowerTerm(const json::Value &expression, const Scope &scope,
                  Location location);
  Value lowerFormula(const json::Value &expression, const Scope &scope,
                     Location location);
  std::optional<unsigned> literalWidth(const json::Array &spec,
                                       const Scope &scope, Location location);
  std::optional<unsigned> termWidth(const json::Value &expression,
                                    const Scope &scope, Location location);
  Value lowerLiteral(const json::Array &node, const Scope &scope,
                     Location location);

  ModuleOp module;
  const json::Object &manifest;
  const json::Object &specification;
  FunctionCache &cache;
  std::optional<unsigned> index;
  OpBuilder builder;

  std::string functionName;
  std::vector<std::pair<std::string, unsigned>> inputs;
  std::optional<unsigned> expectedResultWidth;
  llvm::StringMap<OperationModel> models;
  llvm::StringSet<> unmodeled;
  const json::Array *preconditions = nullptr;
  const json::Value *property = nullptr;
  bool enumerateValues = false;
  std::string resultSymbol;
  std::string definedSymbol;

  func::FuncOp function;
  llvm::DenseMap<Value, Value> values;
  SmallVector<Value> inputValues;
  Value returned;
  /// What the modeled operations require of their operands, one predicate per
  /// requirement per instance. These are proved together with the property.
  SmallVector<Value> obligations;
};

LogicalResult QueryBuilder::readManifest() {
  auto name = specification.getString("function");
  const json::Array *inputList = specification.getArray("inputs");
  const json::Object *operations = manifest.getObject("operations");
  const json::Array *unmodeledList = manifest.getArray("unmodeled");
  preconditions = specification.getArray("preconditions");
  property = specification.get("property");
  auto mode = specification.getString("mode");
  enumerateValues = mode == StringRef("values");
  if (mode && *mode != "values" && *mode != "proof") {
    malformed("unknown query mode");
    return failure();
  }
  if (!name || !inputList || !operations || !unmodeledList || !preconditions ||
      (!property && !enumerateValues)) {
    malformed("missing a required field");
    return failure();
  }
  functionName = name->str();

  for (const json::Value &entry : *inputList) {
    const json::Object *input = entry.getAsObject();
    auto inputName = input ? input->getString("name") : std::nullopt;
    auto width = input ? input->getInteger("width") : std::nullopt;
    if (!inputName || !width || !isSupportedWidth(*width)) {
      malformed("invalid input declaration");
      return failure();
    }
    inputs.emplace_back(inputName->str(), unsigned(*width));
  }
  if (enumerateValues) {
    auto resultName = specification.getString("result_symbol");
    auto definedName = specification.getString("defined_symbol");
    if (!resultName || resultName->empty() || !definedName ||
        definedName->empty() || *resultName == *definedName) {
      malformed("values queries require distinct result_symbol and defined_symbol names");
      return failure();
    }
    for (const auto &input : inputs) {
      if (input.first == *resultName || input.first == *definedName) {
        malformed("a values query output symbol collides with an input name");
        return failure();
      }
    }
    resultSymbol = resultName->str();
    definedSymbol = definedName->str();
  }
  if (const json::Value *width = specification.get("result_width")) {
    if (!width->getAsNull()) {
      auto number = width->getAsInteger();
      if (!number || !isSupportedWidth(*number)) {
        malformed("invalid result width");
        return failure();
      }
      expectedResultWidth = unsigned(*number);
    }
  }
  for (const json::Value &entry : *unmodeledList) {
    auto operation = entry.getAsString();
    if (!operation) {
      malformed("invalid unmodeled operation name");
      return failure();
    }
    unmodeled.insert(*operation);
  }
  for (const auto &entry : *operations) {
    const json::Object *description = entry.second.getAsObject();
    const json::Array *operands =
        description ? description->getArray("operands") : nullptr;
    const json::Array *locals =
        description ? description->getArray("locals") : nullptr;
    auto result = description ? description->getString("result") : std::nullopt;
    const json::Value *value = description ? description->get("value") : nullptr;
    if (!operands || !locals || !result || !value) {
      malformed("invalid semantics for operation '" +
                StringRef(entry.first.str()) + "'");
      return failure();
    }
    OperationModel model;
    model.result = result->str();
    model.value = value;
    model.requirements = description->getArray("requires");
    for (const json::Value &operand : *operands) {
      auto operandName = operand.getAsString();
      if (!operandName) {
        malformed("invalid operand name");
        return failure();
      }
      model.operands.push_back(operandName->str());
    }
    for (const json::Value &local : *locals) {
      const json::Array *pair = local.getAsArray();
      auto label =
          pair && pair->size() == 2 ? (*pair)[0].getAsString() : std::nullopt;
      if (!label) {
        malformed("invalid local binding");
        return failure();
      }
      model.locals.emplace_back(label->str(), &(*pair)[1]);
    }
    models.try_emplace(entry.first.str(), std::move(model));
  }
  return success();
}

/// Function-level attributes that cannot change the value computed by a
/// straight-line body. Anything else is rejected rather than ignored.
bool isNeutralFunctionAttribute(StringRef name) {
  return name == "sym_name" || name == "function_type" ||
         name == "sym_visibility";
}

LogicalResult QueryBuilder::checkFunction() {
  for (Operation &op : *module.getBody()) {
    auto candidate = llvm::dyn_cast<func::FuncOp>(&op);
    if (candidate && candidate.getSymName() == functionName) {
      function = candidate;
      break;
    }
  }
  if (!function) {
    error(module.getLoc(), "SMT query: function @" + functionName +
                               " was not found as a func.func in the module");
    return failure();
  }
  Location location = function.getLoc();
  if (function.isExternal()) {
    error(location, "SMT query: function @" + functionName +
                        " is a declaration without a body");
    return failure();
  }
  for (NamedAttribute attribute : function->getAttrs()) {
    if (!isNeutralFunctionAttribute(attribute.getName().strref())) {
      error(location, "SMT query: unsupported attribute '" +
                          attribute.getName().strref() + "' on function @" +
                          functionName +
                          "; attributes are rejected rather than ignored");
      return failure();
    }
  }
  if (!llvm::hasSingleElement(function.getBody())) {
    error(location,
          "SMT query: unsupported control flow: function @" + functionName +
              " has " + Twine(function.getBody().getBlocks().size()) +
              " blocks, but only straight-line single-block bodies are "
              "supported");
    return failure();
  }
  FunctionType type = function.getFunctionType();
  if (type.getNumResults() != 1) {
    error(location, "SMT query: function @" + functionName + " returns " +
                        Twine(type.getNumResults()) +
                        " values; exactly one scalar result is supported");
    return failure();
  }
  unsigned resultWidth = supportedWidth(type.getResult(0));
  if (!resultWidth) {
    error(location, "SMT query: unsupported result type ")
        << type.getResult(0) << " of function @" << functionName
        << "; supported types are i1, i8, i16, i32, and i64";
    return failure();
  }
  if (expectedResultWidth && *expectedResultWidth != resultWidth) {
    error(location, "SMT query: the property refers to a " +
                        Twine(*expectedResultWidth) +
                        "-bit result, but function @" + functionName +
                        " returns ")
        << type.getResult(0);
    return failure();
  }
  if (type.getNumInputs() != inputs.size()) {
    error(location, "SMT query: function @" + functionName + " has " +
                        Twine(type.getNumInputs()) + " arguments, but " +
                        Twine(inputs.size()) + " inputs were declared");
    return failure();
  }
  for (unsigned index = 0; index < inputs.size(); ++index) {
    unsigned width = supportedWidth(type.getInput(index));
    if (!width) {
      error(location, "SMT query: unsupported type ")
          << type.getInput(index) << " of argument " << index
          << " of function @" << functionName
          << "; supported types are i1, i8, i16, i32, and i64";
      return failure();
    }
    if (width != inputs[index].second) {
      error(location, "SMT query: input '" + inputs[index].first +
                          "' is declared with width " +
                          Twine(inputs[index].second) + ", but argument " +
                          Twine(index) + " of function @" + functionName +
                          " has type ")
          << type.getInput(index);
      return failure();
    }
  }
  return success();
}

/// The width of an expression, computed without emitting any operation. A
/// literal's `like` target contributes only its width, never its value.
std::optional<unsigned> QueryBuilder::termWidth(const json::Value &expression,
                                                const Scope &scope,
                                                Location location) {
  const json::Array *node = expression.getAsArray();
  auto tag = node && !node->empty() ? (*node)[0].getAsString() : std::nullopt;
  if (!tag) {
    malformed("invalid expression in " + scope.description);
    return std::nullopt;
  }
  auto index = node->size() == 2 ? (*node)[1].getAsInteger() : std::nullopt;
  auto select = [&](ArrayRef<Value> candidates) -> std::optional<unsigned> {
    if (!index || *index < 0 || uint64_t(*index) >= candidates.size()) {
      malformed("reference out of range in " + scope.description);
      return std::nullopt;
    }
    return bitvectorWidth(candidates[*index]);
  };
  if (*tag == "operand" && scope.semantic)
    return select(scope.operands);
  if (*tag == "local" && scope.semantic)
    return select(scope.locals);
  if (*tag == "const" && node->size() == 3 && (*node)[2].getAsArray())
    return literalWidth(*(*node)[2].getAsArray(), scope, location);
  if ((*tag == "add" || *tag == "sub" || *tag == "mul") && node->size() == 3) {
    std::optional<unsigned> lhs = termWidth((*node)[1], scope, location);
    if (!lhs)
      return std::nullopt;
    std::optional<unsigned> rhs = termWidth((*node)[2], scope, location);
    if (!rhs)
      return std::nullopt;
    if (*lhs != *rhs) {
      error(location, "SMT query: bv." + *tag + " in " + scope.description +
                          " combines a " + Twine(*lhs) + "-bit value with a " +
                          Twine(*rhs) +
                          "-bit value; widths must be equal and are never "
                          "coerced or assumed equal");
      return std::nullopt;
    }
    return lhs;
  }
  if (*tag == "select" && node->size() == 5 && scope.semantic) {
    // Only the width is wanted here; the comparison and the agreement of the
    // arms are checked where the choice is lowered.
    return termWidth((*node)[3], scope, location);
  }
  malformed("unsupported expression '" + *tag + "' in " + scope.description);
  return std::nullopt;
}

std::optional<unsigned> QueryBuilder::literalWidth(const json::Array &spec,
                                                   const Scope &scope,
                                                   Location location) {
  auto kind = spec.empty() ? std::nullopt : spec[0].getAsString();
  if (kind == StringRef("width") && spec.size() == 2) {
    auto width = spec[1].getAsInteger();
    if (width && isSupportedWidth(*width))
      return unsigned(*width);
  } else if (kind == StringRef("like") && spec.size() == 2 && scope.semantic) {
    const json::Array *target = spec[1].getAsArray();
    if (target && target->size() == 1 &&
        (*target)[0].getAsString() == StringRef("result"))
      return scope.resultWidth;
    return termWidth(spec[1], scope, location);
  }
  malformed("invalid literal width in " + scope.description);
  return std::nullopt;
}

/// Literal policy, shared with the Rhombus front end: a literal for width w
/// must lie in [-2^(w-1), 2^w - 1]. Negative values denote their two's
/// complement residue. Anything else is rejected, never truncated.
Value QueryBuilder::lowerLiteral(const json::Array &node, const Scope &scope,
                                 Location location) {
  auto text = node.size() == 3 ? node[1].getAsString() : std::nullopt;
  const json::Array *spec = node.size() == 3 ? node[2].getAsArray() : nullptr;
  if (!text || !spec) {
    malformed("invalid literal in " + scope.description);
    return {};
  }
  std::optional<unsigned> width = literalWidth(*spec, scope, location);
  if (!width)
    return {};
  StringRef digits = *text;
  bool negative = digits.consume_front("-");
  // 80 bits hold every accepted magnitude and reject absurd inputs early.
  if (digits.empty() || digits.size() > 20 ||
      !llvm::all_of(digits, [](char c) { return c >= '0' && c <= '9'; })) {
    malformed("invalid literal digits in " + scope.description);
    return {};
  }
  llvm::APInt magnitude(80, digits, 10);
  llvm::APInt limit = negative
                          ? llvm::APInt::getOneBitSet(80, *width - 1)
                          : llvm::APInt::getLowBitsSet(80, *width);
  if (magnitude.ugt(limit)) {
    error(location, "SMT query: literal " + *text + " in " +
                        scope.description + " does not fit in " +
                        Twine(*width) +
                        " bits (accepted range is -2^(w-1) through 2^w-1)");
    return {};
  }
  llvm::APInt value = magnitude.trunc(*width);
  if (negative)
    value.negate();
  return smt::BVConstantOp::create(builder, location, value);
}

Value QueryBuilder::lowerTerm(const json::Value &expression,
                              const Scope &scope, Location location) {
  const json::Array *node = expression.getAsArray();
  auto tag = node && !node->empty() ? (*node)[0].getAsString() : std::nullopt;
  if (!tag) {
    malformed("invalid expression in " + scope.description);
    return {};
  }
  auto index = node->size() == 2 ? (*node)[1].getAsInteger() : std::nullopt;
  auto select = [&](ArrayRef<Value> candidates) -> Value {
    if (!index || *index < 0 || uint64_t(*index) >= candidates.size()) {
      malformed("reference out of range in " + scope.description);
      return {};
    }
    return candidates[*index];
  };
  if (*tag == "operand" && scope.semantic)
    return select(scope.operands);
  if (*tag == "local" && scope.semantic)
    return select(scope.locals);
  if (*tag == "input" && !scope.semantic)
    return select(scope.inputs);
  if (*tag == "result" && !scope.semantic && node->size() == 1)
    return scope.result;
  if (*tag == "const")
    return lowerLiteral(*node, scope, location);
  if ((*tag == "add" || *tag == "sub" || *tag == "mul") && node->size() == 3) {
    Value lhs = lowerTerm((*node)[1], scope, location);
    if (!lhs)
      return {};
    Value rhs = lowerTerm((*node)[2], scope, location);
    if (!rhs)
      return {};
    if (lhs.getType() != rhs.getType()) {
      error(location, "SMT query: bv." + *tag + " in " + scope.description +
                          " combines a " + Twine(bitvectorWidth(lhs)) +
                          "-bit value with a " + Twine(bitvectorWidth(rhs)) +
                          "-bit value; widths must be equal and are never "
                          "coerced or assumed equal");
      return {};
    }
    if (*tag == "add")
      return smt::BVAddOp::create(builder, location, lhs, rhs);
    if (*tag == "mul")
      return smt::BVMulOp::create(builder, location, lhs, rhs);
    // The SMT dialect has no subtraction operation. Wrapping subtraction is
    // exactly addition of the two's complement negation.
    Value negated = smt::BVNegOp::create(builder, location, rhs);
    return smt::BVAddOp::create(builder, location, lhs, negated);
  }
  if (*tag == "select" && node->size() == 5 && scope.semantic) {
    Value parts[4];
    for (unsigned i = 0; i < 4; ++i) {
      parts[i] = lowerTerm((*node)[i + 1], scope, location);
      if (!parts[i])
        return {};
    }
    for (unsigned i = 0; i < 4; i += 2) {
      if (parts[i].getType() == parts[i + 1].getType())
        continue;
      error(location, "SMT query: bv.if in " + scope.description +
                          (i == 0 ? " compares a " : " chooses between a ") +
                          Twine(bitvectorWidth(parts[i])) +
                          "-bit value and a " +
                          Twine(bitvectorWidth(parts[i + 1])) +
                          "-bit value; widths must be equal and are never "
                          "coerced or assumed equal");
      return {};
    }
    Value test = smt::EqOp::create(builder, location, parts[0], parts[1]);
    return smt::IteOp::create(builder, location, test, parts[2], parts[3]);
  }
  malformed("unsupported expression '" + *tag + "' in " + scope.description);
  return {};
}

Value QueryBuilder::lowerFormula(const json::Value &expression,
                                 const Scope &scope, Location location) {
  const json::Array *node = expression.getAsArray();
  auto tag = node && !node->empty() ? (*node)[0].getAsString() : std::nullopt;
  if (!tag) {
    malformed("invalid predicate in " + scope.description);
    return {};
  }
  if (*tag == "eq" && node->size() == 3) {
    Value lhs = lowerTerm((*node)[1], scope, location);
    if (!lhs)
      return {};
    Value rhs = lowerTerm((*node)[2], scope, location);
    if (!rhs)
      return {};
    if (lhs.getType() != rhs.getType()) {
      error(location, "SMT query: equality in " + scope.description +
                          " compares a " + Twine(bitvectorWidth(lhs)) +
                          "-bit value with a " + Twine(bitvectorWidth(rhs)) +
                          "-bit value");
      return {};
    }
    return smt::EqOp::create(builder, location, lhs, rhs);
  }
  if (*tag == "not" && node->size() == 2) {
    Value input = lowerFormula((*node)[1], scope, location);
    if (!input)
      return {};
    return smt::NotOp::create(builder, location, input);
  }
  if ((*tag == "and" || *tag == "or") && node->size() >= 2) {
    SmallVector<Value> operands;
    for (const json::Value &child : llvm::drop_begin(*node)) {
      Value operand = lowerFormula(child, scope, location);
      if (!operand)
        return {};
      operands.push_back(operand);
    }
    if (operands.size() == 1)
      return operands.front();
    Type boolean = smt::BoolType::get(module.getContext());
    if (*tag == "and")
      return smt::AndOp::create(builder, location, boolean, operands);
    return smt::OrOp::create(builder, location, boolean, operands);
  }
  malformed("unsupported predicate '" + *tag + "' in " + scope.description);
  return {};
}

LogicalResult QueryBuilder::lowerConstant(arith::ConstantOp op) {
  Location location = op.getLoc();
  for (NamedAttribute attribute : op->getAttrs()) {
    if (attribute.getName().strref() != "value") {
      error(location, "SMT query: unsupported attribute '" +
                          attribute.getName().strref() +
                          "' on arith.constant");
      return failure();
    }
  }
  unsigned width = supportedWidth(op.getType());
  auto value = llvm::dyn_cast<IntegerAttr>(op.getValue());
  if (!width || !value) {
    error(location, "SMT query: unsupported constant of type ")
        << op.getType() << "; supported types are i1, i8, i16, i32, and i64";
    return failure();
  }
  values[op.getResult()] =
      smt::BVConstantOp::create(builder, location, value.getValue());
  return success();
}

LogicalResult QueryBuilder::lowerModeled(Operation *op,
                                         const OperationModel &model) {
  Location location = op->getLoc();
  std::string name = op->getName().getStringRef().str();
  // IRDL describes structure only, and dynamically registered operations carry
  // no effect interfaces. Attaching semantics declares a pure, total model, so
  // a missing interface is accepted while a known effect is rejected.
  if (auto effects = llvm::dyn_cast<MemoryEffectOpInterface>(op)) {
    if (!effects.hasNoEffect()) {
      error(location, "SMT query: operation '" + name +
                          "' has known memory effects, which the pure SMT "
                          "model cannot represent");
      return failure();
    }
  }
  if (op->hasTrait<OpTrait::IsTerminator>() || op->getNumSuccessors() != 0) {
    error(location, "SMT query: operation '" + name +
                        "' is a terminator; control flow is unsupported");
    return failure();
  }
  if (op->getNumRegions() != 0) {
    error(location, "SMT query: operation '" + name +
                        "' has regions, which are unsupported");
    return failure();
  }
  // The declared model cannot observe attributes, so an attribute could carry
  // meaning that the proof would silently ignore.
  if (!op->getAttrs().empty()) {
    error(location, "SMT query: operation '" + name + "' carries attribute '" +
                        op->getAttrs().front().getName().strref() +
                        "'; attribute-dependent semantics are unsupported and "
                        "attributes are rejected rather than ignored");
    return failure();
  }
  if (op->getNumOperands() != model.operands.size() ||
      op->getNumResults() != 1) {
    error(location, "SMT query: operation '" + name + "' has " +
                        Twine(op->getNumOperands()) + " operands and " +
                        Twine(op->getNumResults()) +
                        " results, which is incompatible with its declared "
                        "semantics (" +
                        Twine(model.operands.size()) +
                        " operands, 1 result)");
    return failure();
  }
  SmallVector<Value> operands;
  for (unsigned index = 0; index < op->getNumOperands(); ++index) {
    Value operand = op->getOperand(index);
    if (!supportedWidth(operand.getType())) {
      error(location, "SMT query: operand '" + model.operands[index] +
                          "' of operation '" + name +
                          "' has unsupported type ")
          << operand.getType()
          << "; supported types are i1, i8, i16, i32, and i64";
      return failure();
    }
    Value lowered = values.lookup(operand);
    if (!lowered) {
      error(location, "SMT query: internal error: operand '" +
                          model.operands[index] + "' of operation '" + name +
                          "' has no lowered value");
      return failure();
    }
    operands.push_back(lowered);
  }
  unsigned resultWidth = supportedWidth(op->getResult(0).getType());
  if (!resultWidth) {
    error(location, "SMT query: result '" + model.result + "' of operation '" +
                        name + "' has unsupported type ")
        << op->getResult(0).getType()
        << "; supported types are i1, i8, i16, i32, and i64";
    return failure();
  }

  std::string description = "the semantics of '" + name + "'";
  SmallVector<Value> locals;
  Scope scope;
  scope.description = description;
  scope.semantic = true;
  scope.operands = operands;
  scope.resultWidth = resultWidth;
  for (const auto &local : model.locals) {
    scope.locals = locals;
    Value value = lowerTerm(*local.second, scope, location);
    if (!value)
      return failure();
    locals.push_back(value);
  }
  scope.locals = locals;
  Value result = lowerTerm(*model.value, scope, location);
  if (!result)
    return failure();
  if (bitvectorWidth(result) != resultWidth) {
    error(location, "SMT query: the semantics of '" + name + "' produce a " +
                        Twine(bitvectorWidth(result)) + "-bit value for result '" +
                        model.result + "', whose type is ")
        << op->getResult(0).getType()
        << "; widths are never coerced or assumed equal";
    return failure();
  }
  if (model.requirements) {
    std::string requirement = "a requirement of '" + name + "'";
    scope.description = requirement;
    for (const json::Value &predicate : *model.requirements) {
      Value obligation = lowerFormula(predicate, scope, location);
      if (!obligation)
        return failure();
      obligations.push_back(obligation);
    }
  }
  values[op->getResult(0)] = result;
  return success();
}

LogicalResult QueryBuilder::lowerBody() {
  Block &block = function.getBody().front();
  for (unsigned index = 0; index < inputs.size(); ++index) {
    Type type = smt::BitVectorType::get(module.getContext(),
                                        inputs[index].second);
    Value input = smt::DeclareFunOp::create(
        builder, function.getLoc(), type,
        builder.getStringAttr(inputs[index].first));
    values[block.getArgument(index)] = input;
    inputValues.push_back(input);
  }
  for (Operation &op : block) {
    StringRef name = op.getName().getStringRef();
    if (auto constant = llvm::dyn_cast<arith::ConstantOp>(&op)) {
      if (failed(lowerConstant(constant)))
        return failure();
      continue;
    }
    if (auto terminator = llvm::dyn_cast<func::ReturnOp>(&op)) {
      if (terminator.getNumOperands() != 1 || !terminator->getAttrs().empty()) {
        error(op.getLoc(), "SMT query: unsupported return in function @" +
                               functionName);
        return failure();
      }
      returned = values.lookup(terminator.getOperand(0));
      continue;
    }
    auto model = models.find(name);
    if (model != models.end()) {
      if (failed(lowerModeled(&op, model->second)))
        return failure();
      continue;
    }
    if (unmodeled.contains(name)) {
      error(op.getLoc(), "SMT query: operation '" + name +
                             "' has no declared SMT semantics; add an smt "
                             "clause to its declaration");
      return failure();
    }
    error(op.getLoc(),
          "SMT query: unsupported operation '" + name +
              "'; only arith.constant, func.return, and operations with "
              "declared SMT semantics are supported");
    return failure();
  }
  if (!returned) {
    error(function.getLoc(), "SMT query: function @" + functionName +
                                 " does not return a supported value");
    return failure();
  }
  return success();
}

/// A final structural check: the query must contain only operations and types
/// that the stock SMT-LIB exporter understands for this fragment.
LogicalResult QueryBuilder::checkResult() {
  static const llvm::StringSet<> allowed = {
      "smt.solver", "smt.set_logic", "smt.declare_fun", "smt.bv.constant",
      "smt.bv.add", "smt.bv.mul",    "smt.bv.neg",      "smt.eq",
      "smt.ite",
      "smt.not",    "smt.and",       "smt.or",          "smt.assert",
      "smt.check",  "smt.yield"};
  bool valid = true;
  module->walk([&](Operation *op) {
    if (op == module.getOperation())
      return;
    if (!allowed.contains(op->getName().getStringRef())) {
      error(op->getLoc(), "SMT query: internal error: residual operation '" +
                              op->getName().getStringRef() + "'");
      valid = false;
    }
    for (Type type : op->getResultTypes()) {
      auto bitvector = llvm::dyn_cast<smt::BitVectorType>(type);
      if (!llvm::isa<smt::BoolType>(type) &&
          !(bitvector && isSupportedWidth(bitvector.getWidth()))) {
        error(op->getLoc(), "SMT query: internal error: residual type ")
            << type;
        valid = false;
      }
    }
  });
  return valid ? success() : failure();
}

LogicalResult QueryBuilder::run() {
  if (failed(readManifest()) || failed(checkFunction()))
    return failure();

  Location location = function.getLoc();
  builder.setInsertionPointToEnd(module.getBody());
  smt::SolverOp solver =
      smt::SolverOp::create(builder, location, TypeRange{}, ValueRange{});
  Block &body = solver.getBodyRegion().emplaceBlock();
  builder.setInsertionPointToEnd(&body);
  smt::SetLogicOp::create(builder, location, StringRef("QF_BV"));

  auto existing = cache.find(functionName);
  if (existing == cache.end()) {
    if (failed(lowerBody()))
      return failure();
    LoweredFunction prepared;
    // Capture exactly the body, before adding this question's assertions.
    // The first operation is set_logic, whose scope belongs to each query.
    for (Operation &op : llvm::drop_begin(body))
      prepared.operations.push_back(&op);
    prepared.inputs = inputValues;
    prepared.returned = returned;
    prepared.obligations = obligations;
    cache.try_emplace(functionName, std::move(prepared));
  } else {
    IRMapping mapping;
    const LoweredFunction &prepared = existing->second;
    for (Operation *op : prepared.operations)
      builder.clone(*op, mapping);
    for (auto [position, input] : llvm::enumerate(prepared.inputs)) {
      Value cloned = mapping.lookup(input);
      cloned.getDefiningOp<smt::DeclareFunOp>().setNamePrefixAttr(
          builder.getStringAttr(inputs[position].first));
      inputValues.push_back(cloned);
    }
    returned = mapping.lookup(prepared.returned);
    for (Value obligation : prepared.obligations)
      obligations.push_back(mapping.lookup(obligation));
  }

  // Assert the preconditions and the negation of what is to be shown: the
  // property, and that every operation was used within what its model
  // requires. No other assumption is added.
  Scope scope;
  scope.inputs = inputValues;
  scope.result = returned;
  unsigned index = 0;
  for (const json::Value &precondition : *preconditions) {
    std::string description = "precondition " + std::to_string(index++);
    scope.description = description;
    Value assumption = lowerFormula(precondition, scope, location);
    if (!assumption)
      return failure();
    smt::AssertOp::create(builder, location, assumption);
  }
  if (enumerateValues) {
    // Expose the result and definedness separately. The caller first asks if
    // any admitted input violates a requirement, so enumeration cannot hide
    // partial functions by filtering away their undefined inputs.
    Value result = smt::DeclareFunOp::create(
        builder, location, returned.getType(), builder.getStringAttr(resultSymbol));
    smt::AssertOp::create(
        builder, location, smt::EqOp::create(builder, location, result, returned));
    Value one = smt::BVConstantOp::create(builder, location, llvm::APInt(1, 1));
    Value definedValue = one;
    if (!obligations.empty()) {
      Value condition = obligations.size() == 1
                            ? obligations.front()
                            : smt::AndOp::create(
                                  builder, location,
                                  smt::BoolType::get(module.getContext()),
                                  obligations);
      Value zero = smt::BVConstantOp::create(builder, location, llvm::APInt(1, 0));
      definedValue = smt::IteOp::create(builder, location, condition, one, zero);
    }
    Value defined = smt::DeclareFunOp::create(
        builder, location, one.getType(), builder.getStringAttr(definedSymbol));
    smt::AssertOp::create(
        builder, location, smt::EqOp::create(builder, location, defined, definedValue));
  } else {
    scope.description = "the property";
    Value goal = lowerFormula(*property, scope, location);
    if (!goal)
      return failure();
    if (!obligations.empty()) {
      obligations.push_back(goal);
      goal = smt::AndOp::create(builder, location,
                                smt::BoolType::get(module.getContext()),
                                obligations);
    }
    smt::AssertOp::create(builder, location,
                          smt::NotOp::create(builder, location, goal));
  }

  smt::CheckOp check = smt::CheckOp::create(builder, location, TypeRange{});
  for (Region &region : check->getRegions()) {
    region.emplaceBlock();
    smt::CheckOp::ensureTerminator(region, builder, location);
  }
  smt::SolverOp::ensureTerminator(solver.getBodyRegion(), builder, location);

  return success();
}

class SmtQueryPass
    : public PassWrapper<SmtQueryPass, OperationPass<ModuleOp>> {
public:
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(SmtQueryPass)

  SmtQueryPass() = default;
  SmtQueryPass(const SmtQueryPass &other) : PassWrapper(other) {}

  StringRef getArgument() const final { return "pille-smt-query"; }
  StringRef getDescription() const final {
    return "Lower functions to isolated SMT dialect queries using declared "
           "operation semantics";
  }
  void getDependentDialects(DialectRegistry &registry) const override {
    registry.insert<smt::SMTDialect>();
  }

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto buffer = llvm::MemoryBuffer::getFile(manifest.getValue());
    if (!buffer) {
      module.emitError() << "cannot read SMT query manifest '"
                         << manifest.getValue()
                         << "': " << buffer.getError().message();
      return signalPassFailure();
    }
    llvm::Expected<json::Value> document = json::parse((*buffer)->getBuffer());
    if (!document) {
      module.emitError() << "malformed SMT query manifest: "
                         << llvm::toString(document.takeError());
      return signalPassFailure();
    }
    const json::Object *root = document->getAsObject();
    if (!root) {
      module.emitError() << "malformed SMT query manifest: expected an object";
      return signalPassFailure();
    }
    auto version = root->getInteger("version");
    if (root->getString("format") != StringRef("pille-smt-query") ||
        (version != int64_t(1) && version != int64_t(2))) {
      module.emitError() << "malformed SMT query manifest: expected format "
                           "\"pille-smt-query\" version 1 or 2";
      return signalPassFailure();
    }
    SmallVector<Operation *> sourceOperations;
    for (Operation &op : *module.getBody())
      sourceOperations.push_back(&op);
    FunctionCache cache;
    if (version == int64_t(1)) {
      if (failed(QueryBuilder(module, *root, *root, cache).run()))
        return signalPassFailure();
    } else {
      const json::Array *queries = root->getArray("queries");
      if (!queries) {
        module.emitError() << "malformed SMT query manifest: missing queries array";
        return signalPassFailure();
      }
      for (auto [index, entry] : llvm::enumerate(*queries)) {
        const json::Object *specification = entry.getAsObject();
        if (!specification) {
          module.emitError() << "SMT batch spec " << index
                             << ": expected a query object";
          return signalPassFailure();
        }
        if (failed(QueryBuilder(module, *root, *specification, cache, index).run()))
          return signalPassFailure();
      }
    }
    // Remove the source only after every selected body has been prepared. Its
    // custom operations must never reach the stock SMT-LIB exporter.
    for (Operation *op : sourceOperations)
      op->erase();
    if (failed(QueryBuilder(module, *root, *root, cache).checkResult()) ||
        failed(verify(module)))
      return signalPassFailure();

    // Optional private sidecar: one standalone module per solver, printed by
    // MLIR itself. The host can expose members lazily without N subprocesses
    // or having to split/parse MLIR text.
    if (auto path = root->getString("query_modules")) {
      json::Array printed;
      for (Operation &solver : *module.getBody()) {
        OwningOpRef<ModuleOp> standalone = ModuleOp::create(module.getLoc());
        standalone->getBody()->push_back(solver.clone());
        std::string text;
        llvm::raw_string_ostream stream(text);
        standalone->print(stream, OpPrintingFlags().enableDebugInfo());
        stream << '\n';
        printed.push_back(std::move(text));
      }
      std::error_code code;
      llvm::raw_fd_ostream output(*path, code);
      if (code) {
        module.emitError() << "cannot write SMT query modules '" << *path
                           << "': " << code.message();
        return signalPassFailure();
      }
      output << json::Value(std::move(printed));
      output.close();
      if (output.has_error()) {
        module.emitError() << "cannot finish writing SMT query modules '" << *path << "'";
        output.clear_error();
        return signalPassFailure();
      }
    }
  }

  Option<std::string> manifest{
      *this, "manifest",
      llvm::cl::desc("Path of the JSON manifest describing the query")};
};
} // namespace

extern "C" PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK mlirGetPassPluginInfo() {
  return {MLIR_PLUGIN_API_VERSION, "PilleSmtQuery", "0.1",
          []() { PassRegistration<SmtQueryPass>(); }};
}
