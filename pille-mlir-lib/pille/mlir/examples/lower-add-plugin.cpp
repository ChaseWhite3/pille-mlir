// A minimal executable semantics for the IRDL-defined rhombus.add operation.
// Build against the same LLVM installation that supplies mlir-opt.
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Pass/PassRegistry.h"
#include "mlir/Tools/Plugins/PassPlugin.h"
#include "mlir/Transforms/GreedyPatternRewriteDriver.h"
#include <utility>

namespace {
class LowerAddPattern : public mlir::RewritePattern {
public:
  explicit LowerAddPattern(mlir::MLIRContext *context)
      : RewritePattern("rhombus.add", /*benefit=*/1, context) {}

  mlir::LogicalResult
  matchAndRewrite(mlir::Operation *op,
                  mlir::PatternRewriter &rewriter) const override {
    // IRDL verifies these conditions when the dialect is loaded. Checking here
    // also keeps this example well-defined if used with unregistered input.
    if (op->getNumOperands() != 2 || op->getNumResults() != 1)
      return mlir::failure();
    auto type = op->getResult(0).getType();
    if ((!type.isSignlessInteger(32) && !type.isSignlessInteger(64)) ||
        op->getOperand(0).getType() != type ||
        op->getOperand(1).getType() != type)
      return mlir::failure();
    // No overflow flags: this is wrapping integer addition.
    rewriter.replaceOpWithNewOp<mlir::arith::AddIOp>(
        op, op->getOperand(0), op->getOperand(1));
    return mlir::success();
  }
};

class LowerAddPass
    : public mlir::PassWrapper<LowerAddPass,
                               mlir::OperationPass<mlir::ModuleOp>> {
public:
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(LowerAddPass)

  llvm::StringRef getArgument() const final { return "pille-lower-add"; }
  llvm::StringRef getDescription() const final {
    return "Lower rhombus.add to wrapping arith.addi";
  }
  void getDependentDialects(mlir::DialectRegistry &registry) const override {
    registry.insert<mlir::arith::ArithDialect>();
  }
  void runOnOperation() override {
    mlir::RewritePatternSet patterns(&getContext());
    patterns.add<LowerAddPattern>(&getContext());
    if (mlir::failed(mlir::applyPatternsGreedily(getOperation(),
                                               std::move(patterns))))
      signalPassFailure();
  }
};
} // namespace

extern "C" mlir::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
mlirGetPassPluginInfo() {
  return {MLIR_PLUGIN_API_VERSION, "PilleLowerAdd", "0.1", []() {
            mlir::PassRegistration<LowerAddPass>();
          }};
}
