// Valid builtin MLIR, but invalid for the IRDL-defined rhombus.add operation:
// both operands and its result must have the same integer type.
module {
  func.func @invalid_add(%lhs: i32, %rhs: i64) -> i32 {
    %sum = "rhombus.add"(%lhs, %rhs) : (i32, i64) -> i32
    return %sum : i32
  }
}
