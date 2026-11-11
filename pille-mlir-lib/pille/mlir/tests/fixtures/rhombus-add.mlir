module {
  func.func @add(%lhs: i32, %rhs: i32) -> i32 {
    %sum = "rhombus.add"(%lhs, %rhs) : (i32, i32) -> i32
    return %sum : i32
  }
}
