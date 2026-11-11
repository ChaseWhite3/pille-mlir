module {
  func.func @annotate(%value: !rhombus.word<i32>) -> !rhombus.word<i32> {
    %result = "rhombus.annotate"(%value) {mode = #rhombus.mode<"checked">}
      : (!rhombus.word<i32>) -> !rhombus.word<i32>
    return %result : !rhombus.word<i32>
  }
}
