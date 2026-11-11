// A mode accepts only "checked" or "wrapping".
module {
  func.func @invalid_mode(%value: !rhombus.word<i32>) -> !rhombus.word<i32> {
    %result = "rhombus.annotate"(%value) {mode = #rhombus.mode<"unchecked">}
      : (!rhombus.word<i32>) -> !rhombus.word<i32>
    return %result : !rhombus.word<i32>
  }
}
