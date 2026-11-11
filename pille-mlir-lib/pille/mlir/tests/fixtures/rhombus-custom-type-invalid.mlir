// The word type's parameter must be i32 or i64, so f32 must fail verification.
module {
  func.func private @invalid_word(!rhombus.word<f32>)
}
