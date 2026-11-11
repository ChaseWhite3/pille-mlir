// Runtime dialect definition. Reusing %integer also requires equal operand and
// result types, beyond requiring each type to be either i32 or i64.
module {
  irdl.dialect @rhombus {
    irdl.type @word {
      %i32 = irdl.is i32
      %i64 = irdl.is i64
      %integer = irdl.any_of(%i32, %i64)
      irdl.parameters(element: %integer)
    }

    irdl.attribute @mode {
      %checked = irdl.is "checked"
      %wrapping = irdl.is "wrapping"
      %choice = irdl.any_of(%checked, %wrapping)
      irdl.parameters(value: %choice)
    }

    irdl.operation @add {
      %i32 = irdl.is i32
      %i64 = irdl.is i64
      %integer = irdl.any_of(%i32, %i64)
      irdl.operands(lhs: %integer, rhs: %integer)
      irdl.results(sum: %integer)
    }

    irdl.operation @annotate {
      %element = irdl.any
      %word = irdl.parametric @rhombus::@word<%element>
      %choice = irdl.any
      %mode = irdl.parametric @rhombus::@mode<%choice>
      irdl.operands(value: %word)
      irdl.results(result: %word)
      irdl.attributes {"mode" = %mode}
    }
  }
}
