module {
  irdl.dialect @closer_strengths {
    irdl.operation @leave {
      %c0 = irdl.is i8
      %c1 = irdl.is i8
      %c2 = irdl.is i8
      irdl.operands(before: %c0, state: %c1)
      irdl.results(out: %c2)
    }

    irdl.operation @is {
      %c0 = irdl.is i8
      %c1 = irdl.is i8
      %c2 = irdl.is i8
      irdl.operands(value: %c0, wanted: %c1)
      irdl.results(out: %c2)
    }

    irdl.operation @both {
      %c0 = irdl.is i8
      %c1 = irdl.is i8
      %c2 = irdl.is i8
      irdl.operands(a: %c0, b: %c1)
      irdl.results(out: %c2)
    }

    irdl.operation @either {
      %c0 = irdl.is i8
      %c1 = irdl.is i8
      %c2 = irdl.is i8
      irdl.operands(a: %c0, b: %c1)
      irdl.results(out: %c2)
    }

    irdl.operation @none {
      %c0 = irdl.is i8
      %c1 = irdl.is i8
      irdl.operands(a: %c0)
      irdl.results(out: %c1)
    }
  }
}
