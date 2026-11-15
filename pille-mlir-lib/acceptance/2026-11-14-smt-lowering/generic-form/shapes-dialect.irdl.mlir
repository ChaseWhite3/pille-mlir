module {
  irdl.dialect @arithmetic {
    irdl.operation @add {
      %c0 = irdl.is i1
      %c1 = irdl.is i8
      %c2 = irdl.any_of(%c0, %c1)
      %c3 = irdl.is i16
      %c4 = irdl.any_of(%c2, %c3)
      %c5 = irdl.is i32
      %c6 = irdl.any_of(%c4, %c5)
      %c7 = irdl.is i64
      %c8 = irdl.any_of(%c6, %c7)
      irdl.operands(lhs: %c8, rhs: %c8)
      irdl.results(out: %c8)
    }

    irdl.operation @sub {
      %c0 = irdl.is i1
      %c1 = irdl.is i8
      %c2 = irdl.any_of(%c0, %c1)
      %c3 = irdl.is i16
      %c4 = irdl.any_of(%c2, %c3)
      %c5 = irdl.is i32
      %c6 = irdl.any_of(%c4, %c5)
      %c7 = irdl.is i64
      %c8 = irdl.any_of(%c6, %c7)
      irdl.operands(lhs: %c8, rhs: %c8)
      irdl.results(out: %c8)
    }

    irdl.operation @mul {
      %c0 = irdl.is i1
      %c1 = irdl.is i8
      %c2 = irdl.any_of(%c0, %c1)
      %c3 = irdl.is i16
      %c4 = irdl.any_of(%c2, %c3)
      %c5 = irdl.is i32
      %c6 = irdl.any_of(%c4, %c5)
      %c7 = irdl.is i64
      %c8 = irdl.any_of(%c6, %c7)
      irdl.operands(lhs: %c8, rhs: %c8)
      irdl.results(out: %c8)
    }

    irdl.operation @increment {
      %c0 = irdl.is i1
      %c1 = irdl.is i8
      %c2 = irdl.any_of(%c0, %c1)
      %c3 = irdl.is i16
      %c4 = irdl.any_of(%c2, %c3)
      %c5 = irdl.is i32
      %c6 = irdl.any_of(%c4, %c5)
      %c7 = irdl.is i64
      %c8 = irdl.any_of(%c6, %c7)
      irdl.operands(value: %c8)
      irdl.results(out: %c8)
    }

    irdl.operation @minus_one {
      %c0 = irdl.is i1
      %c1 = irdl.is i8
      %c2 = irdl.any_of(%c0, %c1)
      %c3 = irdl.is i16
      %c4 = irdl.any_of(%c2, %c3)
      %c5 = irdl.is i32
      %c6 = irdl.any_of(%c4, %c5)
      %c7 = irdl.is i64
      %c8 = irdl.any_of(%c6, %c7)
      irdl.operands()
      irdl.results(out: %c8)
    }

    irdl.operation @square_of_sum {
      %c0 = irdl.is i1
      %c1 = irdl.is i8
      %c2 = irdl.any_of(%c0, %c1)
      %c3 = irdl.is i16
      %c4 = irdl.any_of(%c2, %c3)
      %c5 = irdl.is i32
      %c6 = irdl.any_of(%c4, %c5)
      %c7 = irdl.is i64
      %c8 = irdl.any_of(%c6, %c7)
      irdl.operands(lhs: %c8, rhs: %c8)
      irdl.results(out: %c8)
    }

    irdl.operation @forty_two {
      %c0 = irdl.is i8
      irdl.operands()
      irdl.results(out: %c0)
    }

    irdl.operation @opaque {
      %c0 = irdl.is i1
      %c1 = irdl.is i8
      %c2 = irdl.any_of(%c0, %c1)
      %c3 = irdl.is i16
      %c4 = irdl.any_of(%c2, %c3)
      %c5 = irdl.is i32
      %c6 = irdl.any_of(%c4, %c5)
      %c7 = irdl.is i64
      %c8 = irdl.any_of(%c6, %c7)
      irdl.operands(value: %c8)
      irdl.results(out: %c8)
    }

    irdl.operation @loose {
      %c0 = irdl.is i32
      %c1 = irdl.is i64
      %c2 = irdl.any_of(%c0, %c1)
      %c3 = irdl.is i32
      %c4 = irdl.is i64
      %c5 = irdl.any_of(%c3, %c4)
      %c6 = irdl.is i32
      %c7 = irdl.is i64
      %c8 = irdl.any_of(%c6, %c7)
      irdl.operands(lhs: %c2, rhs: %c5)
      irdl.results(out: %c8)
    }

    irdl.operation @anything {
      %c0 = irdl.any
      %c1 = irdl.any
      %c2 = irdl.any
      irdl.operands(lhs: %c0, rhs: %c1)
      irdl.results(out: %c2)
    }
  }
}
