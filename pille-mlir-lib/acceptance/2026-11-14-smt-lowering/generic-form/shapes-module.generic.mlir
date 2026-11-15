"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "successor"}> ({
  ^bb0(%arg4: i32 loc("<stdin>":2:24)):
    %6 = "arith.constant"() <{value = 1 : i32}> : () -> i32 loc("<stdin>":3:12)
    %7 = "arithmetic.add"(%arg4, %6) : (i32, i32) -> i32 loc("<stdin>":4:10)
    "func.return"(%7) : (i32) -> () loc("<stdin>":5:5)
  }) : () -> () loc("<stdin>":2:3)
  "func.func"() <{function_type = (i8, i1) -> i64, sym_name = "hidden", sym_visibility = "private"}> ({
  ^bb0(%arg2: i8 loc("<stdin>":7:29), %arg3: i1 loc("<stdin>":7:38)):
    %2 = "arith.constant"() <{value = true}> : () -> i1 loc("<stdin>":8:10)
    %3 = "arith.constant"() <{value = -1 : i8}> : () -> i8 loc("<stdin>":9:10)
    %4 = "arith.constant"() <{value = -1 : i64}> : () -> i64 loc("<stdin>":10:10)
    %5 = "arithmetic.add"(%4, %4) {rounding = "up"} : (i64, i64) -> i64 loc("<stdin>":11:10)
    "func.return"(%5) : (i64) -> () loc("<stdin>":12:5)
  }) {pille.note = "x"} : () -> () loc("<stdin>":7:3)
  "func.func"() <{function_type = (i32) -> i32, sym_name = "declared", sym_visibility = "private"}> ({
  }) : () -> () loc("<stdin>":14:3)
  "func.func"() <{function_type = (i32) -> i32, sym_name = "branch"}> ({
  ^bb0(%arg1: i32 loc("<stdin>":15:21)):
    "cf.br"()[^bb1] : () -> () loc("<stdin>":16:5)
  ^bb1:  // pred: ^bb0
    "func.return"(%arg1) : (i32) -> () loc("<stdin>":18:5)
  }) : () -> () loc("<stdin>":15:3)
  "func.func"() <{function_type = (i32) -> i32, sym_name = "effect"}> ({
  ^bb0(%arg0: i32 loc("<stdin>":20:21)):
    %0 = "memref.alloca"() <{operandSegmentSizes = array<i32: 0, 0>}> : () -> memref<i32> loc("<stdin>":21:13)
    "memref.store"(%arg0, %0) : (i32, memref<i32>) -> () loc("<stdin>":22:5)
    %1 = "memref.load"(%0) : (memref<i32>) -> i32 loc("<stdin>":23:10)
    "func.return"(%1) : (i32) -> () loc("<stdin>":24:5)
  }) : () -> () loc("<stdin>":20:3)
}) : () -> () loc("<stdin>":1:1)
