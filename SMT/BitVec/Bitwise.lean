module
prelude

public import SMT.BitVec.Basic

@[expose] public section

namespace SMT.BitVec

/-- SMT `bvnot`: each valid result bit is the complement of the input bit. -/
abbrev bvnot {n : Nat} (x : _root_.BitVec n) : _root_.BitVec n := ~~~x
/-- SMT `bvand`: each result bit is the conjunction of the two operand bits. -/
abbrev bvand {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x &&& y
/-- SMT `bvor`: each result bit is the disjunction of the two operand bits. -/
abbrev bvor {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x ||| y
/-- SMT `bvxor`: each result bit is the exclusive-or of the two operand bits. -/
abbrev bvxor {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x ^^^ y
/-- SMT `bvnand`: bitwise complement of `bvand x y`. -/
abbrev bvnand {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := ~~~(x &&& y)
/-- SMT `bvnor`: bitwise complement of `bvor x y`. -/
abbrev bvnor {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := ~~~(x ||| y)
/-- SMT `bvxnor`: bitwise complement of `bvxor x y`. -/
abbrev bvxnor {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := ~~~(x ^^^ y)
/-- SMT `bvcomp`: the width-one vector 1 when x = y, and 0 otherwise; not Bool. -/
abbrev bvcomp {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec 1 :=
  _root_.BitVec.ofBool (decide (x = y))

end SMT.BitVec
