module
prelude

public import SMT.BitVec.Basic

@[expose] public section

namespace SMT.BitVec

/-- SMT `bvult`: true iff U(x) < U(y). -/
abbrev bvult {n : Nat} (x y : _root_.BitVec n) : Bool := x.ult y
/-- SMT `bvule`: true iff U(x) ≤ U(y). -/
abbrev bvule {n : Nat} (x y : _root_.BitVec n) : Bool := x.ule y
/-- SMT `bvugt`: true iff U(x) > U(y). -/
abbrev bvugt {n : Nat} (x y : _root_.BitVec n) : Bool := y.ult x
/-- SMT `bvuge`: true iff U(x) ≥ U(y). -/
abbrev bvuge {n : Nat} (x y : _root_.BitVec n) : Bool := y.ule x
/-- SMT `bvslt`: true iff S(x) < S(y), interpreting the same sort as two's complement. -/
abbrev bvslt {n : Nat} (x y : _root_.BitVec n) : Bool := x.slt y
/-- SMT `bvsle`: true iff S(x) ≤ S(y). -/
abbrev bvsle {n : Nat} (x y : _root_.BitVec n) : Bool := x.sle y
/-- SMT `bvsgt`: true iff S(x) > S(y). -/
abbrev bvsgt {n : Nat} (x y : _root_.BitVec n) : Bool := y.slt x
/-- SMT `bvsge`: true iff S(x) ≥ S(y). -/
abbrev bvsge {n : Nat} (x y : _root_.BitVec n) : Bool := y.sle x

end SMT.BitVec
