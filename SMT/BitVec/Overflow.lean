module
prelude

public import SMT.BitVec.Basic

@[expose] public section

namespace SMT.BitVec

/-- SMT `bvnego`: true iff S(x)=-2^(n-1), for positive n. -/
abbrev bvnego {n : Nat} (x : _root_.BitVec n) : Bool := x.negOverflow
/-- SMT `bvuaddo`: true iff U(x)+U(y) ≥ 2^n. -/
abbrev bvuaddo {n : Nat} (x y : _root_.BitVec n) : Bool := x.uaddOverflow y
/-- SMT `bvsaddo`: true iff S(x)+S(y) lies outside [-2^(n-1), 2^(n-1)-1]. -/
abbrev bvsaddo {n : Nat} (x y : _root_.BitVec n) : Bool := x.saddOverflow y
/-- SMT `bvusubo`: true iff U(x) < U(y). -/
abbrev bvusubo {n : Nat} (x y : _root_.BitVec n) : Bool := x.usubOverflow y
/-- SMT `bvssubo`: true iff S(x)-S(y) lies outside [-2^(n-1), 2^(n-1)-1]. -/
abbrev bvssubo {n : Nat} (x y : _root_.BitVec n) : Bool := x.ssubOverflow y
/-- SMT `bvumulo`: true iff U(x)*U(y) ≥ 2^n. -/
abbrev bvumulo {n : Nat} (x y : _root_.BitVec n) : Bool := x.umulOverflow y
/-- SMT `bvsmulo`: true iff S(x)*S(y) lies outside [-2^(n-1), 2^(n-1)-1]. -/
abbrev bvsmulo {n : Nat} (x y : _root_.BitVec n) : Bool := x.smulOverflow y
/-- SMT `bvsdivo`: true iff S(x)=-2^(n-1) and S(y)=-1, for positive n.
A zero divisor does not count as overflow. -/
abbrev bvsdivo {n : Nat} (x y : _root_.BitVec n) : Bool := x.sdivOverflow y

end SMT.BitVec
