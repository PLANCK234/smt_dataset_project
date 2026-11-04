module
prelude

public import SMT.BitVec.Basic

@[expose] public section

namespace SMT.BitVec

/-- SMT `bvudiv`: unsigned quotient floor(U(x)/U(y)); a zero divisor returns all ones.
Uses the SMT-specific Lean primitive, whose zero behavior differs from ordinary `/`. -/
abbrev bvudiv {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x.smtUDiv y
/-- SMT `bvurem`: unsigned remainder U(x) mod U(y); a zero divisor returns x. -/
abbrev bvurem {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x.umod y
/-- SMT `bvsdiv`: N_n(trunc(S(x)/S(y))) for nonzero y. At zero it returns
N_n(1) for a negative dividend, all ones otherwise. Signed minimum / -1 wraps. -/
abbrev bvsdiv {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x.smtSDiv y
/-- SMT `bvsrem`: truncating signed remainder S(x)-S(y)*trunc(S(x)/S(y)).
A zero divisor returns x. A nonzero remainder follows the dividend's sign. -/
abbrev bvsrem {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x.srem y
/-- SMT `bvsmod`: floor signed remainder S(x)-S(y)*floor(S(x)/S(y)).
A zero divisor returns x. A nonzero remainder follows the divisor's sign.
This semantics is centralized here; the Rust backend emits only this call. -/
abbrev bvsmod {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x.smod y

end SMT.BitVec
