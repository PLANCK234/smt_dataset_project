module
prelude

public import SMT.BitVec.Basic

@[expose] public section

namespace SMT.BitVec

/-- SMT `ubv_to_int` (Ints-enabled profile): the nonnegative integer U(x). -/
abbrev ubv_to_int {n : Nat} (x : _root_.BitVec n) : Int := (x.toNat : Int)
/-- SMT `sbv_to_int` (Ints-enabled profile): the signed two's-complement integer S(x). -/
abbrev sbv_to_int {n : Nat} (x : _root_.BitVec n) : Int := x.toInt
/-- SMT `(_ int_to_bv n)` (Ints-enabled profile, n > 0): N_n(z), using
the nonnegative residue of z modulo 2^n, including when z is negative. -/
abbrev int_to_bv (n : Nat) (z : Int) : _root_.BitVec n := _root_.BitVec.ofInt n z

/-- PBV `(int_to_pbv n z)`: the n-bit representation of z modulo 2^n,
including negative z. Unlike indexed SMT syntax, n may be a symbolic width.
This typed interface represents valid positive source widths by Lean Nat;
it does not assign PBV semantics to nonpositive source widths. -/
abbrev int_to_pbv (n : Nat) (z : Int) : _root_.BitVec n := int_to_bv n z

end SMT.BitVec
