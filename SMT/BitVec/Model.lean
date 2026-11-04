module
prelude

public import Init.Data.BitVec.Basic

/-! Mathematical interpretation helpers, separate from SMT-facing compatibility operations.
SMT contracts assume positive widths; Lean's underlying BitVec also permits width zero.
-/
@[expose] public section

namespace SMT.BitVec

/-- Unsigned interpretation U(x), in the interval [0, 2^n). -/
abbrev toUnsigned {n : Nat} (x : _root_.BitVec n) : Nat := x.toNat
/-- Signed two's-complement interpretation S(x), in [-2^(n-1), 2^(n-1)) for n > 0. -/
abbrev toSigned {n : Nat} (x : _root_.BitVec n) : Int := x.toInt
/-- Modular construction N_n(z), whose unsigned value is z mod 2^n. -/
abbrev fromInt (n : Nat) (z : Int) : _root_.BitVec n := _root_.BitVec.ofInt n z
/-- Minimum signed value -2^(n-1), for positive width n. -/
abbrev signedMin (n : Nat) : Int := -(2 ^ (n - 1) : Int)
/-- Maximum signed value 2^(n-1)-1, for positive width n. -/
abbrev signedMax (n : Nat) : Int := (2 ^ (n - 1) : Int) - 1
/-- Maximum unsigned value 2^n-1. -/
abbrev unsignedMax (n : Nat) : Nat := 2 ^ n - 1

end SMT.BitVec
