module
prelude
public import Init.Data.Int.Bitwise.Lemmas
public import Init.Data.Int.Pow

public import SMT.BitVec.Model
public import SMT.BitVec.Shift
public import Init.Data.BitVec.Lemmas

/-! Shift semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

theorem bvshl_semantics (x y : _root_.BitVec n) :
    toUnsigned (bvshl x y) = (toUnsigned x * 2 ^ toUnsigned y) % 2 ^ n := by
  rw [bvshl_eq_shiftLeft]
  simp [_root_.BitVec.shiftLeft_eq', toUnsigned, Nat.shiftLeft_eq]
theorem bvlshr_semantics (x y : _root_.BitVec n) :
    toUnsigned (bvlshr x y) = toUnsigned x / 2 ^ toUnsigned y := by
  simp [bvlshr, toUnsigned, Nat.shiftRight_eq_div_pow]
theorem bvashr_semantics (x y : _root_.BitVec n) :
    toSigned (bvashr x y) = toSigned x / 2 ^ toUnsigned y := by
  simpa only [toSigned, toUnsigned, Int.shiftRight_eq_div_pow, Int.natCast_pow, Int.cast_ofNat_Int] using
    (_root_.BitVec.toInt_sshiftRight' (x := x) (y := y))

end SMT.BitVec
