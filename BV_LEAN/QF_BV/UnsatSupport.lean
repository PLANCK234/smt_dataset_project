/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Shared helper for QF_BV UNSAT proofs.
-/
import LEMMAS_learned.BitVec.Shift.Bounds

namespace BV.QF_BV.Unsat
open SMT.BitVec
open Learned.BitVec

/-- A nonzero left-shift count clears both x and its modular square.
The zero-count branch preserves both sides; no restriction on the width is needed. -/
theorem square_right_shift_by_left_shift (x y : BitVec n) :
    bvlshr (bvmul x x) (bvshl y x) = bvmul x (bvlshr x (bvshl y x)) := by
  by_cases hc : bvshl y x = literal n 0
  · rw [hc, bvlshr_zero, bvlshr_zero]
  · have hcount := lt_toNat_bvshl_of_ne_zero x y hc
    have hx : bvlshr x (bvshl y x) = literal n 0 :=
      bvlshr_eq_zero_of_le _ _ (Nat.le_of_lt hcount)
    have hsquare : bvlshr (bvmul x x) (bvshl y x) = literal n 0 := by
      apply toNat_injective
      rw [toNat_bvlshr, toNat_bvmul, toNat_literal, Nat.zero_mod]
      apply Nat.div_eq_of_lt
      calc
        x.toNat * x.toNat % 2 ^ n ≤ x.toNat * x.toNat := Nat.mod_le _ _
        _ < 2 ^ (x.toNat + 1) := Learned.Nat.sq_lt_two_pow_succ _
        _ ≤ 2 ^ (bvshl y x).toNat := Nat.pow_le_pow_right (by decide) hcount
    rw [hx, hsquare, bvmul_zero]

end BV.QF_BV.Unsat
