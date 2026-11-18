/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_641.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Self

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (neg_zero)

/-
Proof sketch:
Left shift commutes with negation: (-t) << t = -(t << t).
Let b = t << t. If b = 0 both sides are s; otherwise the count is at least n and both sides are zero.
-/

theorem bv_term_small_rw_641 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvshl (bvneg t) t)) = (bvlshr s (bvneg (bvshl t t))) := by
  intro n s t
  rw [bvshl_bvneg]
  by_cases hb : bvshl t t = literal n 0
  · rw [hb]
    simp only [bvneg, literal, neg_zero,
      bvshl_zero, bvlshr_zero]
  · have h := width_le_toNat_bvneg_bvshl_self t hb
    rw [bvshl_large _ _ h, bvlshr_large _ _ h]

end BV.QF_BV.Unsat
