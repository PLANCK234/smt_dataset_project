/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_269.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Self

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (neg_zero)

/-
数学分析：
令 b = t << t。若 b = 0，取负仍为零，两边均为 s。
若 b ≠ 0，第 234 条的下界引理给出 (-b).toNat ≥ n，左右移均为零。
-/

theorem bv_term_small_rw_269 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvneg (bvshl t t))) = (bvlshr s (bvneg (bvshl t t))) := by
  intro n s t
  by_cases hb : bvshl t t = literal n 0
  · rw [hb]
    simp only [bvneg, literal, neg_zero,
      bvshl_zero, bvlshr_zero]
  · have h := width_le_toNat_bvneg_bvshl_self t hb
    rw [bvshl_large _ _ h, bvlshr_large _ _ h]

end BV.QF_BV.Unsat
