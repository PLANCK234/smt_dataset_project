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
数学分析：
左移与取负交换：(-t) << t = -(t << t)。
再令 b = t << t；b 为零时两边为 s，非零时移位量至少为 n，两边为零。
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
