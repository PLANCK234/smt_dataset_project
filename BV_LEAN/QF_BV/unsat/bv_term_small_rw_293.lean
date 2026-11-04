/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_293.smt2
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
利用双重取负与左移交换，将 s << (-s) 改写成 -((-s) << (-s))。
令 b = (-s) << (-s)。b 为零时两边为 s；
b 非零时，已有自移位取负下界给出 (-b).toNat ≥ n，因此两边均为零。
-/

theorem bv_term_small_rw_293 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvshl s (bvneg s))) = (bvlshr s (bvshl s (bvneg s))) := by
  intro n s t
  have he : bvshl s (bvneg s) =
      bvneg (bvshl (bvneg s) (bvneg s)) := by
    rw [← bvshl_bvneg, bvneg_bvneg]
  rw [he]
  by_cases hb : bvshl (bvneg s) (bvneg s) = literal n 0
  · rw [hb]
    simp only [bvneg, literal, neg_zero,
      bvshl_zero, bvlshr_zero]
  · have h := width_le_toNat_bvneg_bvshl_self (bvneg s) hb
    rw [bvshl_large _ _ h, bvlshr_large _ _ h]

end BV.QF_BV.Unsat
