/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_359.smt2
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
利用双重取负与左移交换，将 t << (-t) 改写成 -((-t) << (-t))。
令 b = (-t) << (-t)。b 为零时两边为 s；
b 非零时，已有自移位取负下界给出 (-b).toNat ≥ n，因此两边均为零。
-/

theorem bv_term_small_rw_359 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvshl t (bvneg t))) = (bvlshr s (bvshl t (bvneg t))) := by
  intro n s t
  have he : bvshl t (bvneg t) =
      bvneg (bvshl (bvneg t) (bvneg t)) := by
    rw [← bvshl_bvneg, bvneg_bvneg]
  rw [he]
  by_cases hb : bvshl (bvneg t) (bvneg t) = literal n 0
  · rw [hb]
    simp only [bvneg, literal, neg_zero,
      bvshl_zero, bvlshr_zero]
  · have h := width_le_toNat_bvneg_bvshl_self (bvneg t) hb
    rw [bvshl_large _ _ h, bvlshr_large _ _ h]

end BV.QF_BV.Unsat
