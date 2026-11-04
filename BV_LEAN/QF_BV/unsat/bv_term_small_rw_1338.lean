/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1338.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1338 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvand s t) (bvshl s t)) = (bvand s (bvlshr t (bvshl s t))) := by
  intro n s t
  rw [bvlshr_bvand]
  by_cases h : bvshl s t = literal n 0
  · simp only [h, bvlshr_zero]
  · rw [bvlshr_bvshl_self_eq_ite t s, ite_eq_right h]
    simp only [bvand_zero]

end BV.QF_BV.Unsat
