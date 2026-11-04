/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_308.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvlshr_bvshl_self (x y : BitVec n) :
    bvor x (bvlshr x (bvshl y x)) = x := by
  rw [bvlshr_bvshl_self_eq_ite]
  split <;> simp only [bvor_self, bvor_zero]

theorem bv_term_small_rw_308 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvlshr s (bvshl s s))) = s := by
  intro n s t
  simp only [bvor_bvlshr_bvshl_self]

end BV.QF_BV.Unsat
