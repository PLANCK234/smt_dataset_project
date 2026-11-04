/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_751.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvor_bvlshr (x y : BitVec n) :
    bvlshr x (bvor y (bvlshr y x)) = bvlshr x y := by
  rcases Nat.le_total x.toNat y.toNat with h | h
  · rw [bvlshr_eq_zero_of_le x y h]
    exact bvlshr_eq_zero_of_le x _ (Nat.le_trans h SMT.Nat.left_le_or)
  · rw [bvlshr_eq_zero_of_le y x h, bvor_zero]

theorem bv_term_small_rw_751 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvor (bvlshr t s) t)) = (bvlshr s t) := by
  intro n s t
  simp only [bvor_comm, bvlshr_bvor_bvlshr]

end BV.QF_BV.Unsat
