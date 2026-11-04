/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_323.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvadd_bvshl_self (x y : BitVec n) :
    bvand x (bvadd x (bvshl y x)) = x := by
  rw [← bvor_bvshl_self, bvand_bvor_absorb]

theorem bv_term_small_rw_323 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvadd s (bvshl t s))) = s := by
  intro n s t
  simp only [bvand_bvadd_bvshl_self]

end BV.QF_BV.Unsat
