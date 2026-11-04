/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_325.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvadd_bvshl_self (x y : BitVec n) :
    bvor x (bvadd x (bvshl y x)) = bvadd x (bvshl y x) := by
  rw [← bvor_bvshl_self, ← bvor_assoc, bvor_self]

theorem bv_term_small_rw_325 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvadd s (bvshl t s))) = (bvadd s (bvshl t s)) := by
  intro n s t
  simp only [bvor_bvadd_bvshl_self]

end BV.QF_BV.Unsat
