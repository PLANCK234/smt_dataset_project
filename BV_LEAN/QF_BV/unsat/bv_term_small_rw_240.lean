/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_240.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (not_eq_neg_add)

theorem bv_term_small_rw_240 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvnot (bvadd s t))) = (bvnot (bvadd (bvlshr s s) t)) := by
  intro n s t
  simp only [bvlshr_self, bvadd_comm, bvadd_zero] <;> simp only [bvadd, bvnot, not_eq_neg_add] <;> grind

end BV.QF_BV.Unsat
