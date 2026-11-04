/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_692.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvnot_self (x : BitVec n) :
    bvlshr (bvnot x) x = bvlshr (bvnot (literal n 0)) x := by
  rw [← bvor_bvnot x, bvlshr_bvor, bvlshr_self]
  simp [bvor, literal]

theorem bv_term_small_rw_692 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvlshr (bvnot (literal n 0)) t)) = (bvlshr s (bvlshr (bvnot t) t)) := by
  intro n s t
  simp only [bvlshr_bvnot_self]

end BV.QF_BV.Unsat
