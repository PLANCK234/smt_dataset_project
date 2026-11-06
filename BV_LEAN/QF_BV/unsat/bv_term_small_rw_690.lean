/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: BV/QF_BV/unsat/bv-term-small-rw_690.smt2
Original status: unknown; proved UNSAT.
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat
open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_690 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul s (bvlshr (bvnot (literal n 0)) t)) = (bvmul s (bvlshr (bvnot t) t)) := by
  intro n s t
  have h : bvlshr (bvnot t) t = bvlshr (bvnot (literal n 0)) t := by
    rw [← bvor_bvnot t, bvlshr_bvor, bvlshr_self]
    simp [bvor, literal]
  rw [h]

end BV.QF_BV.Unsat
