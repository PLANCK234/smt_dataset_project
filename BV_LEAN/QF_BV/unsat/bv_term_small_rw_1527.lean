/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1527.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvnot_self (x : BitVec n) :
    bvlshr (bvnot x) x = bvlshr (bvnot (literal n 0)) x := by
  rw [← bvor_bvnot x, bvlshr_bvor, bvlshr_self]
  simp [bvor, literal]

theorem bv_term_small_rw_1527 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr (bvnot t) s) t) = (bvlshr (bvlshr (bvnot s) s) t) := by
  intro n s t
  rw [bvlshr_bvlshr_comm (bvnot t) s t,
    bvlshr_bvnot_self, bvlshr_bvnot_self,
    bvlshr_bvlshr_comm]

end BV.QF_BV.Unsat
