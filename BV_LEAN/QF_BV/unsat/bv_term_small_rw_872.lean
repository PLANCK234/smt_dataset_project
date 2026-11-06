/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: BV/QF_BV/unsat/bv-term-small-rw_872.smt2
Original status: unknown; proved UNSAT.
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat
open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_872 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul s (bvor (bvlshr t t) s)) = (bvmul s s) := by
  intro n s t
  rw [bvlshr_self]
  simp only [bvor, literal, _root_.BitVec.zero_or]
  

end BV.QF_BV.Unsat
