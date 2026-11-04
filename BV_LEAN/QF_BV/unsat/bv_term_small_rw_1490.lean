/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1490.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1490 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvmul s (bvshl t s)) t) = (bvmul s (bvshl (bvshl t s) t)) := by
  intro n s t
  exact bvshl_bvmul s (bvshl t s) t

end BV.QF_BV.Unsat
