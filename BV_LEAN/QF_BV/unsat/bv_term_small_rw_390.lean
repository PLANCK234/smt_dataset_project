/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_390.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_390 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvmul t (bvnot (literal n 0)))) = (bvlshr s (bvneg t)) := by
  intro n s t
  simp only [bvmul_bvnot_zero]

end BV.QF_BV.Unsat
