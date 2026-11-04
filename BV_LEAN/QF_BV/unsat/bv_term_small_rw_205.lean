/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_205.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

theorem bv_term_small_rw_205 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvnot (bvor s (bvnot t))) = (bvand (bvnot s) t) := by
  intro n s t
  rw [bvnot_bvor, bvnot_bvnot]

end BV.QF_BV.Unsat
