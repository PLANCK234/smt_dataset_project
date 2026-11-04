/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_388.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_388 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul s (bvmul t (bvnot (literal n 0)))) = (bvneg (bvmul s t)) := by
  intro n s t
  rw [bvmul_bvnot_zero]
  exact bvmul_bvneg s t

end BV.QF_BV.Unsat
