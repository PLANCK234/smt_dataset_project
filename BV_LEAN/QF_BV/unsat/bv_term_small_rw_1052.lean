/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1052.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1052 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd t (bvnot (bvor s t))) = (bvor (bvnot s) t) := by
  intro n s t
  simp only [bvnot_bvor, bvadd_bvand_bvnot, bvor_comm]

end BV.QF_BV.Unsat
