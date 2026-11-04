/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_384.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_384 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvadd t (bvnot (literal n 0)))) = (bvlshr s (bvnot (bvneg t))) := by
  intro n s t
  simp only [bvadd_bvnot_zero]

end BV.QF_BV.Unsat
