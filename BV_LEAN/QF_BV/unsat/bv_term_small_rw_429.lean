/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_429.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

theorem bv_term_small_rw_429 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvor t (bvand s t))) = (bvor s t) := by
  intro n s t
  (ext i h; simp [bvand, bvor, bvnot]; grind)

end BV.QF_BV.Unsat
