/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1529.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

theorem bv_term_small_rw_1529 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvadd (bvnot t) t) t) = (bvshl (bvnot (bvlshr s s)) t) := by
  intro n s t
  first
  | (simp [bvadd_comm, bvmul_comm, bvand_comm, bvor_comm]; done)
  | (simp [bvadd, bvmul, bvneg, bvnot, bvand, bvor, bvlshr, bvshl_eq_shiftLeft, literal, bvadd_comm, bvmul_comm, bvand_comm, bvor_comm]; done)

end BV.QF_BV.Unsat
