/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_668.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Self

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

/-
数学分析：
令 b = (~t) << t。b 为零时左右移量均为零，结果为 s。
非零时，令 a = t.toNat。若 n ≤ 2^a，可整除性给出 b.toNat ≥ 2^a ≥ n。
若 2^a < n，则 (a+1)*2^a ≤ 2^(n-1)，且 b 的值是 2^n-(a+1)*2^a，
至少为半个数值范围，从而 ≥ n。因此非零分支左右移均为零。
-/

theorem bv_term_small_rw_668 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvshl (bvnot t) t)) = (bvlshr s (bvshl (bvnot t) t)) := by
  intro n s t
  by_cases hb : bvshl (bvnot t) t = literal n 0
  · rw [hb, bvshl_zero, bvlshr_zero]
  · have h := width_le_toNat_bvshl_bvnot_self t hb
    rw [bvshl_large _ _ h, bvlshr_large _ _ h]

end BV.QF_BV.Unsat
