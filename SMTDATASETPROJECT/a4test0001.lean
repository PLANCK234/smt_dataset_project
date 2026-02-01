import Mathlib.Data.Num.Bitwise
import reap

/-
SMT-LIB:

(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(assert (bvslt (_ bv100 32) a))
(check-sat)

Meaning (sat): ∃ a : BitVec 32, bvslt (100:32) a
-/

/-- Signed interpretation of an n-bit bitvector (two's complement). -/
def sbv_to_int {n : Nat} (x : BitVec n) : Int :=
  x.toInt

/-- Signed less-than (bvslt) on bitvectors. -/
def bvslt {n : Nat} (x y : BitVec n) : Prop :=
  sbv_to_int x < sbv_to_int y

/-- The SMT benchmark is satisfiable. -/
theorem a4test0001 : ∃ a : BitVec 32, bvslt (BitVec.ofNat 32 100) a := by
  -- choose a = 101
  use BitVec.ofNat 32 101
  simp only [bvslt]
  exact Int.compare_eq_lt.mp rfl
