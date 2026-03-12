import SmtQFBV.BV.logic

open SMT

section a49test0010

variable (x1 x2 : BitVec 32)

def assert1 (x1 : BitVec 32) : Prop :=
  ¬ (¬ ((bvand x1 (bvconst 16 32)) = (bvconst 0 32)))

def assert2 (x1 : BitVec 32) (x2 : BitVec 32)  : Prop :=
  ¬ (bvslt x1 (bvlshr x2 (bvconst 1 32)))

def assert3 (x1 : BitVec 32)  : Prop :=
  ¬ ((bvand x1 (bvconst 8 32)) = (bvconst 0 32))

def assert4 (x1 : BitVec 32)  : Prop :=
  ¬ (¬ ((bvand x1 (bvconst 4 32)) = (bvconst 0 32)))

def formula : Prop :=
  assert1 x1 ∧ assert2 x1 x2 ∧ assert3 x1 ∧ assert4 x1

theorem a49test0010.smt2 : ∃ (x1 x2 : BitVec 32), formula x1 x2 := by
  simp only [formula, assert1, assert2, assert3, assert4]
  simp only [bvand, bvconst, Decidable.not_not, bvslt, bvlshr, BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.one_mod, BitVec.toInt_ushiftRight, Nat.succ_ne_self,
    ↓reduceIte, Int.natCast_shiftRight, not_lt]
  use (bvconst 2147467114 32), (bvconst 0 32)
  simp only [bvconst, BitVec.reduceAnd, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
    Int.cast_ofNat_Int, Int.zero_shiftRight, BitVec.reduceToInt, Int.zero_le_ofNat, BitVec.reduceEq,
    not_false_eq_true, and_self]

end a49test0010
