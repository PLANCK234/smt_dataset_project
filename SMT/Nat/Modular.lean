/-
Adapted from Lean v4.34.1, Init/Data/Nat/{Mod,Div/Lemmas,Bitwise/Lemmas}.lean.
Copyright (c) 2024 Lean FRO, LLC. Released under Apache 2.0;
see THIRD_PARTY_LICENSES/Apache-2.0.txt and UPSTREAM.md.
-/
module
prelude
public import Init.Data.Nat.Dvd

public import SMT.Nat.And

@[expose] public section

namespace SMT.Nat

/-- The unsigned residue at a fixed width (including width zero). -/
abbrev truncate (width value : Nat) : Nat := value % 2 ^ width
/-- The finite mask for bitvector complement. Nat has no unbounded bitwise NOT. -/
abbrev mask (width : Nat) : Nat := 2 ^ width - 1

theorem truncate_lt (n x : Nat) : truncate n x < 2 ^ n := Nat.mod_lt x (Nat.two_pow_pos n)
theorem truncate_of_lt (n x : Nat) (h : x < 2 ^ n) : truncate n x = x := Nat.mod_eq_of_lt h
theorem truncate_idem (n x : Nat) : truncate n (truncate n x) = truncate n x := Nat.mod_mod _ _
theorem truncate_add (n x y : Nat) :
    truncate n (x + y) = truncate n (truncate n x + truncate n y) := Nat.add_mod _ _ _
theorem truncate_mul (n x y : Nat) :
    truncate n (x * y) = truncate n (truncate n x * truncate n y) := Nat.mul_mod _ _ _
theorem and_mask (n x : Nat) : x &&& mask n = truncate n x := and_two_pow_sub_one_eq_mod x n
/-- Removing an inner modulus is valid only when the outer width is no larger. -/
theorem truncate_truncate (n m x : Nat) (h : n ≤ m) :
    truncate n (truncate m x) = truncate n x := by
  apply Nat.mod_mod_of_dvd
  exact Nat.pow_dvd_pow 2 h

theorem truncate_sub_of_le (n x y : Nat) (hx : x < 2 ^ n) (_hy : y ≤ x) :
    truncate n (x - y) = x - y := Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx)

end SMT.Nat
