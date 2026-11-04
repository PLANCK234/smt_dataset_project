module
prelude

public import Init.Data.Bool
public import Init.Data.List.Pairwise

/-! SMT-LIB 2.7 Core semantics. Equality is lawful decidable equality, never arbitrary BEq. -/
@[expose] public section

namespace SMT.Core

/-- SMT `true`: the true Boolean value. -/
abbrev true_ : Bool := true
/-- SMT `false`: the false Boolean value. -/
abbrev false_ : Bool := false
/-- SMT `not p`: true exactly when `p` is false. -/
abbrev not (p : Bool) : Bool := !p
/-- SMT `and p q`: true exactly when both operands are true. -/
abbrev and (p q : Bool) : Bool := p && q
/-- SMT `or p q`: true exactly when at least one operand is true. -/
abbrev or (p q : Bool) : Bool := p || q
/-- SMT `xor p q`: true exactly when one operand is true and the other is false. -/
abbrev xor (p q : Bool) : Bool := Bool.xor p q
/-- SMT `=> p q`: false exactly when `p` is true and `q` is false. -/
abbrev implies (p q : Bool) : Bool := !p || q
/-- SMT homogeneous `= x y`: true exactly when the two values are equal. -/
abbrev eq {α : Type u} [DecidableEq α] (x y : α) : Bool := decide (x = y)
/-- SMT `ite p x y`: selects `x` when `p` is true, and `y` otherwise. -/
abbrev ite {α : Sort u} (p : Bool) (x y : α) : α := cond p x y
/-- The proposition that the Boolean SMT term `p` holds. -/
abbrev holds (p : Bool) : Prop := p = true

/-- Internal pairwise comparison helper; true iff `x` differs from every list member. -/
def differentFrom {α : Type u} [DecidableEq α] (x : α) : List α → Bool
  | [] => true
  | y :: ys => not (eq x y) && differentFrom x ys

/-- SMT `distinct`: true iff every pair of positions has unequal values.
The source requires at least two operands; this total helper also accepts shorter lists. -/
def distinct {α : Type u} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => differentFrom x xs && distinct xs

@[simp] theorem differentFrom_nil {α : Type u} [DecidableEq α] (x : α) :
    differentFrom x [] = true := rfl
@[simp] theorem differentFrom_cons {α : Type u} [DecidableEq α]
    (x y : α) (ys : List α) :
    differentFrom x (y :: ys) = (not (eq x y) && differentFrom x ys) := rfl
@[simp] theorem distinct_nil {α : Type u} [DecidableEq α] :
    distinct ([] : List α) = true := rfl
@[simp] theorem distinct_cons {α : Type u} [DecidableEq α]
    (x : α) (xs : List α) : distinct (x :: xs) = (differentFrom x xs && distinct xs) := rfl

/-- Core equality agrees with logical equality. -/
@[simp] theorem holds_eq {α : Type u} [DecidableEq α] (x y : α) :
    holds (eq x y) ↔ x = y := by simp [holds, eq]

theorem differentFrom_semantics {α : Type u} [DecidableEq α] (x : α) (xs : List α) :
    holds (differentFrom x xs) ↔ ∀ y ∈ xs, x ≠ y := by
  induction xs with
  | nil => simp [holds]
  | cons y ys ih => simp [holds, not, eq, ih]

/-- A universal, generic-sort contract for the pairwise semantics of SMT `distinct`. -/
theorem distinct_semantics {α : Type u} [DecidableEq α] (xs : List α) :
    holds (distinct xs) ↔ xs.Pairwise (fun x y => x ≠ y) := by
  induction xs with
  | nil => simp [holds]
  | cons x xs ih =>
    simp only [holds, distinct_cons, Bool.and_eq_true, List.pairwise_cons]
    exact and_congr (differentFrom_semantics x xs) ih

end SMT.Core
