import Std
import Mathlib.Data.Num.Bitwise
import Mathlib.Data.Bool.Basic

namespace SMT

/-
(concat (_ BitVec i) (_ BitVec j) (_ BitVec m))
  - concatenation of bitvectors of size i and j to get a new bitvector of
    size m, where m = i + j
-/
@[simp]
def concat {i j : Nat} (x : BitVec i) (y : BitVec j) : BitVec (i + j) := BitVec.append x y

/-
((_ extract i j) (_ BitVec m) (_ BitVec n))
  - extraction of bits i down to j from a bitvector of size m to yield a
    new bitvector of size n, where n = i - j + 1
-/
@[simp]
def extract {m : Nat} (i j : Nat) (x : BitVec m) : BitVec (i - j + 1) := BitVec.extractLsb i j x

@[simp]
def bvconst (x : Nat) (n : Nat) : BitVec n :=
  BitVec.ofNat n x

@[simp] def bvzero {m : Nat} : BitVec m := BitVec.ofNat m 0

@[simp]
def msb {m : Nat} (s : BitVec m) : BitVec 1 :=
  (extract (m - 1) (m - 1) s).cast (by simp only [Nat.sub_self, zero_add])

@[simp] def msb0 {m : Nat} (s : BitVec m) : Prop := msb (m := m) s = BitVec.ofNat 1 0
@[simp] def msb1 {m : Nat} (s : BitVec m) : Prop := msb (m := m) s = BitVec.ofNat 1 1

@[simp] def bvnot {m : Nat} (x : BitVec m) : BitVec m := ~~~x
@[simp] def bvand {m : Nat} (x y : BitVec m) : BitVec m := x &&& y
@[simp] def bvor  {m : Nat} (x y : BitVec m) : BitVec m := x ||| y
@[simp] def bvneg {m : Nat} (x : BitVec m) : BitVec m := -x
@[simp] def bvabs {m : Nat} (x : BitVec m) : BitVec m :=
  if msb x = (0 : BitVec 1) then x else bvneg x
@[simp] def bvadd {m : Nat} (x y : BitVec m) : BitVec m := x + y
@[simp] def bvmul {m : Nat} (x y : BitVec m) : BitVec m := x * y
@[simp] def bvudiv {m : Nat} (x y : BitVec m) : BitVec m := BitVec.smtUDiv x y
@[simp] def bvurem {m : Nat} (x y : BitVec m) : BitVec m := BitVec.umod x y
@[simp] def bvshl {m : Nat} (x y : BitVec m) : BitVec m := x <<< y
@[simp] def bvlshr {m : Nat} (x y : BitVec m) : BitVec m := x >>> y

@[simp] def bvult {m : Nat} (x y : BitVec m) : Prop := BitVec.ult x y
@[simp] def bvnego {m : Nat} (x : BitVec m) : Prop := x ≠ 0
@[simp]
def bvuaddo {m : Nat} (x y : BitVec m) : Prop := BitVec.uaddOverflow x y
@[simp] def bvsaddo {m : Nat} (x y : BitVec m) : Prop := BitVec.saddOverflow x y
@[simp] def bvumulo {m : Nat} (x y : BitVec m) : Prop := BitVec.umulOverflow x y
@[simp] def bvsmulo {m : Nat} (x y : BitVec m) : Prop := BitVec.smulOverflow x y

@[simp] def ubv_to_int {m : Nat} (x : BitVec m) : Int := x.toNat
@[simp] def sbv_to_int {m : Nat} (x : BitVec m) : Int := x.toInt
@[simp] def int_to_bv (m : Nat) (x : Int) : BitVec m := BitVec.ofInt m x
@[simp] def bvnand {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x &&& y)
@[simp] def bvnand' {m : Nat} (x y : BitVec m) : BitVec m := bvnot (bvand x y)
@[simp] def bvnor {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x ||| y)
@[simp] def bvnor' {m : Nat} (x y : BitVec m) : BitVec m := bvnot (bvor x y)

/-
bvxor [s1 s2 ... sn] = (bvxor' (bvxor' s1 s2) ... sn)
-/

@[simp]
def bvxor {m : Nat} : List (BitVec m) → BitVec m
| []      => 0
| x :: xs => xs.foldl (fun acc y => acc ^^^ y) x
@[simp] def bvxor' {m : Nat} (x y : BitVec m) : BitVec m := x ^^^ y
@[simp] def bvxor'' {m : Nat} (x y : BitVec m) : BitVec m := bvor (bvand x (bvnot y)) (bvand (bvnot x) y)
@[simp] def bvxnor {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x ^^^ y)
@[simp] def bvxnor' {m : Nat} (x y : BitVec m) : BitVec m := bvor (bvand x y) (bvand (bvnot x) (bvnot y))
@[simp] def bvcomp {m : Nat} (x y : BitVec m) : BitVec 1 := if x = y then BitVec.ofNat 1 1 else BitVec.ofNat 1 0

@[simp]
def bvcomp' : {m : Nat} → BitVec m → BitVec m → BitVec 1
  | 0, _, _ => 1
  | 1, s, t => bvxnor s t
  | m+2, s, t =>
      let hi_s : BitVec 1 := (extract (m+1) (m+1) s).cast (by simp only [Nat.sub_self, zero_add])
      let hi_t : BitVec 1 := (extract (m+1) (m+1) t).cast (by simp only [Nat.sub_self, zero_add])
      let lo_s : BitVec (m+1) := extract m 0 s
      let lo_t : BitVec (m+1) := extract m 0 t
      bvand (bvxnor hi_s hi_t) (bvcomp lo_s lo_t)

@[simp] def bvsub {m : Nat} (x y : BitVec m) : BitVec m := x - y
@[simp] def bvsub' {m : Nat} (x y : BitVec m) : BitVec m := bvadd x (bvneg y)
@[simp] def bvsdiv {m : Nat} (x y : BitVec m) : BitVec m := BitVec.sdiv x y

@[simp]
def bvsdiv' {m : Nat} (s t : BitVec m) : BitVec m :=
  let msb_s : BitVec 1 := msb s
  let msb_t : BitVec 1 := msb t
  if msb_s = (0 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvudiv s t
  else if msb_s = (1 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvneg (bvudiv (bvneg s) t)
  else if msb_s = (0 : BitVec 1) ∧ msb_t = (1 : BitVec 1) then
    bvneg (bvudiv s (bvneg t))
  else
    bvudiv (bvneg s) (bvneg t)

@[simp] def bvsrem {m : Nat} (x y : BitVec m) : BitVec m := BitVec.srem x y

@[simp]
def bvsrem' {m : Nat} (s t : BitVec m) : BitVec m :=
  let msb_s := msb s
  let msb_t := msb t
  if msb_s = (0 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvurem s t
  else if msb_s = (1 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvneg (bvurem (bvneg s) t)
  else if msb_s = (0 : BitVec 1) ∧ msb_t = (1 : BitVec 1) then
    bvurem s (bvneg t)
  else
    bvneg (bvurem (bvneg s) (bvneg t))

@[simp] def bvsmod {m : Nat} (x y : BitVec m) : BitVec m := BitVec.smod x y

@[simp]
def bvsmod' {m : Nat} (s t : BitVec m) : BitVec m :=
  let msb_s := msb s
  let msb_t := msb t
  let abs_s := bvabs s
  let abs_t := bvabs t
  let u := bvurem abs_s abs_t
  if u = (0 : BitVec m) then
    u
  else if msb_s = (0 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    u
  else if msb_s = (1 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvadd (bvneg u) t
  else if msb_s = (0 : BitVec 1) ∧ msb_t = (1 : BitVec 1) then
    bvadd u t
  else
    bvneg u

@[simp] def bvashr {m : Nat} (x y : BitVec m) : BitVec m := BitVec.sshiftRight x y.toNat
@[simp] def bvusubo {m : Nat} (x y : BitVec m) : Prop := x.toNat < y.toNat

@[simp]
def bvssubo {m : Nat} (x y : BitVec m) : Prop :=
  let sx := x.toInt
  let sy := y.toInt
  let r  := sx - sy
  let min : Int := -(2 : Int) ^ (m - 1)
  let max : Int := (2 : Int) ^ (m - 1) - 1
  r < min ∨ r > max

@[simp] def bvsdivo {m : Nat} (x y : BitVec m) : Prop :=
  x.toInt = -(2 : Int) ^ (m - 1) ∧ y.toInt = -1

@[simp]
def re_peat {m : Nat} (i : Nat) (hi : i ≥ 1) (x : BitVec m) : BitVec (i * m) :=
  match i with
  | 0 => False.elim (by exact Nat.not_succ_le_zero 0 hi)
  | 1 => by
      simpa
  | n + 2 =>
      cast
        (by rw [← Nat.add_one_mul])
        (concat (re_peat (n + 1) (by exact Nat.le_add_left 1 n) x) x)

@[simp] def zero_extend {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m + i) :=
  cast (by simp only [Nat.add_comm]) (concat (BitVec.ofNat i 0) x)

@[simp] def sign_extend {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m + i) :=
  .ofInt (m + i) x.toInt

@[simp]
def rotate_left {m : Nat} (i : Nat) (x : BitVec m) : BitVec m :=
  if h : m = 0 then
    cast (by simp only [h]) x
  else
    let k := i % m
    if hk : k = 0 then
      x
    else
      have : m - k - 1 + 1 + (m - 1 - (m - k) + 1) = m := by
          rw [Nat.sub_add_cancel, ←  Nat.add_assoc]
          have h1 :  m - k + (m - 1 - (m - k)) + 1 > 0 := by
            exact Nat.zero_lt_succ (m - k + (m - 1 - (m - k)))
          rw [Nat.sub_one_cancel h1 (Nat.zero_lt_of_ne_zero h)]
          rw [Nat.add_sub_cancel]
          have : m > m - k := by
            apply Nat.div_rec_fuel_lemma (Nat.zero_lt_of_ne_zero hk)
            apply (Nat.le_of_succ_le (Nat.mod_lt i (Nat.zero_lt_of_ne_zero h)))
            apply (Nat.lt_add_one m)
          have h2 : m - 1 ≥ m - k := by exact Nat.le_sub_one_of_lt this
          exact Nat.add_sub_of_le h2
          have h3 : i % m < m := by
            exact Nat.mod_lt i (Nat.pos_of_ne_zero h)
          exact Nat.le_sub_of_add_le' h3
      cast
        (by simp only [Nat.sub_zero]; rw [this])
        (concat
          (extract (m - k - 1) 0 x)
          (extract (m - 1) (m - k) x))

@[simp]
def rotate_right {m : Nat} (i : Nat) (x : BitVec m) : BitVec m :=
  if h : m = 0 then
    cast (by simp [h]) x
  else
    let k := i % m
    if hk : k = 0 then
      x
    else
      have : k - 1 + 1 + (m - 1 - k + 1) = m := by
          rw [Nat.sub_add_cancel, ←  Nat.add_assoc]
          have h1 :  k+ (m - 1 - k) + 1 > 0 := by
            exact Nat.zero_lt_succ (k + (m - 1 - k))
          rw [Nat.sub_one_cancel h1 (Nat.zero_lt_of_ne_zero h)]
          rw [Nat.add_sub_cancel]
          have : m > k := by exact Nat.lt_of_succ_le (Nat.mod_lt i (Nat.pos_of_ne_zero h))
          have h2 : m - 1 ≥ k := by exact Nat.le_sub_one_of_lt this
          exact Nat.add_sub_of_le h2
          exact Nat.one_le_iff_ne_zero.mpr hk
      cast
        (by simp only [Nat.sub_zero]; rw [this])
        (concat
          (extract (k - 1) 0 x)
          (extract (m - 1) k x))

@[simp] def bvule {m : Nat} (x y : BitVec m) : Prop := x.toNat ≤ y.toNat
@[simp] def bvugt {m : Nat} (x y : BitVec m) : Prop := x.toNat > y.toNat
@[simp] def bvuge {m : Nat} (x y : BitVec m) : Prop := x.toNat ≥ y.toNat

@[simp] def bvslt {m : Nat} (x y : BitVec m) : Prop := x.toInt < y.toInt
@[simp] def bvsle {m : Nat} (x y : BitVec m) : Prop := x.toInt ≤ y.toInt
@[simp] def bvsgt {m : Nat} (x y : BitVec m) : Prop := x.toInt > y.toInt
@[simp] def bvsge {m : Nat} (x y : BitVec m) : Prop := x.toInt ≥ y.toInt

@[simp] def bvule' {m : Nat} (x y : BitVec m) : Prop := (bvult x y) ∨ (x = y)
@[simp] def bvugt' {m : Nat} (x y : BitVec m) : Prop := bvult y x
@[simp] def bvuge' {m : Nat} (x y : BitVec m) : Prop := (bvult y x) ∨ (x = y)

/-
    For all terms s,t of sort (_ BitVec m), where 0 < m,

    (bvnand s t) abbreviates (bvnot (bvand s t))
    (bvnor s t) abbreviates (bvnot (bvor s t))
    (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
    (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
    (bvcomp s t) abbreviates (bvxnor s t) if m = 1, and
       (bvand (bvxnor ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
              (bvcomp ((_ extract |m-2| 0) s) ((_ extract |m-2| 0) t))) otherwise.

    Additionally, bvxor is left associative, so:

    (bvxor s_1 s_2 ... s_n) abbreviates (bvxor (bvxor s_1 s_2 ...) s_n), and
-/

theorem bvnand_eq_bvnand' {m : Nat} (s t : BitVec m) :
  bvnand s t = bvnand' s t := by simp only [bvnand, bvnand', bvnot, bvand]

theorem bvnor_eq_bvnor' {m : Nat} (s t : BitVec m) :
  bvnor s t = bvnor' s t := by simp only [bvnor, bvnor', bvnot, bvor]

theorem bvxor'_eq_bvxor'' {m : Nat} (s t : BitVec m) :
  bvxor' s t = bvxor'' s t := by
  unfold bvxor' bvxor''
  simp only [bvor, bvand, bvnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  cases hs : s.getLsbD i <;> cases ht : t.getLsbD i <;> simp [hs, ht]

theorem bvxnor_eq_bvxnor' {m : Nat} (s t : BitVec m) :
    bvxnor s t = bvxnor' s t := by
  unfold bvxnor bvxnor'
  simp only [bvor, bvand, bvnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  cases hs : s.getLsbD i <;> cases ht : t.getLsbD i <;> simp [hs, ht]

lemma bvcomp_eq_one_bit (s t : BitVec 1) :
    (if s = t then 1#1 else 0#1) = ~~~(s ^^^ t) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [Nat.lt_one_iff, BitVec.getLsbD_not, BitVec.getLsbD_xor]
  intro hi
  subst i
  simp only [Nat.lt_add_one, BitVec.getLsbD_eq_getElem, decide_true, Bool.true_and]
  cases s using BitVec.casesOn
  cases t using BitVec.casesOn
  bv_decide

lemma ite_and_to_bvand (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1#1 : BitVec 1) else 0#1) =
      (if P then 1#1 else 0#1) &&& (if Q then 1#1 else 0#1) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma eq_iff_hi_lo_eq {k : Nat} (s t : BitVec (k + 2)) :
    s = t ↔
      BitVec.extractLsb (k + 1) (k + 1) s =
        BitVec.extractLsb (k + 1) (k + 1) t
      ∧
      BitVec.extractLsb k 0 s =
        BitVec.extractLsb k 0 t := by
  simp only [Nat.sub_zero]
  constructor
  · intro h
    subst h
    simp only [and_self]
  intro h
  rcases h with ⟨hhi, hlo⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i = k + 1
  · subst hi
    simp only [Nat.lt_add_one, BitVec.getLsbD_eq_getElem, forall_const]
    have h0 := congrArg (fun x => x[0]) hhi
    simpa using h0
  intro hlt
  have hik : i < k + 1 := by
    exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hi
  have h := congrArg (fun x => x.getLsbD i) hlo
  simpa [(Nat.le_of_lt_succ hik)] using h

theorem bvcomp_eq_bvcomp' {m : Nat} (s t : BitVec m) :
    bvcomp s t = bvcomp' s t := by
  simp only [bvcomp, bvcomp', BitVec.ofNat_eq_ofNat, bvxnor, bvand, extract, BitVec.xor_cast,
    BitVec.not_cast]
  cases m with
    | zero =>
      simp only [ite_eq_left_iff, BitVec.zero_eq_one_iff, Nat.succ_ne_self, imp_false,
        Decidable.not_not]
      exact BitVec.eq_of_getMsbD_eq fun i ↦ congrFun rfl
    | succ m =>
      cases m with
      | zero =>
        simp only [Nat.reduceAdd]
        exact bvcomp_eq_one_bit s t
      | succ k =>
          by_cases h : s = t
          · subst h
            simp only [↓reduceIte, BitVec.xor_self, BitVec.not_zero]
            sorry
          simp [h]
          sorry


theorem bvxor_eq_bvxor' {m : Nat} (s t : BitVec m) :
  bvxor [s, t] = bvxor' s t := by simp only [bvxor, List.foldl_cons, List.foldl_nil, bvxor']

theorem bvsub_eq_bvsub' {m : Nat} (s t : BitVec m) :
   bvsub s t = bvsub' s t := by
  unfold bvsub bvsub'
  simp only [bvadd, bvneg]
  exact BitVec.sub_eq_add_neg s t

theorem bvsdiv_eq_bvsdiv' {m : Nat} (hm : 0 < m) (s t : BitVec m) :
    bvsdiv s t = bvsdiv' s t := by sorry

theorem bvsrem_eq_bvsrem' {m : Nat} (hm : 0 < m) (s t : BitVec m) :
    bvsrem s t = bvsrem' s t := by sorry

theorem bvsmod_eq_bvsmod' {m : Nat} (hm : 0 < m) (s t : BitVec m) :
    bvsmod s t = bvsmod' s t := by sorry

theorem bvule_eq_bvule' {m : Nat} (s t : BitVec m) :
    bvule s t ↔ bvule' s t := by
  unfold bvule bvule'
  simp only [bvult]
  unfold BitVec.ult
  constructor
  · intro h
    have hlt_or_eq : s.toNat < t.toNat ∨ s.toNat = t.toNat :=
      lt_or_eq_of_le h
    cases hlt_or_eq with
    | inl hlt =>
      left
      simpa using (decide_eq_true_eq.mpr hlt)
    | inr heq =>
      right
      apply BitVec.eq_of_toNat_eq
      simpa using heq
  intro h
  cases h with
  | inl hlt =>
    have hlt' : s.toNat < t.toNat :=
      decide_eq_true_eq.mp hlt
    exact Nat.le_of_lt hlt'
  | inr heq =>
    subst heq
    simp only [le_refl]

theorem bvugt_eq_bvugt' {m : Nat} (s t : BitVec m) :
    bvugt s t ↔ bvugt' s t := by
  unfold bvugt bvugt' bvult BitVec.ult
  exact Iff.symm decide_eq_true_iff

theorem bvuge_eq_bvuge' {m : Nat} (s t : BitVec m) :
    bvuge s t ↔ bvuge' s t := by
  unfold bvuge bvuge' bvult BitVec.ult
  simp only [ge_iff_le, decide_eq_true_eq]
  apply Iff.symm
  constructor
  · intro h
    apply Nat.le_iff_lt_or_eq.mpr
    cases h with
    | inl hlt =>
      left
      simpa using (decide_eq_true_eq.mpr hlt)
    | inr heq =>
      right
      exact BitVec.toNat_inj.mpr (id (Eq.symm heq))
  intro h
  apply Nat.le_iff_lt_or_eq.mp at h
  cases h with
  | inl hlt =>
    exact Or.intro_left (s = t) hlt
  | inr heq =>
    right
    apply BitVec.eq_of_toNat_eq
    exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (Eq.symm heq))) m)


end SMT
