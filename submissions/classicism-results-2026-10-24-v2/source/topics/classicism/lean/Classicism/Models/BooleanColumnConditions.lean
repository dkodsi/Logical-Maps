import Classicism.Models.ChoiceFreshColumns
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Order.Hom.Basic

/-!
# Small partial bit assignments on cardinally many columns and rows

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md`, sections 2 and 8
(unpaginated). Conditions are actual partial functions on `κ.out × κ.out`
whose domain has cardinality less than κ. The order is stronger-below-weaker.
Binary unions and coordinate insertions need only that κ is infinite.

Column permutations act by actual order isomorphisms. Fresh columns and rows
are obtained from the domain bound, and the previously certified assignment
lemma supplies an explicit small common extension of a condition and a
fresh-column transposition. No compatibility verdict, forcing/model-existence
principle, or Choice failure is assumed. Less-than-κ chain closure, regularity
arguments, Boolean completion actions, and the typed model remain separate.
-/

namespace Classicism.Meta.ChoiceBoolean.ColumnConditions

universe u

open Cardinal

abbrev Point (κ : Cardinal.{u}) := κ.out × κ.out
abbrev Raw (κ : Cardinal.{u}) := ChoiceFreshColumns.Assignment κ.out κ.out Bool

def domain {κ : Cardinal.{u}} (p : Raw κ) : Set (Point κ) :=
  {a | ∃ b, p a = some b}

structure Condition (κ : Cardinal.{u}) where
  toFun : Raw κ
  small : Cardinal.mk (domain toFun) < κ

instance {κ : Cardinal.{u}} : CoeFun (Condition κ) (fun _ => Point κ → Option Bool) :=
  ⟨Condition.toFun⟩

@[ext] theorem Condition.ext {κ : Cardinal.{u}} {p q : Condition κ}
    (h : ∀ a, p a = q a) : p = q := by
  cases p with
  | mk p hp =>
    cases q with
    | mk q hq =>
      have e : p = q := funext h
      subst q
      rfl

instance {κ : Cardinal.{u}} : PartialOrder (Condition κ) where
  le p q := ChoiceFreshColumns.Extends p.toFun q.toFun
  le_refl p := fun _ _ h => h
  le_trans p q r hpq hqr := fun a b h => hpq a b (hqr a b h)
  le_antisymm p q hpq hqp := by
    apply Condition.ext
    intro a
    cases hp : p a with
    | none =>
      cases hq : q a with
      | none => rfl
      | some b =>
        have h := hpq a b hq
        rw [hp] at h
        cases h
    | some b => exact (hqp a b hp).symm

theorem le_iff {κ : Cardinal.{u}} (p q : Condition κ) :
    p ≤ q ↔ ∀ a b, q a = some b → p a = some b := Iff.rfl

def Compatible {κ : Cardinal.{u}} (p q : Condition κ) : Prop :=
  ChoiceFreshColumns.Compatible p.toFun q.toFun

theorem compatible_of_common_extension {κ : Cardinal.{u}} {p q r : Condition κ}
    (hrp : r ≤ p) (hrq : r ≤ q) : Compatible p q := by
  intro a b c hp hq
  exact Option.some.inj ((hrp a b hp).symm.trans (hrq a c hq))

theorem small_union {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {A : Type u}
    {s t : Set A} (hs : Cardinal.mk s < κ) (ht : Cardinal.mk t < κ) :
    Cardinal.mk (s ∪ t : Set A) < κ :=
  (Cardinal.mk_union_le s t).trans_lt (Cardinal.add_lt_of_lt hκ hs ht)

theorem small_insert {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {A : Type u}
    {s : Set A} (hs : Cardinal.mk s < κ) (a : A) :
    Cardinal.mk (insert a s : Set A) < κ :=
  Cardinal.mk_insert_le.trans_lt (Cardinal.add_one_lt_of_lt hκ hs)

def empty {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) : Condition κ where
  toFun _ := none
  small := by
    have hd : domain (fun _ : Point κ => (none : Option Bool)) = ∅ := by
      ext a
      simp [domain]
    rw [Cardinal.mk_set_eq_zero_iff.mpr hd]
    exact Cardinal.aleph0_pos.trans_le hκ

@[simp] theorem empty_apply {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (a : Point κ) :
    empty hκ a = none := rfl

theorem le_empty {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (p : Condition κ) :
    p ≤ empty hκ := by
  intro a b h
  cases h

theorem merge_domain {κ : Cardinal.{u}} (p q : Raw κ) :
    domain (ChoiceFreshColumns.merge p q) = domain p ∪ domain q := by
  ext a
  exact ChoiceFreshColumns.merge_domain p q a

/-- Left-biased union; compatibility is needed for extending the right side,
but its domain bound holds for arbitrary pairs of conditions. -/
def merge {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (p q : Condition κ) : Condition κ where
  toFun := ChoiceFreshColumns.merge p.toFun q.toFun
  small := by
    rw [merge_domain]
    exact small_union hκ p.small q.small

theorem merge_le_left {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (p q : Condition κ) :
    merge hκ p q ≤ p := ChoiceFreshColumns.merge_extends_left _ _

theorem merge_le_right {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (p q : Condition κ)
    (h : Compatible p q) : merge hκ p q ≤ q :=
  ChoiceFreshColumns.merge_extends_right _ _ h

theorem compatible_iff_common_extension {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (p q : Condition κ) : Compatible p q ↔ ∃ r : Condition κ, r ≤ p ∧ r ≤ q :=
  ⟨fun h => ⟨merge hκ p q, merge_le_left hκ p q, merge_le_right hκ p q h⟩,
    fun ⟨_, hp, hq⟩ => compatible_of_common_extension hp hq⟩

noncomputable def singleton {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (a : Point κ) (b : Bool) : Condition κ := by
  classical
  refine ⟨fun x => if x = a then some b else none, ?_⟩
  have hd : domain (fun x : Point κ => if x = a then some b else none) = {a} := by
    ext x
    by_cases h : x = a <;> simp [domain, h]
  rw [hd, Cardinal.mk_singleton]
  exact Cardinal.one_lt_aleph0.trans_le hκ

@[simp] theorem singleton_apply {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (a : Point κ) (b : Bool) : singleton hκ a b a = some b := by
  classical
  simp [singleton]

theorem singleton_compatible {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (p : Condition κ) (a : Point κ) (b : Bool) (ha : p a = none) :
    Compatible (singleton hκ a b) p := by
  classical
  intro x c d hx hp
  by_cases hxa : x = a
  · subst x
    rw [ha] at hp
    cases hp
  · simp [singleton, hxa] at hx

/-- Assign the specified coordinate, preserving the old condition when that
coordinate was unused. -/
noncomputable def put {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (p : Condition κ) (a : Point κ) (b : Bool) : Condition κ :=
  merge hκ (singleton hκ a b) p

@[simp] theorem put_apply {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (p : Condition κ) (a : Point κ) (b : Bool) : put hκ p a b a = some b :=
  merge_le_left hκ (singleton hκ a b) p a b (singleton_apply hκ a b)

theorem put_le {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (p : Condition κ) (a : Point κ) (b : Bool) (ha : p a = none) :
    put hκ p a b ≤ p :=
  merge_le_right hκ _ _ (singleton_compatible hκ p a b ha)

def columnMap {κ : Cardinal.{u}} (σ : Equiv.Perm κ.out) (a : Point κ) : Point κ :=
  (σ a.1, a.2)

theorem columnMap_injective {κ : Cardinal.{u}} (σ : Equiv.Perm κ.out) :
    Function.Injective (columnMap σ) := by
  intro a b h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change σ a.1 = σ b.1 at h₁
  change a.2 = b.2 at h₂
  exact Prod.ext (σ.injective h₁) h₂

/-- A column c moves to σ(c); the assignment is pulled back along σ⁻¹. -/
def permute {κ : Cardinal.{u}} (σ : Equiv.Perm κ.out) (p : Condition κ) : Condition κ where
  toFun a := p (columnMap σ.symm a)
  small := by
    let f : domain (fun a => p (columnMap σ.symm a)) → domain p.toFun :=
      fun a => ⟨columnMap σ.symm a.val, a.property⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact columnMap_injective σ.symm (congrArg Subtype.val h)
    exact (Cardinal.mk_le_of_injective hf).trans_lt p.small

@[simp] theorem permute_apply {κ : Cardinal.{u}} (σ : Equiv.Perm κ.out)
    (p : Condition κ) (c r : κ.out) :
    permute σ p (c, r) = p (σ.symm c, r) := rfl

theorem permute_inverse {κ : Cardinal.{u}} (σ : Equiv.Perm κ.out) (p : Condition κ) :
    permute σ.symm (permute σ p) = p := by
  apply Condition.ext
  rintro ⟨c, r⟩
  simp only [permute_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem permute_le_iff {κ : Cardinal.{u}} (σ : Equiv.Perm κ.out)
    (p q : Condition κ) : permute σ p ≤ permute σ q ↔ p ≤ q := by
  constructor
  · intro h a b hq
    have hq' : permute σ q (σ a.1, a.2) = some b := by
      simpa only [permute_apply, Equiv.symm_apply_apply] using hq
    have hp := h (σ a.1, a.2) b hq'
    simpa only [permute_apply, Equiv.symm_apply_apply] using hp
  · intro h a b hq
    exact h (columnMap σ.symm a) b hq

def permutationOrderIso {κ : Cardinal.{u}} (σ : Equiv.Perm κ.out) :
    Condition κ ≃o Condition κ where
  toFun := permute σ
  invFun := permute σ.symm
  left_inv := permute_inverse σ
  right_inv p := by simpa only [Equiv.symm_symm] using permute_inverse σ.symm p
  map_rel_iff' := permute_le_iff σ _ _

noncomputable def transposition {κ : Cardinal.{u}} (i j : κ.out) : Equiv.Perm κ.out := by
  classical
  exact
    { toFun := ChoiceFreshColumns.swap i j
      invFun := ChoiceFreshColumns.swap i j
      left_inv := ChoiceFreshColumns.swap_involutive i j
      right_inv := ChoiceFreshColumns.swap_involutive i j }

noncomputable def transpose {κ : Cardinal.{u}} (i j : κ.out) (p : Condition κ) :
    Condition κ := permute (transposition i j) p

theorem transpose_apply {κ : Cardinal.{u}} (i j : κ.out) (p : Condition κ) (a : Point κ) :
    transpose i j p a = @ChoiceFreshColumns.transpose κ.out κ.out Bool
      (Classical.decEq κ.out) i j p.toFun a := by
  classical
  rfl

theorem fresh_compatible {κ : Cardinal.{u}} (p : Condition κ) (i j : κ.out)
    (hj : ∀ r, p (j, r) = none) : Compatible p (transpose i j p) := by
  classical
  exact ChoiceFreshColumns.fresh_compatible p.toFun i j hj

theorem fresh_amalgam {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (p : Condition κ)
    (i j : κ.out) (hj : ∀ r, p (j, r) = none) :
    ∃ q : Condition κ, q ≤ p ∧ q ≤ transpose i j p :=
  (compatible_iff_common_extension hκ p (transpose i j p)).mp
    (fresh_compatible p i j hj)

def usedColumns {κ : Cardinal.{u}} (p : Condition κ) : Set κ.out :=
  Prod.fst '' domain p.toFun

def usedRows {κ : Cardinal.{u}} (p : Condition κ) : Set κ.out :=
  Prod.snd '' domain p.toFun

theorem usedColumns_small {κ : Cardinal.{u}} (p : Condition κ) :
    Cardinal.mk (usedColumns p) < κ := Cardinal.mk_image_le.trans_lt p.small

theorem usedRows_small {κ : Cardinal.{u}} (p : Condition κ) :
    Cardinal.mk (usedRows p) < κ := Cardinal.mk_image_le.trans_lt p.small

theorem exists_outside {κ : Cardinal.{u}} (s : Set κ.out) (hs : Cardinal.mk s < κ) :
    ∃ c, c ∉ s := by
  classical
  by_contra hn
  have hall : ∀ c, c ∈ s := by
    intro c
    by_contra hc
    exact hn ⟨c, hc⟩
  have he : s = Set.univ := Set.eq_univ_iff_forall.mpr hall
  have hbad : κ < κ := by simpa only [he, Cardinal.mk_univ, Cardinal.mk_out] using hs
  exact (lt_irrefl κ) hbad

theorem column_unused {κ : Cardinal.{u}} (p : Condition κ) (c : κ.out)
    (hc : c ∉ usedColumns p) : ∀ r, p (c, r) = none := by
  intro r
  cases h : p (c, r) with
  | none => rfl
  | some b => exact False.elim (hc ⟨(c, r), ⟨b, h⟩, rfl⟩)

theorem row_unused {κ : Cardinal.{u}} (p : Condition κ) (r : κ.out)
    (hr : r ∉ usedRows p) : ∀ c, p (c, r) = none := by
  intro c
  cases h : p (c, r) with
  | none => rfl
  | some b => exact False.elim (hr ⟨(c, r), ⟨b, h⟩, rfl⟩)

theorem exists_fresh_column {κ : Cardinal.{u}} (p : Condition κ) :
    ∃ c, ∀ r, p (c, r) = none := by
  obtain ⟨c, hc⟩ := exists_outside (usedColumns p) (usedColumns_small p)
  exact ⟨c, column_unused p c hc⟩

theorem exists_fresh_row {κ : Cardinal.{u}} (p : Condition κ) :
    ∃ r, ∀ c, p (c, r) = none := by
  obtain ⟨r, hr⟩ := exists_outside (usedRows p) (usedRows_small p)
  exact ⟨r, row_unused p r hr⟩

/-- A column fresh for the condition and outside a separately specified
small support, while also different from the column to be transposed. -/
theorem exists_fresh_column_avoiding {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (p : Condition κ) (s : Set κ.out) (hs : Cardinal.mk s < κ) (i : κ.out) :
    ∃ j, j ∉ s ∧ j ≠ i ∧ ∀ r, p (j, r) = none := by
  obtain ⟨j, hj⟩ := exists_outside (insert i (s ∪ usedColumns p))
    (small_insert hκ (small_union hκ hs (usedColumns_small p)) i)
  have hji : j ≠ i := fun h => hj (Set.mem_insert_iff.mpr (Or.inl h))
  have hjs : j ∉ s := fun h => hj (Set.mem_insert_iff.mpr (Or.inr (Or.inl h)))
  have hjp : j ∉ usedColumns p :=
    fun h => hj (Set.mem_insert_iff.mpr (Or.inr (Or.inr h)))
  exact ⟨j, hjs, hji, column_unused p j hjp⟩

theorem fresh_amalgam_avoiding {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (p : Condition κ) (s : Set κ.out) (hs : Cardinal.mk s < κ) (i : κ.out) :
    ∃ j, j ∉ s ∧ j ≠ i ∧ ∃ q : Condition κ, q ≤ p ∧ q ≤ transpose i j p := by
  obtain ⟨j, hjs, hji, hj⟩ := exists_fresh_column_avoiding hκ p s hs i
  exact ⟨j, hjs, hji, fresh_amalgam hκ p i j hj⟩

end Classicism.Meta.ChoiceBoolean.ColumnConditions
