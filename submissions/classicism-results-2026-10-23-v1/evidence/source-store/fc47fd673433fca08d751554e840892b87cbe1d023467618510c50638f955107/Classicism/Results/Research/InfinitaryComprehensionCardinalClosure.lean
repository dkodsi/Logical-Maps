import Mathlib.ModelTheory.Skolem
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Elementary submodels closed under externally coded short sequences

This is ordinary first-order/set-theoretic metatheory. We use Mathlib's actual
Skolem expansion and an explicitly constructed regular-length tower. There is
no assumed closed elementary submodel or assumed preservation of its theory.

The operation family is external: an operation may have any arity of cardinal
less than kappa, and its output is an element of the ambient first-order
structure. For an H-theta application these operations must be supplied by
actual set codes of sequences. This file does not implement H-theta, the coding
of infinitary formulas, satisfaction absoluteness, or the typed Henkin reduct.

Source: research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md,
Theorem 5.2 (misc, 23 October 2026). The first-order Skolem theorem is Mathlib's
existing theorem, not a new result of this development.
-/

namespace Classicism.Research.InfinitaryComprehension.CardinalClosure

open Cardinal FirstOrder FirstOrder.Language Set

universe u

/-- Explicit external codes. No closure property of a submodel is a field. -/
structure CodeSystem (A : Type u) where
  Index : Type u
  Args : Index → Type u
  code : (i : Index) → (Args i → A) → A

namespace CodeSystem

variable {A : Type u} (D : CodeSystem A)

def outputs (X : Set A) : Set A :=
  ⋃ i, Set.range (fun f : D.Args i → X => D.code i (fun a => (f a).val))

def expand (X : Set A) : Set A := X ∪ D.outputs X

theorem subset_expand (X : Set A) : X ⊆ D.expand X := Set.subset_union_left

theorem code_mem_expand (X : Set A) (i : D.Index) (f : D.Args i → A)
    (hf : ∀ a, f a ∈ X) : D.code i f ∈ D.expand X := by
  apply Or.inr
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  exact ⟨fun a => ⟨f a, hf a⟩, rfl⟩

/-- A union of at most lambda sets of size at most lambda remains small. -/
theorem card_union_family_le {I : Type u} (lambdaCard : Cardinal.{u}) (hLambda : ℵ₀ ≤ lambdaCard)
    (hI : #I ≤ lambdaCard) (X : I → Set A) (hX : ∀ i, #(X i) ≤ lambdaCard) :
    #(⋃ i, X i) ≤ lambdaCard := by
  calc
    #(⋃ i, X i) ≤ #I * ⨆ i, #(X i) := Cardinal.mk_iUnion_le X
    _ ≤ lambdaCard * lambdaCard := mul_le_mul' hI (ciSup_le' hX)
    _ = lambdaCard := Cardinal.mul_eq_self hLambda

theorem card_expand_le (lambdaCard : Cardinal.{u}) (hLambda : ℵ₀ ≤ lambdaCard)
    (hI : #D.Index ≤ lambdaCard) (hpow : ∀ i, lambdaCard ^ #(D.Args i) ≤ lambdaCard)
    (X : Set A) (hX : #X ≤ lambdaCard) : #(D.expand X) ≤ lambdaCard := by
  have ho : #(D.outputs X) ≤ lambdaCard := by
    apply card_union_family_le lambdaCard hLambda hI
    intro i
    calc
      #(Set.range (fun f : D.Args i → X => D.code i (fun a => (f a).val)))
          ≤ #(D.Args i → X) := Cardinal.mk_range_le
      _ = #X ^ #(D.Args i) := by simp only [Cardinal.mk_arrow, Cardinal.lift_id]
      _ ≤ lambdaCard ^ #(D.Args i) := Cardinal.power_le_power_right hX
      _ ≤ lambdaCard := hpow i
  exact (Cardinal.mk_union_le X (D.outputs X)).trans
    ((add_le_add hX ho).trans_eq (Cardinal.add_eq_self hLambda))

end CodeSystem

/-- Regularity provides a strict common stage bound for every short family. -/
theorem short_family_bounded {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {I : Type u} (hI : #I < κ) (f : I → κ.ord.ToType) :
    ∃ j : κ.ord.ToType, ∀ i, f i < j := by
  let o : Ordinal.{u} := ⨆ i, (f i).toOrd.val + 1
  have ho : o < κ.ord := by
    apply Ordinal.iSup_add_one_lt_of_lt_cof
    · simpa only [hκ.cof_ord] using hI
    · exact fun i => (f i).toOrd.property
  refine ⟨Ordinal.ToType.mk ⟨o, ho⟩, ?_⟩
  intro i
  apply (Ordinal.ToType.mk.symm.lt_iff_lt).1
  simpa only [OrderIso.symm_apply_apply] using
    (show (f i).toOrd < (⟨o, ho⟩ : Set.Iio κ.ord) from
      Ordinal.lt_iSup_add_one (fun i => (f i).toOrd.val) i)

/-- Only data for constructing a tower; no target substructure is assumed. -/
structure ClosureData (L : FirstOrder.Language.{u, u}) (A : Type u)
    [L.Structure A] where
  κ : Cardinal.{u}
  lambdaCard : Cardinal.{u}
  regular : κ.IsRegular
  kappa_le : κ ≤ lambdaCard
  function_bound : #(Σ n, L.Functions n) ≤ lambdaCard
  seed : Set A
  seed_bound : #seed ≤ lambdaCard
  codes : CodeSystem A
  index_bound : #codes.Index ≤ lambdaCard
  arity_small : ∀ i, #(codes.Args i) < κ
  power_bound : lambdaCard ^< κ ≤ lambdaCard

namespace ClosureData

variable {L : FirstOrder.Language.{u, u}} {A : Type u} [L.Structure A]
variable (D : ClosureData L A)

abbrev Index := D.κ.ord.ToType
abbrev SmallStage := {N : L.Substructure A // #N ≤ D.lambdaCard}

theorem infinite_bound : ℵ₀ ≤ D.lambdaCard := D.regular.aleph0_le.trans D.kappa_le

theorem card_index : #D.Index ≤ D.lambdaCard := by
  simpa only [Index, Cardinal.mk_ord_toType] using D.kappa_le

theorem closure_bound (X : Set A) (hX : #X ≤ D.lambdaCard) :
    #(Substructure.closure L X) ≤ D.lambdaCard := by
  have h := Substructure.lift_card_closure_le (L := L) (s := X)
  simp only [Cardinal.lift_id] at h
  apply h.trans
  apply max_le D.infinite_bound
  exact (add_le_add hX D.function_bound).trans_eq
    (Cardinal.add_eq_self D.infinite_bound)

def previous (i : D.Index) (rec : ∀ j : D.Index, j < i → D.SmallStage) : Set A :=
  ⋃ j : Set.Iio i, ((rec j.val j.property).val : Set A)

theorem previous_bound (i : D.Index) (rec : ∀ j : D.Index, j < i → D.SmallStage) :
    #(D.previous i rec) ≤ D.lambdaCard := by
  apply CodeSystem.card_union_family_le D.lambdaCard D.infinite_bound
    ((Cardinal.mk_subtype_le _).trans D.card_index)
  exact fun j => (rec j.val j.property).property

noncomputable def step (i : D.Index)
    (rec : ∀ j : D.Index, j < i → D.SmallStage) : D.SmallStage :=
  ⟨Substructure.closure L (D.seed ∪ D.codes.expand (D.previous i rec)), by
    apply D.closure_bound
    apply (Cardinal.mk_union_le _ _).trans
    have he := D.codes.card_expand_le D.lambdaCard D.infinite_bound D.index_bound
      (fun i => (Cardinal.powerlt_le.1 D.power_bound) _ (D.arity_small i))
      (D.previous i rec) (D.previous_bound i rec)
    exact (add_le_add D.seed_bound he).trans_eq
      (Cardinal.add_eq_self D.infinite_bound)⟩

/-- At each stage take the Skolem closure after adjoining all short codes from
the union of earlier stages. The recursion is on a genuine well-order. -/
noncomputable def stage : D.Index → D.SmallStage := WellFoundedLT.fix D.step

theorem stage_eq (i : D.Index) :
    (D.stage i).val = Substructure.closure L
      (D.seed ∪ D.codes.expand (⋃ j : Set.Iio i, ((D.stage j.val).val : Set A))) := by
  rw [stage, WellFoundedLT.fix_eq]
  rfl

theorem seed_subset_stage (i : D.Index) : D.seed ⊆ (D.stage i).val := by
  rw [D.stage_eq]
  exact Set.subset_union_left.trans Substructure.subset_closure

theorem stage_lt {i j : D.Index} (h : i < j) : (D.stage i).val ≤ (D.stage j).val := by
  intro x hx
  rw [D.stage_eq j]
  apply Substructure.subset_closure
  apply Or.inr
  apply Or.inl
  exact Set.mem_iUnion.mpr ⟨⟨i, h⟩, hx⟩

theorem stage_mono : Monotone (fun i => (D.stage i).val) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with h | h
  · exact D.stage_lt h
  · subst j
    exact le_rfl

theorem stage_directed : Directed (· ≤ ·) (fun i => (D.stage i).val) := by
  intro i j
  exact ⟨max i j, D.stage_mono (le_max_left _ _), D.stage_mono (le_max_right _ _)⟩

noncomputable def union : L.Substructure A := ⨆ i, (D.stage i).val

theorem index_nonempty : Nonempty D.Index :=
  Ordinal.nonempty_toType_iff.2 D.regular.ord_pos.ne'

theorem mem_union {x : A} : x ∈ D.union ↔ ∃ i, x ∈ (D.stage i).val := by
  letI : Nonempty D.Index := D.index_nonempty
  exact Substructure.mem_iSup_of_directed D.stage_directed

theorem seed_subset_union : D.seed ⊆ D.union := by
  obtain ⟨i⟩ := D.index_nonempty
  intro x hx
  exact D.mem_union.2 ⟨i, D.seed_subset_stage i hx⟩

theorem union_bound : #D.union ≤ D.lambdaCard := by
  have hs : (D.union : Set A) = ⋃ i, ((D.stage i).val : Set A) := by
    ext x
    exact D.mem_union.trans Set.mem_iUnion.symm
  change #(D.union : Set A) ≤ D.lambdaCard
  rw [hs]
  exact CodeSystem.card_union_family_le D.lambdaCard D.infinite_bound D.card_index
    (fun i => ((D.stage i).val : Set A)) (fun i => (D.stage i).property)

/-- The only use of regularity beyond infinitude: every short tuple in the
final union is already in the union preceding one common stage. -/
theorem union_closed (i : D.codes.Index) (f : D.codes.Args i → A)
    (hf : ∀ a, f a ∈ D.union) : D.codes.code i f ∈ D.union := by
  classical
  have hi : ∀ a, ∃ j : D.Index, f a ∈ (D.stage j).val :=
    fun a => D.mem_union.1 (hf a)
  let locate : D.codes.Args i → D.Index := fun a => Classical.choose (hi a)
  obtain ⟨j, hj⟩ := short_family_bounded D.regular (D.arity_small i) locate
  apply D.mem_union.2
  refine ⟨j, ?_⟩
  rw [D.stage_eq j]
  apply Substructure.subset_closure
  apply Or.inr
  apply D.codes.code_mem_expand
  intro a
  exact Set.mem_iUnion.mpr ⟨⟨locate a, hj a⟩, Classical.choose_spec (hi a)⟩

end ClosureData

/-- An actual elementary-substructure existence theorem. The input cardinal
arithmetic and operation codes are explicit; no submodel is an input. Any
designated family of at most lambda parameters can be included in `s`. -/
theorem exists_closed_elementarySubstructure
    (L : FirstOrder.Language.{u, u}) (A : Type u) [L.Structure A]
    (κ lambdaCard : Cardinal.{u}) (hκ : κ.IsRegular) (hKappaLambda : κ ≤ lambdaCard)
    (hpow : lambdaCard ^< κ ≤ lambdaCard) (hL : L.card ≤ lambdaCard) (hA : lambdaCard ≤ #A)
    (D : CodeSystem A) (hI : #D.Index ≤ lambdaCard)
    (hArgs : ∀ i, #(D.Args i) < κ) (s : Set A) (hs : #s ≤ lambdaCard) :
    ∃ N : L.ElementarySubstructure A, s ⊆ N ∧ #N = lambdaCard ∧
      ∀ (i : D.Index) (f : D.Args i → A),
        (∀ a, f a ∈ N) → D.code i f ∈ N := by
  classical
  have hLambda : ℵ₀ ≤ lambdaCard := hκ.aleph0_le.trans hKappaLambda
  letI : Nonempty A := Cardinal.mk_ne_zero_iff.1
    (Cardinal.aleph0_pos.trans_le (hLambda.trans hA)).ne'
  obtain ⟨S, hsS, hS⟩ := L.exists_elementarySubstructure_card_eq s lambdaCard hLambda
    (by simpa only [Cardinal.lift_id] using hs)
    (by simpa only [Cardinal.lift_id] using hL)
    (by simpa only [Cardinal.lift_id] using hA)
  have hScard : #S = lambdaCard := by simpa only [Cardinal.lift_id] using hS
  let T : ClosureData (L.sum L.skolem₁) A :=
    { κ := κ
      lambdaCard := lambdaCard
      regular := hκ
      kappa_le := hKappaLambda
      function_bound :=
        (FirstOrder.Language.card_functions_sum_skolem₁_le (L := L)).trans
          (max_le hLambda hL)
      seed := (S : Set A)
      seed_bound := hScard.le
      codes := D
      index_bound := hI
      arity_small := hArgs
      power_bound := hpow }
  let N : L.ElementarySubstructure A := T.union.elementarySkolem₁Reduct
  have hSN : (S : Set A) ⊆ N := T.seed_subset_union
  refine ⟨N, hsS.trans hSN, ?_, ?_⟩
  · apply le_antisymm T.union_bound
    change lambdaCard ≤ #N
    rw [← hScard]
    exact Cardinal.mk_le_mk_of_subset hSN
  · exact T.union_closed

/-- Specialization to one explicit code operation for each ordinal length below
kappa. In a set universe this is the exact closure demand for short sequences,
once `code` is instantiated by the actual sequence-as-set operation. -/
theorem exists_short_sequence_closed_elementarySubstructure
    (L : FirstOrder.Language.{u, u}) (A : Type u) [L.Structure A]
    (κ lambdaCard : Cardinal.{u}) (hκ : κ.IsRegular) (hKappaLambda : κ ≤ lambdaCard)
    (hpow : lambdaCard ^< κ = lambdaCard) (hL : L.card ≤ lambdaCard) (hA : lambdaCard ≤ #A)
    (code : (i : κ.ord.ToType) → (i.toOrd.val.ToType → A) → A)
    (s : Set A) (hs : #s ≤ lambdaCard) :
    ∃ N : L.ElementarySubstructure A, s ⊆ N ∧ #N = lambdaCard ∧
      ∀ (i : κ.ord.ToType) (f : i.toOrd.val.ToType → A),
        (∀ a, f a ∈ N) → code i f ∈ N := by
  let D : CodeSystem A :=
    { Index := κ.ord.ToType
      Args := (fun i => i.toOrd.val.ToType)
      code := code }
  apply exists_closed_elementarySubstructure L A κ lambdaCard hκ hKappaLambda hpow.le hL hA D
    (by simpa only [D, Cardinal.mk_ord_toType] using hKappaLambda) ?_ s hs
  intro i
  change #i.toOrd.val.ToType < κ
  rw [Cardinal.mk_toType]
  exact Cardinal.lt_ord.1 i.toOrd.property

#print axioms short_family_bounded
#print axioms exists_closed_elementarySubstructure
#print axioms exists_short_sequence_closed_elementarySubstructure

end Classicism.Research.InfinitaryComprehension.CardinalClosure
