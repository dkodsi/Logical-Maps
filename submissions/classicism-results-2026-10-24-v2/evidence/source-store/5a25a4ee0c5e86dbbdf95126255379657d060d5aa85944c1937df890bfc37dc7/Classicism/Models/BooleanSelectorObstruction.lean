import Classicism.Models.BooleanIndexedProfiles

/-!
# The concrete supported higher-selector obstruction

Original formalization (misc), 23 October 2026, of section 8 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
Fresh-column amalgamation forces a supported entity to have zero equality
with every column outside its support. The literal predicate of outside
columns is admitted and nonempty, but every supported selecting operation
has value zero at its own outside predicate. The column family is explicitly
instantiated by the constructed profiles; the ground injection is the
remaining cardinal input. Translation to an object-language sentence is
downstream, not claimed by this algebraic theorem.
-/

namespace Classicism.Meta.ChoiceBoolean.SelectorObstruction

open ColumnConditions ColumnAlgebra

noncomputable section

open scoped Classical

variable {κ : Cardinal}

/-- Concrete data used by the obstruction, independently constructed by
the column-profile module below. -/
structure ColumnFamily (Y : ActionSpace (action κ)) where
  entry : κ.out → Y.space.Carrier
  equivariant : ∀ π i, Y.action.act π (entry i) = entry (π i)
  separated : ∀ i j, i ≠ j → Y.space.eqv (entry i) (entry j) = ⊥

def profileFamily (hκ : Cardinal.aleph0 ≤ κ)
    {X : ActionSpace (action κ)} {G : Type} (c : GroundChecks.GroundMap X G)
    (f : κ.out → G) (hf : Function.Injective f) :
    ColumnFamily (supportedPredicateSpace X) where
  entry := IndexedProfiles.supportedColumn hκ c f
  equivariant := IndexedProfiles.supportedColumn_action hκ c f
  separated := IndexedProfiles.columns_eqv_zero hκ c f hf

variable {Y : ActionSpace (action κ)} (C : ColumnFamily Y)

theorem finite_small (hκ : Cardinal.aleph0 ≤ κ) {S : Set κ.out} (hS : S.Finite) :
    Cardinal.mk S < κ := by
  letI : Finite S := hS.to_subtype
  exact (Cardinal.mk_lt_aleph0 (α := S)).trans_le hκ

theorem transposition_fixes {S : Set κ.out} {i j : κ.out}
    (hi : i ∉ S) (hj : j ∉ S) :
    PermutationAction.Fixes (transposition i j) S := by
  intro k hk
  change ChoiceFreshColumns.swap i j k = k
  apply ChoiceFreshColumns.swap_other
  · exact fun h => hi (h ▸ hk)
  · exact fun h => hj (h ▸ hk)

/-- No supported entity has positive equality with an outside column. -/
theorem equality_outside_zero (hκ : Cardinal.aleph0 ≤ κ)
    {S : Set κ.out} (hS : Cardinal.mk S < κ) {y : Y.space.Carrier}
    (hy : Y.action.Supports S y) (i : κ.out) (hi : i ∉ S) :
    Y.space.eqv y (C.entry i) = ⊥ := by
  by_contra hn
  obtain ⟨p, hp⟩ := ConditionCompletion.dense_cone (Condition κ) _ hn
  obtain ⟨j, hj, hji, q, hqp, hqt⟩ := fresh_amalgam_avoiding hκ p S hS i
  let π := transposition i j
  have hπ : PermutationAction.Fixes π S := transposition_fixes hi hj
  have hπi : π i = j := ChoiceFreshColumns.swap_left i j
  have hmove : (action κ).map π (Y.space.eqv y (C.entry i)) =
      Y.space.eqv y (C.entry j) := by
    rw [← Y.semilinear, hy π hπ, C.equivariant, hπi]
  have hq₁ := (ConditionCompletion.cone_mono (Condition κ) hqp).trans hp
  have hq₂ : ConditionCompletion.cone (Condition κ) q ≤ Y.space.eqv y (C.entry j) := by
    have h := ((action κ).map π).monotone hp
    rw [action_cone, hmove] at h
    exact (ConditionCompletion.cone_mono (Condition κ) hqt).trans h
  have hq₁' : ConditionCompletion.cone (Condition κ) q ≤ Y.space.eqv (C.entry i) y := by
    simpa only [Y.space.symm y (C.entry i)] using hq₁
  have hz := (le_inf hq₁' hq₂).trans (Y.space.trans (C.entry i) y (C.entry j))
  rw [C.separated i j (Ne.symm hji)] at hz
  exact ConditionCompletion.cone_ne_bot (Condition κ) q (bot_unique hz)

/-- The literal predicate of entries indexed outside S. -/
def outside (S : Set κ.out) : Predicate Y.space where
  toFun y := ⨆ i : κ.out, if i ∉ S then Y.space.eqv y (C.entry i) else ⊥
  coherent x y := by
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    by_cases hi : i ∉ S
    · simp only [if_pos hi]
      have ht : Y.space.eqv x y ⊓ Y.space.eqv x (C.entry i) ≤ Y.space.eqv y (C.entry i) := by
        rw [Y.space.symm x y]
        exact Y.space.trans y x (C.entry i)
      exact ht.trans (le_iSup_of_le i (by simp only [if_pos hi, le_refl]))
    · simp only [if_neg hi, inf_bot_eq, bot_le]

theorem fixes_mem_iff {S : Set κ.out} (π : Equiv.Perm κ.out)
    (hπ : PermutationAction.Fixes π S) (i : κ.out) : π i ∈ S ↔ i ∈ S := by
  constructor
  · intro h
    have he : π i = i := π.injective (hπ (π i) h)
    exact he ▸ h
  · intro h
    rw [hπ i h]
    exact h

theorem outside_supports (S : Set κ.out) : (predicateAction Y).Supports S (outside C S) := by
  intro π hπ
  change actPredicate Y π (outside C S) = outside C S
  apply Predicate.ext (X := Y.space)
  intro y
  change (action κ).map π (⨆ i : κ.out,
      if i ∉ S then Y.space.eqv (Y.action.act π⁻¹ y) (C.entry i) else ⊥) =
    ⨆ i : κ.out, if i ∉ S then Y.space.eqv y (C.entry i) else ⊥
  calc
    _ = ⨆ i : κ.out, (action κ).map π
        (if i ∉ S then Y.space.eqv (Y.action.act π⁻¹ y) (C.entry i) else ⊥) :=
      ((action κ).map π).map_iSup _
    _ = ⨆ i : κ.out, if π i ∉ S then Y.space.eqv y (C.entry (π i)) else ⊥ := by
      apply iSup_congr
      intro i
      by_cases hi : i ∉ S
      · have hπi : π i ∉ S := fun h => hi ((fixes_mem_iff π hπ i).mp h)
        simp only [if_pos hi, if_pos hπi]
        exact (Y.semilinear π (Y.action.act π⁻¹ y) (C.entry i)).symm.trans
          (congrArg₂ Y.space.eqv (Y.action.act_inv_act π y) (C.equivariant π i))
      · have hπi : ¬ π i ∉ S := by
          intro hn
          exact hi (fun h => hn ((fixes_mem_iff π hπ i).mpr h))
        simp only [if_neg hi, if_neg hπi]
        exact ((action κ).map π).map_bot
    _ = _ := π.iSup_comp
      (g := fun i : κ.out => if i ∉ S then Y.space.eqv y (C.entry i) else ⊥)

def supportedOutside (S : Set κ.out) (hS : S.Finite) : SupportedPredicate Y :=
  ⟨outside C S, S, hS, outside_supports C S⟩

theorem supportedOutside_supports (S : Set κ.out) (hS : S.Finite) :
    (supportedPredicateSpace Y).action.Supports S (supportedOutside C S hS) := by
  intro π hπ
  apply Subtype.ext
  exact outside_supports C S π hπ

theorem outside_nonempty (S : Set κ.out) (hS : Cardinal.mk S < κ) :
    (⨆ y : Y.space.Carrier, outside C S y) = ⊤ := by
  obtain ⟨i, hi⟩ := exists_outside S hS
  apply top_le_iff.mp
  apply le_iSup_of_le (C.entry i)
  apply le_iSup_of_le i
  rw [if_pos hi, Y.space.refl]

theorem outside_supported_zero (hκ : Cardinal.aleph0 ≤ κ)
    {S : Set κ.out} (hS : Cardinal.mk S < κ) {y : Y.space.Carrier}
    (hy : Y.action.Supports S y) : outside C S y = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro i
  by_cases hi : i ∉ S
  · simp only [if_pos hi, equality_outside_zero C hκ hS hy i hi, le_refl]
  · simp only [if_neg hi, le_refl]

section SelectingOperations

variable {X : ActionSpace (action κ)} (columns : ColumnFamily (supportedPredicateSpace X))

abbrev SelectorDomain :=
  SupportedPredicate (ActionSpace.product (supportedPredicateSpace (supportedPredicateSpace X)) X)

def selected (F : SelectorDomain (X := X)) (P : SupportedPredicate (supportedPredicateSpace X)) :
    SupportedPredicate X :=
  supportedSectionLeft (supportedPredicateSpace (supportedPredicateSpace X)) X F P
    (supportedPredicate_finitelySupported (supportedPredicateSpace X) P)

def selectorValue (F : SelectorDomain (X := X)) : Values κ :=
  ⨅ P : SupportedPredicate (supportedPredicateSpace X),
    (⨆ y : SupportedPredicate X,
      Predicate.toFun (X := (supportedPredicateSpace X).space) P.val y) ⇨
      Predicate.toFun (X := (supportedPredicateSpace X).space) P.val (selected F P)

include columns in
/-- Every actual admitted selecting operation has Boolean selector value zero. -/
theorem selectorValue_zero (hκ : Cardinal.aleph0 ≤ κ) (F : SelectorDomain (X := X)) :
    selectorValue F = ⊥ := by
  obtain ⟨S, hS, hF⟩ := F.property
  let P : SupportedPredicate (supportedPredicateSpace X) := supportedOutside columns S hS
  have hP : (supportedPredicateSpace (supportedPredicateSpace X)).action.Supports S P :=
    supportedOutside_supports columns S hS
  have hy : (supportedPredicateSpace X).action.Supports S (selected F P) := by
    intro π hπ
    apply Subtype.ext
    have hs := sectionLeft_supports
      (supportedPredicateSpace (supportedPredicateSpace X)) X hF hP
    exact hs π (by simpa only [Set.union_self] using hπ)
  have hz := outside_supported_zero columns hκ (finite_small hκ hS) hy
  have hn := outside_nonempty columns S (finite_small hκ hS)
  apply bot_unique
  apply (iInf_le _ P).trans
  change (⨆ y : SupportedPredicate X, outside columns S y) ⇨ outside columns S (selected F P) ≤ ⊥
  rw [hn, hz, top_himp]

include columns in
theorem selector_existence_value_zero (hκ : Cardinal.aleph0 ≤ κ) :
    (⨆ F : SelectorDomain (X := X), selectorValue F) = ⊥ := by
  simp only [selectorValue_zero columns hκ, iSup_bot]

end SelectingOperations

end

end Classicism.Meta.ChoiceBoolean.SelectorObstruction
