import Classicism.Results.Research.InfinitaryComprehensionNominalOccurrences
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.GroupTheory.Perm.Basic

/-!
# An explicit countermodel for every regular infinite parameter bound

For a regular infinite κ, the atoms are κ × Bool with the full permutation
group. Individual atoms have their actual permutation action. At every arrow
type the domain contains all functions with support of cardinality below κ.
Truth values have trivial action, so arbitrary set-sized connectives are
interpreted without adding any higher-type object. A family of fewer than κ
occurring parameters has a common small support, proving every corresponding
actual infinitary Comprehension instance even over a huge ambient parameter
family. The disjunction naming the true-coloured
atoms has no admitted predicate, refuting unrestricted Comprehension in the
same expanded language. No elementary-submodel existence is assumed.

Direct source: research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md, nominal fixed-bound strictness proof, misc,
23 October 2026, unpaginated. Source-only; not yet kernel checked.
-/

namespace Classicism.Research.InfinitaryComprehension.Nominal

open Classicism.Meta
open Classicism.Meta.Nominal
open Cardinal

noncomputable section

namespace RegularBound

variable (κ : Cardinal.{0})

abbrev Atom := κ.ord.ToType × Bool

def atoms : Action (Equiv.Perm (Atom κ)) where
  Carrier := Atom κ
  act g a := g a
  one_act _ := rfl
  mul_act _ _ _ := rfl

/-- The support ideal is literally the sets of cardinality below κ. -/
def ideal (hκ : κ.IsRegular) : SupportIdeal (atoms κ) where
  Small S := #S < κ
  empty := by simpa only [mk_emptyCollection] using hκ.pos
  subset h hT := (mk_le_mk_of_subset h).trans_lt hT
  union hS hT := (mk_union_le _ _).trans_lt (add_lt_of_lt hκ.aleph0_le hS hT)
  image _ {S} hS := mk_image_le.trans_lt hS

def individuals (hκ : κ.IsRegular) : Nom (atoms κ) (ideal κ hκ) where
  obj := atoms κ
  supported a := ⟨{a}, by
    exact lt_of_eq_of_lt (Cardinal.mk_singleton (α := (atoms κ).Carrier) a)
      (hκ.nat_lt 1),
    fun g hg => hg a (Set.mem_singleton a)⟩

def model (hκ : κ.IsRegular) : Henkin.Model :=
  Hierarchy.model (individuals κ hκ)

theorem individual_nonempty (hκ : κ.IsRegular) : Nonempty ((model κ hκ).Dom Ty.e) := by
  have hi : Nonempty κ.ord.ToType := Ordinal.nonempty_toType_iff.2 (ne_of_gt hκ.ord_pos)
  obtain ⟨i⟩ := hi
  exact ⟨(i, false)⟩

/-- Counts typed parameters, rather than the branching nodes of a formula. -/
def ParameterBound (Param : Ty → Type) : Prop := #(Σ σ, Param σ) < κ

/-- The cardinality restriction does not restrict infinitary branching. -/
def BoundedComp (M : Henkin.Model.{0}) (w : M.World) : Prop :=
  ∀ (Param : Ty → Type), ParameterBound κ Param →
    ∀ (η : Henkin.Assignment M Param) (Γ : Ctx) (a : Formula Param Γ),
      M.truth (Henkin.eval M η a.comprehension Henkin.Env.nil) w

/-- The sharp bound counts only distinct typed parameter symbols occurring
in the particular matrix. Unused ambient parameters are unrestricted. -/
def OccurrenceBoundedComp (M : Henkin.Model.{0}) (w : M.World) : Prop :=
  ∀ (Param : Ty → Type) (η : Henkin.Assignment M Param) (Γ : Ctx)
    (a : Formula Param Γ), #(occurring a) < κ →
      M.truth (Henkin.eval M η a.comprehension Henkin.Env.nil) w

/-- Regularity is used only to combine the supports of the named parameters. -/
theorem assignment_supported (hκ : κ.IsRegular) {Param : Ty → Type}
    (hParam : ParameterBound κ Param)
    (η : Henkin.Assignment (model κ hκ) Param) :
    Supported (atoms κ)
      (Hierarchy.assignmentAction (individuals κ hκ) Param) (ideal κ hκ) η := by
  let X (p : Σ σ, Param σ) := Hierarchy.dom (individuals κ hκ) p.1
  let value (p : Σ σ, Param σ) : X p := η p.2
  let support (p : Σ σ, Param σ) : Set (Atom κ) :=
    Classical.choose ((X p).supported (value p))
  have hs (p : Σ σ, Param σ) : #(support p) < κ ∧
      Supports (atoms κ) (X p).obj (support p) (value p) :=
    Classical.choose_spec ((X p).supported (value p))
  refine ⟨⋃ p, support p, ?_, ?_⟩
  · exact (card_iUnion_lt_iff_forall_of_isRegular hκ hParam).2 (fun p => (hs p).1)
  · intro g hg
    funext σ p
    exact (hs ⟨σ, p⟩).2 g (fun a ha => hg a (Set.mem_iUnion.mpr ⟨⟨σ, p⟩, ha⟩))

theorem bounded_comprehension (hκ : κ.IsRegular) :
    BoundedComp κ (model κ hκ) () := by
  intro Param hParam η Γ a
  exact Hierarchy.comprehension_of_supported (individuals κ hκ) η
    (assignment_supported κ hκ hParam η) a ()

/-- Choose and unite supports only for values named by this formula. -/
theorem comprehension_of_occurrence_bound (hκ : κ.IsRegular)
    {Param : Ty → Type} {Γ} (a : Formula Param Γ)
    (η : Henkin.Assignment (model κ hκ) Param) (ha : #(occurring a) < κ) :
    (model κ hκ).truth
      (Henkin.eval (model κ hκ) η a.comprehension Henkin.Env.nil) () := by
  let Occ : Type := occurring a
  let X (p : Occ) := Hierarchy.dom (individuals κ hκ) p.val.1
  let value (p : Occ) : X p := η p.val.2
  let support (p : Occ) : Set (Atom κ) :=
    Classical.choose ((X p).supported (value p))
  have hs (p : Occ) : #(support p) < κ ∧
      Supports (atoms κ) (X p).obj (support p) (value p) :=
    Classical.choose_spec ((X p).supported (value p))
  have hS : #(⋃ p : Occ, support p) < κ :=
    (card_iUnion_lt_iff_forall_of_isRegular hκ ha).2 (fun p => (hs p).1)
  apply Hierarchy.comprehension_of_supported_evaluation (individuals κ hκ) a η
  apply Hierarchy.eval_function_supported (individuals κ hκ) a η
    (⋃ p : Occ, support p) hS
  intro p hp
  exact supports_mono (atoms κ) (X ⟨p, hp⟩).obj
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hx⟩) (hs ⟨p, hp⟩).2

theorem occurrence_bounded_comprehension (hκ : κ.IsRegular) :
    OccurrenceBoundedComp κ (model κ hκ) () := by
  intro Param η Γ a ha
  exact comprehension_of_occurrence_bound κ hκ a η ha

/-- Even an infinitary matrix with just finitely many distinct occurring
parameters is covered, regardless of the ambient family's cardinality. -/
theorem finite_occurrence_comprehension (hκ : κ.IsRegular)
    {Param : Ty → Type} {Γ} (a : Formula Param Γ)
    (η : Henkin.Assignment (model κ hκ) Param) (ha : (occurring a).Finite) :
    (model κ hκ).truth
      (Henkin.eval (model κ hκ) η a.comprehension Henkin.Env.nil) () :=
  comprehension_of_occurrence_bound κ hκ a η (ha.lt_aleph0.trans_le hκ.aleph0_le)

/-- All actual finite-branching syntax instances, over arbitrary ambient
parameter families. Finiteness of occurrences is proved from the syntax. -/
theorem finite_branching_comprehension (hκ : κ.IsRegular)
    {Param : Ty → Type} {Γ} (a : Formula Param Γ)
    (η : Henkin.Assignment (model κ hκ) Param) (ha : finitelyBranching a) :
    (model κ hκ).truth
      (Henkin.eval (model κ hκ) η a.comprehension Henkin.Env.nil) () :=
  finite_occurrence_comprehension κ hκ a η (finite_occurring_of_finitelyBranching a ha)

/-- Neither colour class can be covered by fewer than κ atoms. -/
theorem colour_outside {S : Set (Atom κ)} (hS : #S < κ) (b : Bool) :
    ∃ i : κ.ord.ToType, (i, b) ∉ S := by
  classical
  by_contra h
  have hall : ∀ i : κ.ord.ToType, (i, b) ∈ S := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  let f : κ.ord.ToType → S := fun i => ⟨(i, b), hall i⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact congrArg Prod.fst (congrArg Subtype.val hij)
  have hc : κ ≤ #S := by
    simpa only [Cardinal.mk_ord_toType] using Cardinal.mk_le_of_injective hf
  exact (not_le_of_gt hS) hc

def colour (a : Atom κ) : Prop := a.2 = true

/-- A swap outside the proposed support exchanges a true and a false atom. -/
theorem colour_not_supported (hκ : κ.IsRegular) :
    ¬ Supported (atoms κ)
      (function (individuals κ hκ).obj (trivialNom (atoms κ) (ideal κ hκ) Prop).obj)
      (ideal κ hκ) (colour κ) := by
  classical
  rintro ⟨S, hS, hs⟩
  obtain ⟨i, hi⟩ := colour_outside κ hS true
  obtain ⟨j, hj⟩ := colour_outside κ hS false
  letI : DecidableEq (Atom κ) := fun a b => Classical.propDecidable (a = b)
  let g : Equiv.Perm (Atom κ) := Equiv.swap (i, true) (j, false)
  have hg : Fixes (atoms κ) S g := by
    intro a ha
    change g a = a
    exact Equiv.swap_apply_of_ne_of_ne
      (fun he => hi (he ▸ ha)) (fun he => hj (he ▸ ha))
  have he := (function_support_iff (individuals κ hκ)
    (trivialNom (atoms κ) (ideal κ hκ) Prop) S (colour κ)).1 hs g hg (i, true)
  change colour κ (g (i, true)) = colour κ (i, true) at he
  have hs' : g (i, true) = (j, false) := Equiv.swap_apply_left _ _
  rw [hs'] at he
  have ht : colour κ (i, true) := rfl
  have hf : colour κ (j, false) := he.symm ▸ ht
  exact Bool.false_ne_true hf

/-- Actual unbounded formula in exactly the interpreted expanded language. -/
def colourFormula (hκ : κ.IsRegular) : Formula (model κ hκ).Dom [Ty.e] :=
  .iOr κ.ord.ToType (fun i => .eq (.var .zero) (.param (i, true)))

theorem eval_colourFormula (hκ : κ.IsRegular) (a : Atom κ) :
    Henkin.eval (model κ hκ) (Henkin.selfAssignment (model κ hκ))
      (colourFormula κ hκ) (Henkin.Env.cons a Henkin.Env.nil) = colour κ a := by
  change (∃ i : κ.ord.ToType, a = (i, true)) = (a.2 = true)
  apply propext
  constructor
  · rintro ⟨i, rfl⟩
    rfl
  · intro ha
    exact ⟨a.1, Prod.ext rfl ha⟩

theorem colour_comprehension_false (hκ : κ.IsRegular) :
    ¬ (model κ hκ).truth
      (Henkin.eval (model κ hκ) (Henkin.selfAssignment (model κ hκ))
        (colourFormula κ hκ).comprehension Henkin.Env.nil) () := by
  intro hc
  obtain ⟨R, hR⟩ := (Henkin.eval_comprehension_iff (model κ hκ)
    (Henkin.selfAssignment (model κ hκ)) (colourFormula κ hκ) ()).1 hc
  have hfun : R.val = colour κ := by
    funext a
    have h := hR (Henkin.Env.cons a Henkin.Env.nil) ()
    change R.val a ↔ Henkin.eval (model κ hκ) _ (colourFormula κ hκ) _ at h
    exact (propext h).trans (eval_colourFormula κ hκ a)
  exact colour_not_supported κ hκ (hfun ▸ R.property)

theorem not_unrestricted_comprehension (hκ : κ.IsRegular) :
    ¬ Henkin.Comp (model κ hκ) () := by
  intro hc
  exact colour_comprehension_false κ hκ
    (hc _ (Henkin.selfAssignment (model κ hκ)) [Ty.e] (colourFormula κ hκ))

/-- Concrete same-language strictness, with full profile faithfulness and
literal identity necessity. Atomicity is the explicit profile-order property;
C5 and Intensionality are truth of the actual syntax. This is not a claimed
native `Meta.Model` proof-transport certificate. -/
theorem fixed_bound_strictness (hκ : κ.IsRegular) :
    ∃ M : Henkin.Model.{0}, ∃ w : M.World,
      Nonempty (M.Dom Ty.e) ∧ Henkin.Faithful M ∧ AtomicProfiles M ∧
      C5Valid M ∧ IntensionalityValid M ∧
      BoundedComp κ M w ∧ ¬ Henkin.Comp M w ∧
      (∀ p : M.Dom Ty.t, M.app M.boxObj p = p) := by
  exact ⟨model κ hκ, (), individual_nonempty κ hκ,
    Hierarchy.faithful (individuals κ hκ), Hierarchy.atomic_profiles (individuals κ hκ),
    Hierarchy.c5_valid (individuals κ hκ), Hierarchy.intensionality_valid (individuals κ hκ),
    bounded_comprehension κ hκ, not_unrestricted_comprehension κ hκ,
    Hierarchy.box_eq (individuals κ hκ)⟩

/-- Occurrence-sensitive version of the strictness certificate. The old
declared-family endpoint above is preserved as a weaker corollary. -/
theorem occurrence_fixed_bound_strictness (hκ : κ.IsRegular) :
    ∃ M : Henkin.Model.{0}, ∃ w : M.World,
      Nonempty (M.Dom Ty.e) ∧ Henkin.Faithful M ∧ AtomicProfiles M ∧
      C5Valid M ∧ IntensionalityValid M ∧
      OccurrenceBoundedComp κ M w ∧ ¬ Henkin.Comp M w ∧
      (∀ p : M.Dom Ty.t, M.app M.boxObj p = p) := by
  exact ⟨model κ hκ, (), individual_nonempty κ hκ,
    Hierarchy.faithful (individuals κ hκ), Hierarchy.atomic_profiles (individuals κ hκ),
    Hierarchy.c5_valid (individuals κ hκ), Hierarchy.intensionality_valid (individuals κ hκ),
    occurrence_bounded_comprehension κ hκ, not_unrestricted_comprehension κ hκ,
    Hierarchy.box_eq (individuals κ hκ)⟩

/-- C5 here is the actual boxed-ND formula of the same expanded syntax. -/
theorem model_C5 (hκ : κ.IsRegular) {Param : Ty → Type}
    (η : Henkin.Assignment (model κ hκ) Param) {Γ} (σ : Ty)
    (xs : Henkin.Env (model κ hκ) Γ) :
    (model κ hκ).truth (Henkin.eval (model κ hκ) η
      (.box (Term.necessaryDistinctness (Param := Param) σ)) xs) () :=
  Hierarchy.eval_C5 (individuals κ hκ) η σ xs ()

end RegularBound

#print axioms RegularBound.assignment_supported
#print axioms RegularBound.bounded_comprehension
#print axioms RegularBound.colour_not_supported
#print axioms RegularBound.colour_comprehension_false
#print axioms RegularBound.fixed_bound_strictness
#print axioms RegularBound.comprehension_of_occurrence_bound
#print axioms RegularBound.finite_occurrence_comprehension
#print axioms RegularBound.finite_branching_comprehension
#print axioms RegularBound.occurrence_fixed_bound_strictness

end
end Classicism.Research.InfinitaryComprehension.Nominal
