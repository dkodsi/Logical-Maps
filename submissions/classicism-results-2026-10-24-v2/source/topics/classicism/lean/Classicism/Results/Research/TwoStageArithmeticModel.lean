import Classicism.Models.Functions
import Classicism.Semantics.IntensionalFull
import Classicism.Semantics.Numerals
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finite.Prod

/-!
# Full two-stage models with a singleton current individual domain

Direct source: research/2026-10-22/proof-refinements/finite-type-propagation.md,
section 9, unpaginated original research (misc), 23 October 2026.

The model is constructed through the existing full intensional semantics.
False is the root and true the terminal stage. Its only nonidentity arrow
sends the root individual to a specified terminal individual. Full relational
domains retain values on all future arguments, including those with no root
preimage. Internal Infinity verdicts use the existing Numerals soundness
bridge, not an identification of internal and external finiteness by fiat.
-/

noncomputable section

namespace Classicism.Meta.Research.TwoStageArithmeticModel

open CategoryTheory Intensional

local instance finiteSigma {α : Type} {β : α → Type}
    [Finite α] [∀ a, Finite (β a)] : Finite (Σ a, β a) := by
  letI := Fintype.ofFinite α
  letI := fun a => Fintype.ofFinite (β a)
  infer_instance

variable (E : Type) (e₀ : E)

abbrev Points : Bool → Type
  | false => PUnit
  | true => E

def Arrow : ∀ {W V : Bool}, (Points E W → Points E V) → Prop
  | false, false, f => ∀ x, f x = x
  | false, true, f => ∀ x, f x = e₀
  | true, false, _ => False
  | true, true, f => ∀ x, f x = x

theorem arrow_id (W : Bool) : Arrow E e₀ (id : Points E W → Points E W) := by
  cases W <;> exact fun _ => rfl

theorem arrow_comp {W V U : Bool} {f : Points E W → Points E V}
    {g : Points E V → Points E U} (hf : Arrow E e₀ f) (hg : Arrow E e₀ g) :
    Arrow E e₀ (g ∘ f) := by
  cases W <;> cases V <;> cases U
  · exact fun x => (hg (f x)).trans (hf x)
  · exact fun x => hg (f x)
  · exact False.elim hg
  · exact fun x => (hg (f x)).trans (hf x)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hg
  · exact fun x => (hg (f x)).trans (hf x)

abbrev cat : FunCat where
  Obj := Bool
  X := Points E
  Arr := Arrow E e₀
  arr_id := arrow_id E e₀
  arr_comp := arrow_comp E e₀

abbrev root : (cat E e₀).Ob := false
abbrev terminal : (cat E e₀).Ob := true

def entrance : root E e₀ ⟶ terminal E e₀ :=
  FunCat.arr (fun _ => e₀) (fun _ => rfl)

instance homSubsingleton (W V : (cat E e₀).Ob) : Subsingleton (W ⟶ V) := by
  constructor
  intro f g
  apply FunCat.hom_ext
  funext x
  cases W <;> cases V
  · exact (f.property x).trans (g.property x).symm
  · exact (f.property x).trans (g.property x).symm
  · exact False.elim f.property
  · exact (f.property x).trans (g.property x).symm

instance objectsFinite : Finite (cat E e₀).Ob := inferInstanceAs (Finite Bool)

theorem individuals_nonempty (W : (cat E e₀).Ob) : Nonempty ((cat E e₀).De.obj W) := by
  cases W
  · exact ⟨PUnit.unit⟩
  · exact ⟨e₀⟩

abbrev model : Premodel Signature.pure (cat E e₀).Ob :=
  Premodel.full (cat E e₀).De (root E e₀) (individuals_nonempty E e₀)
    (fun c => nomatch c)

theorem isModel : (model E e₀).IsModel := Premodel.full_isModel (cat E e₀).De

theorem isFull : (model E e₀).Full := fullIncl_surjective (cat E e₀).De

theorem isExtFull : (model E e₀).ExtFull := (isFull E e₀).extFull

theorem root_individuals_subsingleton : Subsingleton ((model E e₀).Dom (root E e₀) .e) :=
  inferInstanceAs (Subsingleton PUnit)

theorem root_individuals_finite : Finite ((model E e₀).Dom (root E e₀) .e) :=
  inferInstanceAs (Finite PUnit)

theorem propositions_finite (W : (cat E e₀).Ob) :
    Finite ((model E e₀).Dom W (.rel .t)) := by
  letI : Finite (cat E e₀).Ob := objectsFinite E e₀
  letI : ∀ V : (cat E e₀).Ob, Finite (W ⟶ V) := fun V =>
    Finite.of_injective (fun _ : W ⟶ V => PUnit.unit)
      (fun f g _ => (homSubsingleton E e₀ W V).elim f g)
  change Finite (Set (Σ V : (cat E e₀).Ob, PUnit × (W ⟶ V)))
  infer_instance

/-- Project an e-predicate's future tuple to its terminal individual. -/
def terminalValue (p : Σ V : (cat E e₀).Ob,
    (FullArgs (cat E e₀).De (.arr .e .t)).obj V × (root E e₀ ⟶ V)) : Option E :=
  match p with
  | ⟨false, _⟩ => none
  | ⟨true, ((x, _), _)⟩ => some x

abbrev Predicate := Set (Σ V : (cat E e₀).Ob,
  (FullArgs (cat E e₀).De (.arr .e .t)).obj V × (root E e₀ ⟶ V))

def emptyPredicate : Predicate E e₀ := ∅

def marker (x : E) : Predicate E e₀ :=
  {p | terminalValue E e₀ p = some x}

theorem marker_injective : Function.Injective (marker E e₀) := by
  intro x y hxy
  let p : Σ V : (cat E e₀).Ob,
      (FullArgs (cat E e₀).De (.arr .e .t)).obj V × (root E e₀ ⟶ V) :=
    ⟨terminal E e₀, (x, PUnit.unit), entrance E e₀⟩
  have hx : p ∈ marker E e₀ x := rfl
  have hy : p ∈ marker E e₀ y := hxy ▸ hx
  exact Option.some.inj hy

theorem root_predicates_infinite [Infinite E] :
    Infinite ((model E e₀).Dom (root E e₀) (.rel (.arr .e .t))) :=
  Infinite.of_injective (marker E e₀) (marker_injective E e₀)

theorem marker_ne_empty (x : E) : marker E e₀ x ≠ ∅ := by
  intro he
  have hm : (⟨terminal E e₀, (x, PUnit.unit), entrance E e₀⟩ :
      Σ V : (cat E e₀).Ob, (FullArgs (cat E e₀).De (.arr .e .t)).obj V ×
        (root E e₀ ⟶ V)) ∈ marker E e₀ x := rfl
  rw [he] at hm
  exact hm

theorem marker_application_eq_empty (x : E) (hx : x ≠ e₀)
    (a : (model E e₀).Dom (root E e₀) .e) :
    (model E e₀).apply ((model E e₀).Incl (.rel (.arr .e .t)) (root E e₀) (marker E e₀ x))
        ((model E e₀).Incl .e (root E e₀) a) =
      (model E e₀).apply ((model E e₀).Incl (.rel (.arr .e .t)) (root E e₀) (emptyPredicate E e₀))
        ((model E e₀).Incl .e (root E e₀) a) := by
  rw [(model E e₀).apply_Incl, (model E e₀).apply_Incl]
  ext ⟨V, ⟨⟩, k⟩
  cases V
  · change (none : Option E) = some x ↔ False
    simp
  · change some ((k : {f : PUnit → E // ∀ a, f a = e₀}).val a) = some x ↔ False
    have hk := (k : {f : PUnit → E // ∀ a, f a = e₀}).property a
    rw [hk]
    exact ⟨fun h => hx (Option.some.inj h).symm, False.elim⟩

/-- Two predicates agree as proposition objects on the sole current individual,
but differ on a future individual. This refutes the exact Functionality instance. -/
theorem not_functionality (x : E) (hx : x ≠ e₀) :
    ¬ (model E e₀).HoldsSentence (Classicism.P.Functionality.quoted .e .t) := by
  intro hF
  simp only [Premodel.HoldsSentence, Classicism.P.Functionality.quoted,
    (model E e₀).holds_forall (isModel E e₀),
    (model E e₀).holds_imp (isModel E e₀),
    (model E e₀).holds_eq (isModel E e₀)] at hF
  have he := hF (marker E e₀ x) (emptyPredicate E e₀) (fun a => marker_application_eq_empty E e₀ x hx a)
  exact marker_ne_empty E e₀ x
    ((model E e₀).Incl_injective (.rel (.arr .e .t)) (root E e₀) he)

/-- Every closed admitted type is externally finite when the terminal base is. -/
theorem all_domains_finite [Finite E] :
    ∀ σ : Ty, ∀ W : (cat E e₀).Ob, Finite ((model E e₀).Dom W σ) := by
  let motiveT := fun σ : Ty => ∀ W : (cat E e₀).Ob, Finite ((FullT (cat E e₀).De σ).obj W)
  let motiveR := fun ρ : RTy => ∀ W : (cat E e₀).Ob, Finite ((FullArgs (cat E e₀).De ρ).obj W)
  apply Ty.rec (motive_1 := motiveT) (motive_2 := motiveR)
  · intro W
    cases W <;> change Finite _ <;> infer_instance
  · intro ρ ih W
    letI : Finite (cat E e₀).Ob := objectsFinite E e₀
    letI : ∀ V : (cat E e₀).Ob, Finite (W ⟶ V) := fun V =>
      Finite.of_injective (fun _ : W ⟶ V => PUnit.unit)
        (fun f g _ => (homSubsingleton E e₀ W V).elim f g)
    letI : ∀ V : (cat E e₀).Ob, Finite ((FullArgs (cat E e₀).De ρ).obj V) := ih
    change Finite (Set (Σ V : (cat E e₀).Ob,
      (FullArgs (cat E e₀).De ρ).obj V × (W ⟶ V)))
    infer_instance
  · intro _ W
    cases W <;> change Finite _ <;> infer_instance
  · intro W
    exact inferInstanceAs (Finite PUnit)
  · intro σ ρ ihσ ihρ W
    letI := ihσ W
    letI := ihρ W
    change Finite (((FullT (cat E e₀).De σ).obj W) × ((FullArgs (cat E e₀).De ρ).obj W))
    infer_instance

abbrev infiniteModel := model Nat 0
abbrev finiteModel := model Bool false

theorem infiniteModel_isModel : infiniteModel.IsModel := isModel Nat 0
theorem finiteModel_isModel : finiteModel.IsModel := isModel Bool false

theorem infiniteModel_finite_bases_infinite_predicates :
    Finite (infiniteModel.Dom (root Nat 0) .e) ∧
      Finite (infiniteModel.Dom (root Nat 0) (.rel .t)) ∧
      Infinite (infiniteModel.Dom (root Nat 0) (.rel (.arr .e .t))) :=
  ⟨root_individuals_finite Nat 0, propositions_finite Nat 0 _, root_predicates_infinite Nat 0⟩

theorem finiteModel_all_domains_finite (σ : Ty) (W : (cat Bool false).Ob) :
    Finite (finiteModel.Dom W σ) := all_domains_finite Bool false σ W

/-- Actual, quantified Frege Infinity: both bases fail it and the predicate type
satisfies it, in one and the same full C-model at its root. -/
theorem infiniteModel_internal_verdicts :
    ¬ infiniteModel.HoldsSentence (axInf .e) ∧
      ¬ infiniteModel.HoldsSentence (axInf (.rel .t)) ∧
      infiniteModel.HoldsSentence (axInf (.rel (.arr .e .t))) := by
  letI : Finite (infiniteModel.Dom infiniteModel.W₀ .e) := root_individuals_finite Nat 0
  letI : Finite (infiniteModel.Dom infiniteModel.W₀ (.rel .t)) := propositions_finite Nat 0 (root Nat 0)
  letI : Infinite (infiniteModel.Dom infiniteModel.W₀ (.rel (.arr .e .t))) := root_predicates_infinite Nat 0
  exact ⟨Premodel.not_holds_axInf_of_finite infiniteModel_isModel (𝟙 _) .e,
    Premodel.not_holds_axInf_of_finite infiniteModel_isModel (𝟙 _) (.rel .t),
    Premodel.holds_axInf_of_infinite infiniteModel_isModel (isExtFull Nat 0)
      (𝟙 _) (.rel (.arr .e .t))⟩

theorem finiteModel_internal_finiteness (σ : Ty) :
    ¬ finiteModel.HoldsSentence (axInf σ) := by
  letI : Finite (finiteModel.Dom finiteModel.W₀ σ) := finiteModel_all_domains_finite σ (root Bool false)
  exact Premodel.not_holds_axInf_of_finite finiteModel_isModel (𝟙 _) σ

theorem finiteModel_not_functionality :
    ¬ finiteModel.HoldsSentence (Classicism.P.Functionality.quoted .e .t) :=
  not_functionality Bool false true (by decide)

theorem infiniteModel_not_functionality :
    ¬ infiniteModel.HoldsSentence (Classicism.P.Functionality.quoted .e .t) :=
  not_functionality Nat 0 1 (by decide)

end Classicism.Meta.Research.TwoStageArithmeticModel

#print axioms Classicism.Meta.Research.TwoStageArithmeticModel.infiniteModel_isModel
#print axioms Classicism.Meta.Research.TwoStageArithmeticModel.infiniteModel_finite_bases_infinite_predicates
#print axioms Classicism.Meta.Research.TwoStageArithmeticModel.finiteModel_all_domains_finite
#print axioms Classicism.Meta.Research.TwoStageArithmeticModel.infiniteModel_internal_verdicts
#print axioms Classicism.Meta.Research.TwoStageArithmeticModel.finiteModel_internal_finiteness
#print axioms Classicism.Meta.Research.TwoStageArithmeticModel.finiteModel_not_functionality
