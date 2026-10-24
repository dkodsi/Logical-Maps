import Classicism.Semantics.IntensionalExamples
import Classicism.Semantics.Numerals
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finite.Prod

/-!
# Four C5 witnesses for the two base finiteness verdicts

Original construction (misc), 23 October 2026, unpaginated. This is an
action-model realization of the four patterns in finite-type-propagation.md,
section 8. It is not asserted to be literally the Boolean-valued presentation
used there. Individuals carry a constant action on a one-object groupoid;
propositions are all sets of arrows. Varying the individual set and the group
independently gives all four actual quantified-Infinity verdicts. Every type
also satisfies necessary distinctness, by the existing groupoid theorem.
-/

noncomputable section

namespace Classicism.Meta.Research.FourC5FinitenessModels

open CategoryTheory Intensional

local instance finiteSigma {α : Type} {β : α → Type}
    [Finite α] [∀ a, Finite (β a)] : Finite (Σ a, β a) := by
  letI := Fintype.ofFinite α
  letI := fun a => Fintype.ofFinite (β a)
  infer_instance

variable (I G : Type) [Group G] (i₀ : I)

def individuals : SingleObj G ⥤ Type := (Functor.const (SingleObj G)).obj I

def model : Premodel Signature.pure (SingleObj G) :=
  Premodel.full (individuals I G) (SingleObj.star G) (fun _ => ⟨i₀⟩)
    (fun c => nomatch c)

theorem isModel : (model I G i₀).IsModel := Premodel.full_isModel _

theorem isFull : (model I G i₀).Full := fullIncl_surjective (individuals I G)

theorem isExtFull : (model I G i₀).ExtFull := (isFull I G i₀).extFull

theorem necessary_distinctness (σ : Ty) :
    (model I G i₀).HoldsSentence (Term.box (Sentence.nd σ)) :=
  Premodel.holds_box_nd_of_groupoid _ (isModel I G i₀) σ

theorem individuals_finite [Finite I] :
    Finite ((model I G i₀).Dom (SingleObj.star G) .e) := inferInstanceAs (Finite I)

theorem individuals_infinite [Infinite I] :
    Infinite ((model I G i₀).Dom (SingleObj.star G) .e) := inferInstanceAs (Infinite I)

theorem propositions_finite [Finite G] :
    Finite ((model I G i₀).Dom (SingleObj.star G) (.rel .t)) := by
  letI : Finite (SingleObj G) := inferInstanceAs (Finite Unit)
  letI : ∀ V W : SingleObj G, Finite (V ⟶ W) := fun _ _ => inferInstanceAs (Finite G)
  change Finite (Set (Σ U : SingleObj G, PUnit × (SingleObj.star G ⟶ U)))
  infer_instance

theorem propositions_infinite [Infinite G] :
    Infinite ((model I G i₀).Dom (SingleObj.star G) (.rel .t)) := by
  change Infinite (Set (Σ U : SingleObj G, PUnit × (SingleObj.star G ⟶ U)))
  letI : Infinite (Σ U : SingleObj G, PUnit × (SingleObj.star G ⟶ U)) :=
    Infinite.of_injective
      (fun m : G => (⟨SingleObj.star G, PUnit.unit, m⟩ :
        Σ U : SingleObj G, PUnit × (SingleObj.star G ⟶ U)))
      (fun m n e => by
        obtain ⟨_, hh⟩ := Sigma.mk.inj_iff.mp e
        exact (Prod.mk.inj (eq_of_heq hh)).2)
  exact Infinite.of_injective (fun x => ({x} : Set _)) Set.singleton_injective

theorem finite_e [Finite I] : ¬ (model I G i₀).HoldsSentence (axInf .e) := by
  letI : Finite ((model I G i₀).Dom (model I G i₀).W₀ .e) := individuals_finite I G i₀
  exact Premodel.not_holds_axInf_of_finite (isModel I G i₀) (𝟙 _) .e

theorem infinite_e [Infinite I] : (model I G i₀).HoldsSentence (axInf .e) := by
  letI : Infinite ((model I G i₀).Dom (model I G i₀).W₀ .e) := individuals_infinite I G i₀
  exact Premodel.holds_axInf_of_infinite (isModel I G i₀) (isExtFull I G i₀) (𝟙 _) .e

theorem finite_t [Finite G] : ¬ (model I G i₀).HoldsSentence (axInf (.rel .t)) := by
  letI : Finite ((model I G i₀).Dom (model I G i₀).W₀ (.rel .t)) := propositions_finite I G i₀
  exact Premodel.not_holds_axInf_of_finite (isModel I G i₀) (𝟙 _) (.rel .t)

theorem infinite_t [Infinite G] : (model I G i₀).HoldsSentence (axInf (.rel .t)) := by
  letI : Infinite ((model I G i₀).Dom (model I G i₀).W₀ (.rel .t)) := propositions_infinite I G i₀
  exact Premodel.holds_axInf_of_infinite (isModel I G i₀) (isExtFull I G i₀) (𝟙 _) (.rel .t)

abbrev finiteFinite := model Unit Unit ()
abbrev infiniteFinite := model Nat Unit 0
abbrev finiteInfinite := model Unit (Equiv.Perm Nat) ()
abbrev infiniteInfinite := model Nat (Equiv.Perm Nat) 0

theorem finite_finite_verdicts :
    ¬ finiteFinite.HoldsSentence (axInf .e) ∧
      ¬ finiteFinite.HoldsSentence (axInf (.rel .t)) :=
  ⟨finite_e Unit Unit (), finite_t Unit Unit ()⟩

theorem infinite_finite_verdicts :
    infiniteFinite.HoldsSentence (axInf .e) ∧
      ¬ infiniteFinite.HoldsSentence (axInf (.rel .t)) :=
  ⟨infinite_e Nat Unit 0, finite_t Nat Unit 0⟩

theorem finite_infinite_verdicts :
    ¬ finiteInfinite.HoldsSentence (axInf .e) ∧
      finiteInfinite.HoldsSentence (axInf (.rel .t)) :=
  ⟨finite_e Unit (Equiv.Perm Nat) (), infinite_t Unit (Equiv.Perm Nat) ()⟩

theorem infinite_infinite_verdicts :
    infiniteInfinite.HoldsSentence (axInf .e) ∧
      infiniteInfinite.HoldsSentence (axInf (.rel .t)) :=
  ⟨infinite_e Nat (Equiv.Perm Nat) 0, infinite_t Nat (Equiv.Perm Nat) 0⟩

end Classicism.Meta.Research.FourC5FinitenessModels

#print axioms Classicism.Meta.Research.FourC5FinitenessModels.isModel
#print axioms Classicism.Meta.Research.FourC5FinitenessModels.necessary_distinctness
#print axioms Classicism.Meta.Research.FourC5FinitenessModels.finite_finite_verdicts
#print axioms Classicism.Meta.Research.FourC5FinitenessModels.infinite_finite_verdicts
#print axioms Classicism.Meta.Research.FourC5FinitenessModels.finite_infinite_verdicts
#print axioms Classicism.Meta.Research.FourC5FinitenessModels.infinite_infinite_verdicts
