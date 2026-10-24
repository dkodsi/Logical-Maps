import Classicism.Results.Research.FullLogicalObserversAtomic

/-!
# The finitary observer side of Infinitary Comprehension

Original source: `research/2026-10-23/infinitary-comprehension/
logical-observer-separation.md`, §§1, 5--6; misc, 23 October 2026.

These are genuine theorems of the existing gated C layer. The material
qualification below is the singleton type-list, proposition-separation
instance of the earlier Logical Observer Separation schema. It includes
both quantifiers and the translated equality guards. It is not silently
replaced by the full-composite observer qualification.

The conclusions do not assert that Infinitary Comprehension has already
been translated into the existing finite syntax, or that a raw lambda-free
H bootstrap is certified. Atomicity is an explicit premise in the reverse
implications; its infinitary derivation is a separate module. No optional
premise is necessitated.
-/

namespace Classicism.Research.InfinitaryComprehensionObservers
open Classicism.P Classicism.Paper
open FullLogicalObservers

/-- Literal pointwise Boolean preservation, as in material OS. -/
def BooleanPointwise (E : Prop → Prop) : Prop :=
  E True = True ∧ E False = False ∧
  (∀ p : Prop, E (¬ p) = ¬ E p) ∧
  (∀ p q : Prop, E (p ∧ q) = (E p ∧ E q)) ∧
  (∀ p q : Prop, E (p ∨ q) = (E p ∨ E q))

/-- Both material quantifier laws and the original translated R/L guards. -/
def LogicalQualified (σ : Type) [Ty σ] (E : Prop → Prop) : Prop :=
  BooleanPointwise E ∧
  (∀ F : σ → Prop, E (∀ x, F x) ↔ ∀ x, E (F x)) ∧
  (∀ F : σ → Prop, E (∃ x, F x) ↔ ∃ x, E (F x)) ∧
  (∀ x : σ, E (x = x)) ∧
  (∀ x y : σ, ∀ F : σ → Prop, E (x = y) → E (F x) → E (F y))

/-- Exactly the t-instance of material OS with the single listed type σ. -/
def LogicalSeparation (σ : Type) [Ty σ] : Prop :=
  ∀ p q : Prop, p = q ↔
    ∀ E : Prop → Prop, LogicalQualified σ E → (E p ↔ E q)

/-- This extra clause fixes identity propositions; it is not one of the
original translated equality guards. -/
def FixesPropositionalIdentity (E : Prop → Prop) : Prop :=
  ∀ p q : Prop, E (p = q) = (p = q)

def EqualityQualified (σ : Type) [Ty σ] (E : Prop → Prop) : Prop :=
  LogicalQualified σ E ∧ FixesPropositionalIdentity E

def EqualitySeparation (σ : Type) [Ty σ] : Prop :=
  ∀ p q : Prop, p = q ↔
    ∀ E : Prop → Prop, EqualityQualified σ E → (E p ↔ E q)

theorem logical_separation_barcan {σ : Type} [Ty σ]
    (sep : LogicalSeparation σ) : Barcan σ := by
  intro F hF
  apply (sep (∀ x, F x) True).2
  intro E hE
  have ht : E True := Eq.mpr hE.1.1 trivial
  exact ⟨fun _ => ht, fun _ => (hE.2.1 F).2
    (fun x => Eq.mpr (congrArg E (hF x)) ht)⟩

/-- Strengthening the observer qualification strengthens separation. -/
theorem equality_separation_logical {σ : Type} [Ty σ]
    (sep : EqualitySeparation σ) : LogicalSeparation σ :=
  fun p q => ⟨fun he E _ => he ▸ Iff.rfl,
    fun h => (sep p q).2 (fun E hE => h E hE.1)⟩

theorem equality_separation_barcan {σ : Type} [Ty σ]
    (sep : EqualitySeparation σ) : Barcan σ :=
  logical_separation_barcan (equality_separation_logical sep)

/-- If p and q differ, every equality-fixing observer sees (p=q) as false.
Separation therefore identifies that identity proposition with bottom. -/
theorem equality_separation_nd {σ : Type} [Ty σ]
    (sep : EqualitySeparation σ) : NecessityOfDistinctness Prop := by
  intro p q hpq
  have hbot : (p = q) = False := by
    apply (sep (p = q) False).2
    intro E hE
    exact ⟨fun h => False.elim (hpq (Eq.mp (hE.2 p q) h)),
      fun h => False.elim (Eq.mp hE.1.1.2.1 h)⟩
  exact Eq.mpr (box_not_eq (p = q)) hbot

/-- Only the t instance of ND and the t quantifier qualification are needed. -/
theorem logical_separation_nd_c5
    (sep : LogicalSeparation Prop) (nd : NecessityOfDistinctness Prop) :
    NecNecessityOfDistinctness Prop :=
  Proofs.nd_and_bf_imply_necessary_nd nd (logical_separation_barcan sep)

theorem equality_separation_c5 (sep : EqualitySeparation Prop) :
    NecNecessityOfDistinctness Prop :=
  logical_separation_nd_c5 (equality_separation_logical sep)
    (equality_separation_nd sep)

theorem logical_separation_nd_necessary_nd {σ : Type} [Ty σ]
    (sep : LogicalSeparation Prop) (nd : NecessityOfDistinctness Prop) :
    NecNecessityOfDistinctness σ :=
  Proofs.necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r
    (logical_separation_nd_c5 sep nd)

theorem equality_separation_necessary_nd {σ : Type} [Ty σ]
    (sep : EqualitySeparation Prop) : NecNecessityOfDistinctness σ :=
  Proofs.necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r
    (equality_separation_c5 sep)

/-- With ND at σ, identity propositions are top or bottom, so preservation
of those two constants alone fixes them. This uses neither Fregean collapse
nor conditional propositional extensionality. -/
theorem fixes_identity_of_nd {σ : Type} [Ty σ] (E : Prop → Prop)
    (ht : E True = True) (hb : E False = False)
    (nd : NecessityOfDistinctness σ) (x y : σ) : E (x = y) = (x = y) := by
  apply (em (x = y)).elim
  · intro hxy
    have he : (x = y) = True := necessity_of_identity x y hxy
    exact (congrArg E he).trans (ht.trans he.symm)
  · intro hxy
    have he : (x = y) = False := Eq.mp (box_not_eq (x = y)) (nd x y hxy)
    exact (congrArg E he).trans (hb.trans he.symm)

theorem bool_full_pointwise (E : Prop → Prop) (hE : BoolFull E) :
    BooleanPointwise E :=
  ⟨boolFull_top hE, boolFull_bot hE, boolFull_not hE,
    boolFull_and hE, boolFull_or hE⟩

/-- In C5 a full-composite observer qualifies for material OS, including R/L. -/
theorem full_qualified_logical {σ : Type} [Ty σ] (E : Prop → Prop)
    (hc5 : NecNecessityOfDistinctness Prop) (hE : QualifiedFull σ E) :
    LogicalQualified σ E := by
  have nd : NecessityOfDistinctness σ :=
    Proofs.necessary_distinctness_necessary_t_implies_distinctness_necessary_r hc5
  have he : ∀ x y : σ, E (x = y) = (x = y) :=
    fixes_identity_of_nd E (boolFull_top hE.1) (boolFull_bot hE.1) nd
  exact ⟨bool_full_pointwise E hE.1,
    (fun F => ⟨Eq.mp (quantifierFull_forall hE.2 F),
      Eq.mpr (quantifierFull_forall hE.2 F)⟩),
    (fun F => ⟨Eq.mp (quantifierFull_exists hE.2 F),
      Eq.mpr (quantifierFull_exists hE.2 F)⟩),
    (fun x => Eq.mpr (he x x) rfl),
    (fun x y F hxy hFx => (Eq.mp (he x y) hxy) ▸ hFx)⟩

theorem full_qualified_equality {σ : Type} [Ty σ] (E : Prop → Prop)
    (hc5 : NecNecessityOfDistinctness Prop) (hE : QualifiedFull σ E) :
    EqualityQualified σ E :=
  ⟨full_qualified_logical E hc5 hE,
    fixes_identity_of_nd E (boolFull_top hE.1) (boolFull_bot hE.1)
      (box_elim hc5)⟩

/-- The same previously constructed principal observers witness the converse;
no new fullness assumption or external selection is used. -/
theorem c5_atomicity_equality_separation {σ : Type} [Ty σ]
    (hat : Atomicity Prop) (hc5 : NecNecessityOfDistinctness Prop) :
    EqualitySeparation σ := by
  intro p q
  exact ⟨fun he E _ => he ▸ Iff.rfl, fun h =>
    (c5_atomicity_full_separation (σ := σ) hat hc5 p q).2
      (fun E hE => Eq.mpr (boolFull_iff hE.1 p q)
        (h E (full_qualified_equality E hc5 hE)))⟩

theorem c5_atomicity_logical_separation {σ : Type} [Ty σ]
    (hat : Atomicity Prop) (hc5 : NecNecessityOfDistinctness Prop) :
    LogicalSeparation σ :=
  equality_separation_logical (c5_atomicity_equality_separation hat hc5)

/-- Exact finite C-side characterization once Atomicity is available.
The full all-type observer schema is not needed in the forward direction. -/
theorem atomicity_equality_separation_iff_c5 (hat : Atomicity Prop) :
    EqualitySeparation Prop ↔ NecNecessityOfDistinctness Prop :=
  ⟨equality_separation_c5, c5_atomicity_equality_separation hat⟩

theorem atomicity_logical_separation_nd_iff_c5 (hat : Atomicity Prop) :
    (LogicalSeparation Prop ∧ NecessityOfDistinctness Prop) ↔
      NecNecessityOfDistinctness Prop :=
  ⟨fun h => logical_separation_nd_c5 h.1 h.2,
    fun hc5 => ⟨c5_atomicity_logical_separation hat hc5, box_elim hc5⟩⟩

end Classicism.Research.InfinitaryComprehensionObservers
