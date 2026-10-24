import Classicism.Results.Research.ChoiceOrbitAveraging
import Classicism.Results.Research.ActualityCore

/-!
# Actuality and internal generation of truth-equivalence classes

Direct source: `research/2026-10-23/choice-transversal-coherence/continuation-code-operations.md`,
§§3–4 (original research, misc, 23 October 2026, unpaginated).
This file proves the exact nullary propositional equivalence. It does not claim
an all-relational schema certificate or assume RC. The unary property version
below states its explicit inhabitation requirement.
-/

namespace Classicism.Research.OrbitActuality
open Classicism.Paper Classicism.P Classicism.Research.OrbitAveraging

def TruthCanonicalizer (j : Prop → Prop) : Prop :=
  (∀ p : Prop, j p ↔ p) ∧ ∀ p q : Prop, (p ↔ q) → j p = j q

def TruthGenerator : Prop :=
  ∃ g : Prop → Prop,
    (∀ p : Prop, g p ↔ p) ∧
    ∀ p q : Prop, (p ↔ q) → Orbit g p q

theorem canonicalizer_truth_test (j : Prop → Prop) (hj : TruthCanonicalizer j)
    (p : Prop) : (j p = j True) ↔ p := by
  constructor
  · intro he
    exact (hj.1 p).1 (Eq.mpr he ((hj.1 True).2 trivial))
  · intro hp
    exact hj.2 p True ⟨fun _ => trivial, fun _ => hp⟩

theorem truthCanonicalizer_actuality (j : Prop → Prop)
    (hj : TruthCanonicalizer j) : Actuality := by
  apply Classicism.Research.positiveEvaluator_actuality
  refine ⟨fun p => j p = j True, ?_⟩
  refine ⟨fun p => canonicalizer_truth_test j hj p, ?_⟩
  intro p hp
  exact necessity_of_identity (j p) (j True)
    ((canonicalizer_truth_test j hj p).2 hp)

theorem truthGenerator_actuality : TruthGenerator → Actuality := by
  intro h
  obtain ⟨g, hg, ho⟩ := h
  apply truthCanonicalizer_actuality (AverageT g)
  refine ⟨fun p => averageT_coext_of_preserves g hg p, ?_⟩
  intro p q hpq
  exact averageT_eq_of_orbit g p q (ho p q hpq)

theorem actuality_truthGenerator : Actuality → TruthGenerator := by
  intro h
  obtain ⟨w, hw⟩ := h
  refine ⟨fun p => w ∧ p, ?_, ?_⟩
  · intro p
    exact ⟨And.right, fun hp => ⟨hw.1, hp⟩⟩
  · intro p q hpq P hP
    have he : (w ∧ p) = (w ∧ q) :=
      (Classicism.Research.ActualityCore.truth_eq_iff w hw p q).2 hpq
    have hpg : P (w ∧ p) := (hP.2 p).1 hP.1
    exact (hP.2 q).2 (Eq.mp (congrArg P he) hpg)

theorem actuality_iff_truthGenerator : Actuality ↔ TruthGenerator :=
  ⟨actuality_truthGenerator, truthGenerator_actuality⟩

def PropertyGenerator (σ : Type) [Ty σ] : Prop :=
  ∃ g : (σ → Prop) → (σ → Prop),
    (∀ A, coext (g A) A) ∧
    ∀ A B, coext A B → Orbit g A B

theorem propertyGenerator_actuality {σ : Type} [Ty σ]
    (a : σ) (h : PropertyGenerator σ) : Actuality := by
  obtain ⟨g, hg, ho⟩ := h
  apply truthCanonicalizer_actuality (fun p => Average g (fun _ : σ => p) a)
  refine ⟨?_, ?_⟩
  · intro p
    exact average_coext_of_preserves g hg (fun _ : σ => p) a
  · intro p q hpq
    have he := average_eq_of_orbit g (fun _ : σ => p) (fun _ : σ => q)
      (ho _ _ (fun _ => hpq))
    exact congrFun he a

theorem actuality_propertyGenerator {σ : Type} [Ty σ] :
    Actuality → PropertyGenerator σ := by
  intro h
  obtain ⟨w, hw⟩ := h
  refine ⟨fun A x => w ∧ A x, ?_, ?_⟩
  · intro A x
    exact ⟨And.right, fun hA => ⟨hw.1, hA⟩⟩
  · intro A B hAB P hP
    have he : (fun x => w ∧ A x) = (fun x => w ∧ B x) := by
      apply Classicism.Research.ActualityCore.localized_eq w hw
      · exact le_of_box_incl (nec% (fun (x : σ) (h : w ∧ A x) => h.1))
      · exact le_of_box_incl (nec% (fun (x : σ) (h : w ∧ B x) => h.1))
      · intro x
        exact ⟨fun hx => ⟨hx.1, (hAB x).1 hx.2⟩,
          fun hx => ⟨hx.1, (hAB x).2 hx.2⟩⟩
    have hpg : P (fun x => w ∧ A x) := (hP.2 A).1 hP.1
    exact (hP.2 B).2 (Eq.mp (congrArg P he) hpg)

theorem actuality_iff_propertyGenerator {σ : Type} [Ty σ] (a : σ) :
    Actuality ↔ PropertyGenerator σ :=
  ⟨actuality_propertyGenerator, propertyGenerator_actuality a⟩

end Classicism.Research.OrbitActuality
