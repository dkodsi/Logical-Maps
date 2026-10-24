import Classicism.Results.Research.Evaluator

/-!
# Canonical normalized actual evaluation

Direct source: `research/2026-10-22/proof-refinements/canonical-actual-evaluator.md`,
§§1–3 (unpaginated original research, `misc`, 22 October 2026).
The kernel here uses implication. It is an Actuality witness, hence identical
to the source's biconditional kernel by uniqueness of actual worlds.
-/

namespace Classicism.Research
open Classicism.Paper Classicism.P

def worldEvaluator (w : Prop) : Prop → Prop := fun p => □ (w → p)
def canonicalEvaluator (E : Prop → Prop) : Prop → Prop := worldEvaluator (truthKernel E)

theorem evaluator_endpoints_possible (E : Prop → Prop) (w : Prop) :
    E w = True → E False = False → ◇ w := fun hw hf h =>
  Eq.mp (hw.symm.trans ((congrArg E h).trans hf)) trivial

theorem actualEvaluator_kernel_possible (E : Prop → Prop) (h : ActualEvaluator E) :
    □ (◇ (truthKernel E)) :=
  modal_K _ _ (modal_K _ _ (nec% (evaluator_endpoints_possible E (truthKernel E)))
    (necessity_of_identity _ _ ((h _).1
      (positiveEvaluator_actualWorld E (actualEvaluator_positive E h)).1)))
    (necessity_of_identity _ _ ((h False).2 (fun hf => hf)))

theorem incompatible_world_tests_step (w p : Prop) :
    (w → ¬ p) → (w → p) → ¬ w := fun hn hp hw => hn hw (hp hw)

theorem incompatible_world_tests (w p : Prop) :
    □ (w → ¬ p) → ◇ w → ¬ □ (w → p) := fun hn hw hp =>
  hw ((box_not_eq w).mp (modal_K _ _
    (modal_K _ _ (nec% (incompatible_world_tests_step w p)) hn) hp))

/-- Stability of the actual world, in addition to Actuality, normalizes both endpoints. -/
theorem worldEvaluator_actual (w : Prop) (hw : ActualWorld w) (hs : □ (◇ w)) :
    ActualEvaluator (worldEvaluator w) := by
  intro p
  refine ⟨fun hp => modal_four _ ((le_iff_prop w p).1 (hw.2 p hp)), ?_⟩
  intro hn
  apply (box_not_eq _).mp
  exact modal_K _ _ (modal_K _ _ (nec% (incompatible_world_tests w p))
    (modal_four _ ((le_iff_prop w (¬ p)).1 (hw.2 (¬ p) hn)))) hs

theorem canonicalEvaluator_actual (E : Prop → Prop) (h : ActualEvaluator E) :
    ActualEvaluator (canonicalEvaluator E) :=
  worldEvaluator_actual _ (positiveEvaluator_actualWorld E (actualEvaluator_positive E h))
    (actualEvaluator_kernel_possible E h)

/-- This is identity by substituting equal kernels, without unrestricted Functionality. -/
theorem canonicalEvaluator_unique (E F : Prop → Prop)
    (hE : ActualEvaluator E) (hF : ActualEvaluator F) :
    canonicalEvaluator E = canonicalEvaluator F :=
  congrArg worldEvaluator
    (actualWorld_unique _ _ (positiveEvaluator_actualWorld E (actualEvaluator_positive E hE))
      (positiveEvaluator_actualWorld F (actualEvaluator_positive F hF)))

theorem canonicalEvaluator_idempotent (E : Prop → Prop) (hE : ActualEvaluator E) :
    canonicalEvaluator (canonicalEvaluator E) = canonicalEvaluator E :=
  canonicalEvaluator_unique _ E (canonicalEvaluator_actual E hE) hE

theorem world_all_instance {σ : Type} [Ty σ] (w : Prop) (F : σ → Prop) (a : σ) :
    (w → ∀ x, F x) → (w → F a) := fun h hw => h hw a

theorem world_all_test {σ : Type} [Ty σ] (w : Prop) (F : σ → Prop) :
    □ (w → ∀ x, F x) → ∀ x, worldEvaluator w (F x) :=
  fun h x => modal_K _ _ (nec% (world_all_instance w F x)) h

theorem not_all_test {σ : Type} [Ty σ] (w : Prop) (F : σ → Prop) (a : σ) :
    ¬ worldEvaluator w (F a) → ¬ (∀ x, worldEvaluator w (F x)) := fun h hall => h (hall a)

/-- Literal universal commutation at each current predicate; no boxed predicate quantifier. -/
theorem worldEvaluator_all {σ : Type} [Ty σ] (w : Prop) (hw : ActualWorld w)
    (hs : □ (◇ w)) (F : σ → Prop) :
    worldEvaluator w (∀ x, F x) = (∀ x, worldEvaluator w (F x)) := by
  have he := worldEvaluator_actual w hw hs
  apply (em (∀ x, F x)).elim
  · intro hall
    have hl : □ (w → ∀ x, F x) := (le_iff_prop _ _).1 (hw.2 _ hall)
    have hq : □ (∀ x, worldEvaluator w (F x)) :=
      modal_K _ _ (nec% (world_all_test w F)) (modal_four _ hl)
    exact ((he _).1 hall).trans hq.symm
  · intro hn
    obtain ⟨a, ha⟩ := (not_forall_eq F).mp hn
    have hna : □ (¬ worldEvaluator w (F a)) := (box_not_eq _).mpr ((he _).2 ha)
    have hq : (∀ x, worldEvaluator w (F x)) = False :=
      (box_not_eq _).mp (modal_K _ _ (nec% (not_all_test w F a)) hna)
    exact ((he _).2 hn).trans hq.symm

theorem canonicalEvaluator_all {σ : Type} [Ty σ] (E : Prop → Prop)
    (h : ActualEvaluator E) (F : σ → Prop) :
    canonicalEvaluator E (∀ x, F x) = (∀ x, canonicalEvaluator E (F x)) :=
  worldEvaluator_all _ (positiveEvaluator_actualWorld E (actualEvaluator_positive E h))
    (actualEvaluator_kernel_possible E h) F

theorem world_exists_intro {σ : Type} [Ty σ] (w : Prop) (F : σ → Prop) (a : σ) :
    worldEvaluator w (F a) → (∃ x, worldEvaluator w (F x)) := fun h => ⟨a, h⟩

theorem world_not_exists_instance {σ : Type} [Ty σ] (w : Prop) (F : σ → Prop) (a : σ) :
    (w → ¬ ∃ x, F x) → (w → ¬ F a) := fun h hw ha => h hw ⟨a, ha⟩

theorem world_no_exists_test {σ : Type} [Ty σ] (w : Prop) (F : σ → Prop) :
    □ (w → ¬ ∃ x, F x) → ◇ w → ¬ (∃ x, worldEvaluator w (F x)) :=
  fun hn hw h => h.elim fun a ha => incompatible_world_tests w (F a)
    (modal_K _ _ (nec% (world_not_exists_instance w F a)) hn) hw ha

/-- Literal existential commutation for each current predicate. -/
theorem worldEvaluator_exists {σ : Type} [Ty σ] (w : Prop) (hw : ActualWorld w)
    (hs : □ (◇ w)) (F : σ → Prop) :
    worldEvaluator w (∃ x, F x) = (∃ x, worldEvaluator w (F x)) := by
  have he := worldEvaluator_actual w hw hs
  apply (em (∃ x, F x)).elim
  · intro hex
    obtain ⟨a, ha⟩ := hex
    have hr : □ (∃ x, worldEvaluator w (F x)) :=
      modal_K _ _ (nec% (world_exists_intro w F a)) ((he _).1 ha)
    exact ((he _).1 ⟨a, ha⟩).trans hr.symm
  · intro hn
    have hl : □ (w → ¬ ∃ x, F x) := (le_iff_prop _ _).1 (hw.2 _ hn)
    have hr : (∃ x, worldEvaluator w (F x)) = False :=
      (box_not_eq _).mp (modal_K _ _ (modal_K _ _
        (nec% (world_no_exists_test w F)) (modal_four _ hl)) hs)
    exact ((he _).2 hn).trans hr.symm

theorem canonicalEvaluator_exists {σ : Type} [Ty σ] (E : Prop → Prop)
    (h : ActualEvaluator E) (F : σ → Prop) :
    canonicalEvaluator E (∃ x, F x) = (∃ x, canonicalEvaluator E (F x)) :=
  worldEvaluator_exists _ (positiveEvaluator_actualWorld E (actualEvaluator_positive E h))
    (actualEvaluator_kernel_possible E h) F

end Classicism.Research
