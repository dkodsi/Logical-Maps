import Classicism.Results.Records.Lattice

/-!
# Actual-truth kernels

Direct source: `research/2026-10-22/notes/uniform-half-comprehension-definitions.md`,
converse argument; `proof-refinements/canonical-actual-evaluator.md`, §§1–2
(unpaginated original research, `misc`, 22 October 2026).

These are shallow proofs. The separate certificate module checks the gate and the
relational types and translates them into object-language C derivations.
-/

namespace Classicism.Research
open Classicism.Paper Classicism.P

/-- Only current agreement and persistence of current true outputs are required. -/
def PositiveEvaluator (T : Prop → Prop) : Prop :=
  (∀ p : Prop, T p ↔ p) ∧ ∀ p : Prop, p → □ (T p)

def HasPositiveEvaluator : Prop := ∃ T : Prop → Prop, PositiveEvaluator T

/-- This kernel uses one implication; no universal is moved through a box. -/
def truthKernel (T : Prop → Prop) : Prop := ∀ p : Prop, T p → p

theorem truthKernel_instance (T : Prop → Prop) (q : Prop) :
    T q → truthKernel T → q := fun h hw => hw q h

theorem positiveEvaluator_actualWorld (T : Prop → Prop) (h : PositiveEvaluator T) :
    ActualWorld (truthKernel T) :=
  ⟨fun p hp => (h.1 p).1 hp, fun q hq =>
    le_of_box_incl (modal_K _ _ (nec% (truthKernel_instance T q)) (h.2 q hq))⟩

theorem positiveEvaluator_actuality : HasPositiveEvaluator → Actuality :=
  fun h => h.elim fun T hT => ⟨truthKernel T, positiveEvaluator_actualWorld T hT⟩

theorem actualWorld_positiveEvaluator (w : Prop) (hw : ActualWorld w) :
    PositiveEvaluator (fun p : Prop => □ (w → p)) :=
  ⟨fun p => ⟨fun h => box_elim h hw.1, fun hp => (le_iff_prop w p).1 (hw.2 p hp)⟩,
   fun p hp => modal_four _ ((le_iff_prop w p).1 (hw.2 p hp))⟩

theorem actuality_positiveEvaluator : Actuality → HasPositiveEvaluator :=
  fun h => h.elim fun w hw => ⟨_, actualWorld_positiveEvaluator w hw⟩

theorem actuality_iff_positiveEvaluator : Actuality ↔ HasPositiveEvaluator :=
  ⟨actuality_positiveEvaluator, positiveEvaluator_actuality⟩

/-- Full current top/bottom evaluation, stronger than the positive evaluator. -/
def ActualEvaluator (E : Prop → Prop) : Prop :=
  ∀ p : Prop, (p → E p = True) ∧ (¬ p → E p = False)

theorem actualEvaluator_positive (E : Prop → Prop) (h : ActualEvaluator E) :
    PositiveEvaluator E := by
  refine ⟨?_, fun p hp => (h p).1 hp⟩
  intro p
  refine ⟨?_, fun hp => box_elim ((h p).1 hp)⟩
  intro hEp
  exact (em p).elim (fun hp => hp) (fun hn => False.elim (((h p).2 hn) ▸ hEp))

/-- Actual-world witnesses are literally equal, by antisymmetry. -/
theorem actualWorld_unique (w v : Prop) (hw : ActualWorld w) (hv : ActualWorld v) :
    w = v := le_antisymm_rel w v (hw.2 v hv.1) (hv.2 w hw.1)

/-- Actuality's atom-local Barcan law, at each fixed type, with an unboxed `F`. -/
theorem actualWorld_all {σ : Type} [Ty σ] (w : Prop) (hw : ActualWorld w)
    (F : σ → Prop) (h : ∀ x : σ, w ≤ F x) : w ≤ (∀ x : σ, F x) :=
  hw.2 _ (fun x => box_elim ((le_iff_prop w (F x)).1 (h x)) hw.1)

end Classicism.Research
