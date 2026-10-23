import Classicism.Results.Research.ActualityCore

/-!
# The canonical current truth-sort bridge

Direct source: `research/2026-10-22/notes/gallin-extensional-core.md`, §8,
and `notes/actuality-world-slice-core.md`, §3 (original research, `misc`,
22 October 2026, unpaginated).

This is the nullary base of the local/Gallin comparison. Its hypothesis is
the existing `ActualEvaluator` predicate, weaker than a globally bivalent
Gallin evaluator. Existence and normalization of evaluators belong to the
core worker; this file only proves the current inverse maps on truth objects.
Higher-type inverse maps and a recursive syntax interpretation are not claimed.
-/

namespace Classicism.Research.ActualityCore
open Classicism.Paper Classicism.P

def Endpoint (q : Prop) : Prop := q = True ∨ q = False

theorem supported_truth_values (w : Prop) (hw : ActualWorld w) (p : Prop)
    (hp : Supported w p) : p = w ∨ p = False :=
  have he : Truth w p = p := cut_fixed w p hp
  (truth_values w hw p).elim (fun h => Or.inl (he.symm.trans h))
    (fun h => Or.inr (he.symm.trans h))

theorem evaluator_endpoint (E : Prop → Prop) (hE : Research.ActualEvaluator E) (p : Prop) :
    Endpoint (E p) :=
  (em p).elim (fun hp => Or.inl ((hE p).1 hp)) (fun hn => Or.inr ((hE p).2 hn))

/-- Backward after forward is literal identity on the local truth domain. -/
theorem truth_bridge_left (w : Prop) (hw : ActualWorld w)
    (E : Prop → Prop) (hE : Research.ActualEvaluator E)
    (p : Prop) (hp : Supported w p) : Truth w (E p) = p :=
  localized_eq w hw _ _ (truth_supported w (E p)) hp
    ⟨fun h => ((Research.actualEvaluator_positive E hE).1 p).1 h.2,
      fun h => ⟨hw.1, ((Research.actualEvaluator_positive E hE).1 p).2 h⟩⟩

/-- Forward after backward is literal identity on the endpoint truth domain. -/
theorem truth_bridge_right (w : Prop) (hw : ActualWorld w)
    (E : Prop → Prop) (hE : Research.ActualEvaluator E)
    (q : Prop) (hq : Endpoint q) : E (Truth w q) = q := by
  apply hq.elim
  · intro ht
    exact (congrArg (fun r : Prop => E (Truth w r)) ht).trans
      (((hE (Truth w True)).1 ⟨hw.1, trivial⟩).trans ht.symm)
  · intro hf
    exact (congrArg (fun r : Prop => E (Truth w r)) hf).trans
      (((hE (Truth w False)).2 (fun h => h.2)).trans hf.symm)

theorem truth_bridge_injective (w : Prop) (hw : ActualWorld w)
    (E : Prop → Prop) (hE : Research.ActualEvaluator E)
    (p q : Prop) (hp : Supported w p) (hq : Supported w q) (he : E p = E q) : p = q :=
  (truth_bridge_left w hw E hE p hp).symm.trans
    ((congrArg (Truth w) he).trans (truth_bridge_left w hw E hE q hq))

theorem endpoint_bridge_injective (w : Prop) (hw : ActualWorld w)
    (E : Prop → Prop) (hE : Research.ActualEvaluator E)
    (p q : Prop) (hp : Endpoint p) (hq : Endpoint q) (he : Truth w p = Truth w q) : p = q :=
  (truth_bridge_right w hw E hE p hp).symm.trans
    ((congrArg E he).trans (truth_bridge_right w hw E hE q hq))

theorem truth_bridge_endpoints (w : Prop) (hw : ActualWorld w)
    (E : Prop → Prop) (hE : Research.ActualEvaluator E) :
    E w = True ∧ E False = False ∧ Truth w True = w ∧ Truth w False = False :=
  ⟨(hE w).1 hw.1, (hE False).2 (fun h => h), truth_true w, truth_false w⟩

/-- The already checked actual-world kernel supplies the canonical parameter.
There is no choice of a world in this construction. -/
theorem canonical_truth_bridge (E : Prop → Prop) (hE : Research.ActualEvaluator E) :
    (∀ p : Prop, Supported (Research.truthKernel E) p →
      Truth (Research.truthKernel E) (E p) = p) ∧
    (∀ q : Prop, Endpoint q → E (Truth (Research.truthKernel E) q) = q) :=
  have hw := Research.positiveEvaluator_actualWorld E (Research.actualEvaluator_positive E hE)
  ⟨fun p hp => truth_bridge_left _ hw E hE p hp,
    fun q hq => truth_bridge_right _ hw E hE q hq⟩

end Classicism.Research.ActualityCore
