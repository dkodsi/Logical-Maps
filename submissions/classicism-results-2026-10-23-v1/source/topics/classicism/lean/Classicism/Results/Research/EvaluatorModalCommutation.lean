import Classicism.Results.Research.Evaluator
import Classicism.Results.Records.Extensionality

/-!
# The modal boundary of actual truth evaluators

Direct source: `research/2026-10-22/notes/gallin-bivalent-evaluator.md`,
section 9, Proposition 8 (misc, unpaginated original research).
Formalization: 23 October 2026.

Both commutation laws below are unboxed and pointwise. The evaluator satisfies
only the existing ActualEvaluator condition. No global output-bivalence,
Choice, Infinity, or Barcan premise is added. The final schema module retains
Extensionality at every relational type, including the nullary type t.
-/

namespace Classicism.Research.EvaluatorModalCommutation
open Classicism.Paper Classicism.P

def HasBoxCommutingEvaluator : Prop :=
  ∃ E : Prop → Prop, ActualEvaluator E ∧ ∀ p : Prop, E (□ p) = □ (E p)

def HasDiamondCommutingEvaluator : Prop :=
  ∃ E : Prop → Prop, ActualEvaluator E ∧ ∀ p : Prop, E (◇ p) = ◇ (E p)

/-- Correctness plus box commutation makes every current truth necessary. -/
theorem box_evaluator_modal_collapse (E : Prop → Prop) (hE : ActualEvaluator E)
    (hcomm : ∀ p : Prop, E (□ p) = □ (E p)) : ∀ p : Prop, p → □ p :=
  fun p hp => ((actualEvaluator_positive E hE).1 (□ p)).1
    ((hcomm p).mpr ((hE p).1 hp))

theorem box_evaluator_fregean : HasBoxCommutingEvaluator → FregeanAxiom :=
  fun h => h.elim fun E hE => fun p q hpq =>
    modalized_fregean p q (box_evaluator_modal_collapse E hE.1 hE.2 (p ↔ q) hpq)

/-- Under the Fregean Axiom, the identity operation is an actual evaluator. -/
theorem fregean_identity_evaluator (h : FregeanAxiom) :
    ActualEvaluator (fun p : Prop => p) :=
  fun p => ⟨fun hp => h p True ⟨fun _ => trivial, fun _ => hp⟩,
    fun hn => h p False ⟨hn, False.elim⟩⟩

theorem fregean_box_evaluator : FregeanAxiom → HasBoxCommutingEvaluator :=
  fun h => ⟨fun p => p, fregean_identity_evaluator h, fun _ => rfl⟩

theorem box_evaluator_iff_fregean : HasBoxCommutingEvaluator ↔ FregeanAxiom :=
  ⟨box_evaluator_fregean, fregean_box_evaluator⟩

/-- The all-relational-type bridge uses the existing C proof of Intensionality. -/
theorem box_evaluator_extensionality {τ : Type} [Rel τ] :
    HasBoxCommutingEvaluator → Extensionality τ :=
  fun h => Proofs.fregean_axiom_implies_extensionality_r (box_evaluator_fregean h)

/-- Only Extensionality's nullary instance is needed for the converse. -/
theorem extensionality_box_evaluator : Extensionality Prop → HasBoxCommutingEvaluator :=
  fun h => fregean_box_evaluator (Proofs.extensionality_r_implies_fregean_axiom h)

/-- Diamond commutation makes every current possibility true. -/
theorem diamond_evaluator_possibility_elim (E : Prop → Prop) (hE : ActualEvaluator E)
    (hcomm : ∀ p : Prop, E (◇ p) = ◇ (E p)) : ∀ p : Prop, ◇ p → p := by
  intro p hp
  have hEp : ◇ (E p) :=
    (hcomm p).mp (((actualEvaluator_positive E hE).1 (◇ p)).2 hp)
  exact (em p).elim (fun h => h) (fun hn => False.elim (hEp ((hE p).2 hn)))

/-- Apply possibility elimination to the negation to recover box collapse. -/
theorem diamond_evaluator_modal_collapse (E : Prop → Prop) (hE : ActualEvaluator E)
    (hcomm : ∀ p : Prop, E (◇ p) = ◇ (E p)) : ∀ p : Prop, p → □ p :=
  fun p hp => (em (□ p)).elim (fun h => h) (fun hn => False.elim
    (diamond_evaluator_possibility_elim E hE hcomm (¬ p) (dia_not_of_not_box p hn) hp))

theorem diamond_evaluator_fregean : HasDiamondCommutingEvaluator → FregeanAxiom :=
  fun h => h.elim fun E hE => fun p q hpq =>
    modalized_fregean p q (diamond_evaluator_modal_collapse E hE.1 hE.2 (p ↔ q) hpq)

theorem fregean_diamond_evaluator : FregeanAxiom → HasDiamondCommutingEvaluator :=
  fun h => ⟨fun p => p, fregean_identity_evaluator h, fun _ => rfl⟩

theorem diamond_evaluator_iff_fregean : HasDiamondCommutingEvaluator ↔ FregeanAxiom :=
  ⟨diamond_evaluator_fregean, fregean_diamond_evaluator⟩

theorem diamond_evaluator_extensionality {τ : Type} [Rel τ] :
    HasDiamondCommutingEvaluator → Extensionality τ :=
  fun h => Proofs.fregean_axiom_implies_extensionality_r (diamond_evaluator_fregean h)

theorem extensionality_diamond_evaluator :
    Extensionality Prop → HasDiamondCommutingEvaluator :=
  fun h => fregean_diamond_evaluator (Proofs.extensionality_r_implies_fregean_axiom h)

end Classicism.Research.EvaluatorModalCommutation
