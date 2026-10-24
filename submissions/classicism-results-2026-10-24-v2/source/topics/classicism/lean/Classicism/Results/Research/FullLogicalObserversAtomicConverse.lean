import Classicism.Results.Research.FullLogicalObservers
import Classicism.Results.Research.CanonicalEvaluator
import Classicism.Results.Research.DiagonalCharacters

/-!
# Full logical separation implies atomicity with Actuality and ND

Direct sources: `research/2026-10-23/operator-characterizations/positive-operator-representation.txt`,
section 3; `reverse-entailment-countermodel.txt`, section 5; and
`database-combination-obstruction.txt`, section 5 (misc, original research,
23 October 2026, unpaginated).

The observer hypothesis retains identities of the full Boolean and quantifier
composites. The proof uses their pointwise consequences, not a replacement
separation premise. Only the type-t instance of quantifier preservation is
needed. The diagonal atom is constructed, not supplied as an extraction axiom.
All optional premises are local; no optional premise is necessitated.
-/

namespace Classicism.Research.FullLogicalObservers
open Classicism.P Classicism.Paper

def Normalize (B O : Prop → Prop) : Prop → Prop := fun p => B (O p)

theorem evaluator_not (B : Prop → Prop) (hB : ActualEvaluator B) (p : Prop) :
    B (¬ p) = ¬ B p := by
  apply (em p).elim
  · intro hp
    calc B (¬ p) = False := (hB (¬ p)).2 (fun hn => hn hp)
      _ = ¬ True := not_true_eq.symm
      _ = ¬ B p := congrArg Not ((hB p).1 hp).symm
  · intro hn
    calc B (¬ p) = True := (hB (¬ p)).1 hn
      _ = ¬ False := not_false_eq.symm
      _ = ¬ B p := congrArg Not ((hB p).2 hn).symm

theorem normalize_truth (B O : Prop → Prop) (hB : ActualEvaluator B) (p : Prop) :
    Normalize B O p ↔ O p :=
  (actualEvaluator_positive B hB).1 (O p)

theorem normalize_bivalent (B O : Prop → Prop) (hB : ActualEvaluator B) :
    DiagonalCharacters.Bivalent (Normalize B O) := fun p =>
  (em (O p)).elim (fun hp => Or.inl ((hB (O p)).1 hp))
    (fun hn => Or.inr ((hB (O p)).2 hn))

theorem normalize_top (B O : Prop → Prop) (hB : ActualEvaluator B)
    (hO : BoolFull O) : Normalize B O True = True :=
  (congrArg B (boolFull_top hO)).trans ((hB True).1 trivial)

theorem normalize_bot (B O : Prop → Prop) (hB : ActualEvaluator B)
    (hO : BoolFull O) : Normalize B O False = False :=
  (congrArg B (boolFull_bot hO)).trans ((hB False).2 (fun hf => hf))

theorem normalize_not (B O : Prop → Prop) (hB : ActualEvaluator B)
    (hO : BoolFull O) : DiagonalCharacters.NegationPreserving (Normalize B O) :=
  fun p => (congrArg B (boolFull_not hO p)).trans (evaluator_not B hB (O p))

theorem boolFull_imp {O : Prop → Prop} (hO : BoolFull O) (p q : Prop) :
    O (p → q) = (O p → O q) := by
  rw [imp_eq_not_or p q, boolFull_or hO, boolFull_not hO, ← imp_eq_not_or]

theorem normalize_imp (B O : Prop → Prop) (hB : ActualEvaluator B)
    (hO : BoolFull O) (p q : Prop) :
    Normalize B O (p → q) ↔ (Normalize B O p → Normalize B O q) :=
  ⟨fun h hp => (normalize_truth B O hB q).2
      (Eq.mp (boolFull_imp hO p q) ((normalize_truth B O hB (p → q)).1 h)
        ((normalize_truth B O hB p).1 hp)),
   fun h => (normalize_truth B O hB (p → q)).2
      (Eq.mpr (boolFull_imp hO p q) (fun hp => (normalize_truth B O hB q).1
        (h ((normalize_truth B O hB p).2 hp))))⟩

theorem normalize_forall (B O : Prop → Prop) (hB : ActualEvaluator B)
    (hO : QuantifierFull Prop O) (F : Prop → Prop) :
    Normalize B O (∀ p, F p) ↔ ∀ p, Normalize B O (F p) :=
  ⟨fun h p => (normalize_truth B O hB (F p)).2
      (Eq.mp (quantifierFull_forall hO F)
        ((normalize_truth B O hB (∀ p, F p)).1 h) p),
   fun h => (normalize_truth B O hB (∀ p, F p)).2
      (Eq.mpr (quantifierFull_forall hO F)
        (fun p => (normalize_truth B O hB (F p)).1 (h p)))⟩

theorem normalize_idempotent (B O : Prop → Prop) (hB : ActualEvaluator B)
    (hO : BoolFull O) (p : Prop) :
    Normalize B O (Normalize B O p) = Normalize B O p :=
  (normalize_bivalent B O hB p).elim
    (fun ht => (congrArg (Normalize B O) ht).trans
      ((normalize_top B O hB hO).trans ht.symm))
    (fun hf => (congrArg (Normalize B O) hf).trans
      ((normalize_bot B O hB hO).trans hf.symm))

/-- The quantifier law forces acceptance of the constructed diagonal kernel. -/
theorem normalize_accepts_kernel (B O : Prop → Prop) (hB : ActualEvaluator B)
    (hO : QualifiedFull Prop O) :
    Normalize B O (DiagonalCharacters.Kernel (Normalize B O)) :=
  (normalize_forall B O hB hO.2
    (fun p => Normalize B O p → p)).2 (fun p =>
      (normalize_imp B O hB hO.1 (Normalize B O p) p).2
        (fun h => Eq.mp (normalize_idempotent B O hB hO.1 p) h))

theorem normalize_diagonal (B O : Prop → Prop) (hB : ActualEvaluator B)
    (hO : QualifiedFull Prop O) : DiagonalCharacters.Diagonal (Normalize B O) :=
  ⟨normalize_bot B O hB hO.1, normalize_bivalent B O hB,
    normalize_not B O hB hO.1, normalize_accepts_kernel B O hB hO⟩

/-- Separation from bottom supplies a qualified observer accepting each nonbottom input. -/
theorem full_separation_accepting (sep : SeparationFull Prop) (p : Prop)
    (hp : p ≠ False) : ∃ O : Prop → Prop, QualifiedFull Prop O ∧ O p := by
  apply (em (∃ O : Prop → Prop, QualifiedFull Prop O ∧ O p)).elim id
  intro hn
  apply False.elim
  apply hp
  apply (sep p False).2
  intro O hO
  apply Eq.mpr (boolFull_iff hO.1 p False)
  exact ⟨fun ht => False.elim (hn ⟨O, hO, ht⟩),
    fun hf => False.elim (Eq.mp (boolFull_bot hO.1) hf)⟩

/-- The diagonal below p is an explicit witness, constructed from its separating observer. -/
theorem evaluator_full_separation_atomicity (B : Prop → Prop) (hB : ActualEvaluator B)
    (sep : SeparationFull Prop) : Atomicity Prop := by
  intro p
  apply (em (p = False)).elim
  · intro hp
    exact Or.inl (le_neg_of_eq_false p hp)
  · intro hp
    obtain ⟨O, hO, hop⟩ := full_separation_accepting sep p hp
    have hd := normalize_diagonal B O hB hO
    have hn : Normalize B O p := (normalize_truth B O hB p).2 hop
    exact Or.inr ⟨DiagonalCharacters.Kernel (Normalize B O),
      DiagonalCharacters.diagonal_atom (Normalize B O) hd,
      DiagonalCharacters.accepted_below (Normalize B O) p
        (DiagonalCharacters.bivalent_true (Normalize B O)
          (normalize_bivalent B O hB) p hn)⟩

/-- Actuality and only local ND at t supply the correct endpoint evaluator. -/
theorem nd_actuality_evaluator (nd : NecessityOfDistinctness Prop)
    (act : Actuality) : ∃ B : Prop → Prop, ActualEvaluator B :=
  act.elim fun w hw => ⟨worldEvaluator w,
    worldEvaluator_actual w hw (nd w False (dia_intro w hw.1))⟩

theorem nd_actuality_full_separation_atomicity :
    NecessityOfDistinctness Prop → Actuality → SeparationFull Prop → Atomicity Prop :=
  fun nd act sep => (nd_actuality_evaluator nd act).elim fun B hB =>
    evaluator_full_separation_atomicity B hB sep

/-- The exact converse needed for the C5 + Actuality characterization. -/
theorem c5_actuality_full_separation_atomicity :
    NecNecessityOfDistinctness Prop → Actuality → SeparationFull Prop → Atomicity Prop :=
  fun c5 => nd_actuality_full_separation_atomicity (box_elim c5)

end Classicism.Research.FullLogicalObservers
