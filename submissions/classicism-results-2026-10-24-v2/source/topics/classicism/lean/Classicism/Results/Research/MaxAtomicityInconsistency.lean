import Classicism.Results.Research.MaxAtomicityJechShelahArithmeticExistence
import Classicism.Results.Research.MaxAtomicityJechShelahConditionSemantics
import Classicism.Results.Research.MaxAtomicityJechShelahLocalFusion

/-!
# The exact pure Max(C) and unboxed Atomicity_t target

Direct source: original argument, misc, 22–23 October 2026,
research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md,
with the explicit canonical-code implementation described in
max-atomicity-canonical-code-proof.md. The underlying rigid forcing is
Jech–Shelah, Journal of Algebra 182 (1996), pp. 749–754.

This source assembles actual constructions; it accepts no rigidity, coding,
soundness, selector, or inconsistency premise. Its verification status is
determined by the serial compiler manifest, not by the presence of this file.
-/

namespace Classicism.Meta.Research.MaxAtomicityInconsistency

open BooleanValued
open MaxAtomicityJechShelahTrees MaxAtomicityJechShelahCylinders
open MaxAtomicityJechShelahIndexedGenerators
open MaxAtomicityJechShelahSyntax MaxAtomicityPureSelector
open MaxAtomicityJechShelahConditionSemantics
open MaxAtomicityJechShelahArithmeticExistence
open MaxAtomicityConcreteModel MaxAtomicitySplitCertificate

noncomputable section

theorem canonical_adequacy : Adequate JSCode indexedGenerator :=
  MaxAtomicitySelectorTransport.adequate_of_canonical JSCode canonical_sound
    (canonical_exists_of_arithmetic canonical_arithmetic_exists)

/-- A literal closed pure term in the original relational language. -/
def F : Term Signature.pure [] SplitterTy := selector JSCode

theorem F_closedTypes : F.closedTypes = true := selector_closedTypes JSCode

theorem F_pure : F.pure = true := selector_pure JSCode

theorem F_splits {p : B} (hp : p ≠ ⊥) :
    p ⊓ eval interpretation F .nil p ≠ ⊥ ∧
      p ⊓ (eval interpretation F .nil p)ᶜ ≠ ⊥ :=
  eval_selector_splits interpretation JSCode indexedGenerator canonical_adequacy
    MaxAtomicityJechShelahLocalFusion.actual_rigid
    indexedGenerator_completely_generates (fun _ h => forcing_completion_atomless h) hp

/-- The reference theory here is exactly bare C. -/
theorem split_identity_not_C_theorem :
    ¬ C.Theorem (Term.eq' (split F) Term.bot) :=
  MaxAtomicitySplitSemantics.split_identity_not_C_theorem interpretation F
    (fun _ hp => F_splits hp)

/-- The exact target: no added L axiom, enriched signature, boxed Atomicity,
or supplied construction certificate occurs as a premise. -/
theorem maximalism_atomicity_inconsistent :
    ¬ AxiomSet.Consistent (AxiomSet.maximalist ∪ P.AtomicityT.schema) :=
  inconsistent_of_split_not_zero_theorem F F_closedTypes split_identity_not_C_theorem

#check maximalism_atomicity_inconsistent
#print axioms canonical_adequacy
#print axioms F_closedTypes
#print axioms F_pure
#print axioms F_splits
#print axioms split_identity_not_C_theorem
#print axioms maximalism_atomicity_inconsistent

end

end Classicism.Meta.Research.MaxAtomicityInconsistency
