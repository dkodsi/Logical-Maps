import Classicism.Results.Research.EvaluatorModalCommutationCertificates
import Classicism.Certified.Signatures

/-!
# Exact evaluator/Extensionality equivalences over C

Direct source: `research/2026-10-22/notes/gallin-bivalent-evaluator.md`,
section 9, Proposition 8 (misc, unpaginated original research).

The existence claims are single sentences with unboxed pointwise commutation.
Extensionality is its full schema at every closed relational type, including t.
The type quantification below is metalinguistic. Pure derivations transport to
any signature; no optional assumption is added to the fixed C background.
-/

namespace Classicism.Meta.Research.EvaluatorModalCommutation
open AxiomSet Classicism.Research.EvaluatorModalCommutation

theorem box_evaluator_iff_extensionality (Ax : AxiomSet Signature.pure) :
    (Ax ⟹ HasBoxCommutingEvaluator.schema) ↔ (Ax ⟹ P.Extensionality.schema) :=
  ⟨fun h => Entails.trans h box_evaluator_extensionality.entails,
   fun h => Entails.trans h extensionality_box_evaluator.entails⟩

theorem diamond_evaluator_iff_extensionality (Ax : AxiomSet Signature.pure) :
    (Ax ⟹ HasDiamondCommutingEvaluator.schema) ↔ (Ax ⟹ P.Extensionality.schema) :=
  ⟨fun h => Entails.trans h diamond_evaluator_extensionality.entails,
   fun h => Entails.trans h extensionality_diamond_evaluator.entails⟩

private theorem transport {Sig : Signature} {A B : AxiomSet Signature.pure}
    (h : A ⟹ B) : AxiomSet.ofPure (Sig := Sig) A ⟹ AxiomSet.ofPure B := by
  rintro a ⟨p, hp, rfl⟩
  exact Derivable.mono (ofPure_union_subset A) (Theorem.ofPure (h p hp))

abbrev HasBoxCommutingEvaluatorIn {Sig : Signature} : AxiomSet Sig :=
  AxiomSet.ofPure HasBoxCommutingEvaluator.schema

abbrev HasDiamondCommutingEvaluatorIn {Sig : Signature} : AxiomSet Sig :=
  AxiomSet.ofPure HasDiamondCommutingEvaluator.schema

/-- The box statement, at any signature and relative to any axiom set. -/
theorem box_evaluator_iff_extensionality_in {Sig : Signature} (Ax : AxiomSet Sig) :
    (Ax ⟹ HasBoxCommutingEvaluatorIn) ↔ (Ax ⟹ P.Extensionality.schemaIn) :=
  ⟨fun h => Entails.trans h (transport box_evaluator_extensionality.entails),
   fun h => Entails.trans h (transport extensionality_box_evaluator.entails)⟩

/-- The diamond statement, with exactly the same evaluator and modal scope. -/
theorem diamond_evaluator_iff_extensionality_in {Sig : Signature} (Ax : AxiomSet Sig) :
    (Ax ⟹ HasDiamondCommutingEvaluatorIn) ↔ (Ax ⟹ P.Extensionality.schemaIn) :=
  ⟨fun h => Entails.trans h (transport diamond_evaluator_extensionality.entails),
   fun h => Entails.trans h (transport extensionality_diamond_evaluator.entails)⟩

end Classicism.Meta.Research.EvaluatorModalCommutation

#print axioms Classicism.Meta.Research.EvaluatorModalCommutation.box_evaluator_iff_extensionality
#print axioms Classicism.Meta.Research.EvaluatorModalCommutation.diamond_evaluator_iff_extensionality
#print axioms Classicism.Meta.Research.EvaluatorModalCommutation.box_evaluator_iff_extensionality_in
#print axioms Classicism.Meta.Research.EvaluatorModalCommutation.diamond_evaluator_iff_extensionality_in
