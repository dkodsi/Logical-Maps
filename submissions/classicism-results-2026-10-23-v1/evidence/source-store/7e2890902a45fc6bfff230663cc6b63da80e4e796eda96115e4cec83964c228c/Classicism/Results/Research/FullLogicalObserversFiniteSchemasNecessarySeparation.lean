import Classicism.Results.Research.FullLogicalObserversFiniteSchemasNecessaryQualifiedAtoms
import Classicism.Results.Research.FullLogicalObserversFiniteSchemasNecessarySeparationRule

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before atomicity_necessary_full_finite"
  err.flush : IO Unit)

set_option maxHeartbeats 2000000 in
theorem atomicity_necessary_full_finite {Ax : AxiomSet Signature.pure}
    (hc5 : Theorem (C.axioms ∪ Ax) C5Condition.term)
    (hat : Theorem (C.axioms ∪ Ax) AtomicCondition.term) (Δ : List Ty) :
    Theorem (C.axioms ∪ Ax) (necessarySeparation Δ) := by
  have hr : Theorem (C.axioms ∪ Ax)
      (Term.imp C5Condition.term (Term.imp AtomicCondition.term
        (Term.imp (Term.box (qualifiedAtoms Δ)) (necessarySeparation Δ)))) :=
    necessary_finite_separation_rule (qualification Δ)
  exact Theorem.mp (Theorem.mp₂ hr hc5 hat) (necessarily_qualified_atoms hc5 Δ)

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: NecessarySeparation complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
