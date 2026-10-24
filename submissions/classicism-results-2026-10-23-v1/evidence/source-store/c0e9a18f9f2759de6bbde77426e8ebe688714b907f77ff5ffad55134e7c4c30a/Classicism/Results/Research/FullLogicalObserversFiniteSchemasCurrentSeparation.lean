import Classicism.Results.Research.FullLogicalObserversFiniteSchemasQualifiedAtoms
import Classicism.Results.Research.FullLogicalObserversFiniteSchemasSeparationRule

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before atomicity_full_finite"
  err.flush : IO Unit)

set_option maxHeartbeats 2000000 in
/-- A proof at every finite list, using one witness for all listed types. -/
theorem atomicity_full_finite {Ax : AxiomSet Signature.pure}
    (hc5 : Theorem (C.axioms ∪ Ax) C5Condition.term)
    (hat : Theorem (C.axioms ∪ Ax) AtomicCondition.term) (Δ : List Ty) :
    Theorem (C.axioms ∪ Ax) (separation Δ) := by
  have hr : Theorem (C.axioms ∪ Ax)
      (Term.imp AtomicCondition.term (Term.imp (qualifiedAtoms Δ) (separation Δ))) :=
    finite_separation_rule (qualification Δ)
  exact Theorem.mp₂ hr hat (qualified_atoms hc5 Δ)

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: CurrentSeparation complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
