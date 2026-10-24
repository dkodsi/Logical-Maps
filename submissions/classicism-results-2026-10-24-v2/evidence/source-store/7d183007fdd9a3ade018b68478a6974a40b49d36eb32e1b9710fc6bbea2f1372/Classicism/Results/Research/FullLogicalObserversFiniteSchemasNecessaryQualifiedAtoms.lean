import Classicism.Results.Research.FullLogicalObserversFiniteSchemasNecessaryConsRule

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before necessarily_qualified_atoms"
  err.flush : IO Unit)

set_option maxHeartbeats 2000000 in
theorem necessarily_qualified_atoms {Ax : AxiomSet Signature.pure}
    (hc5 : Theorem (C.axioms ∪ Ax) C5Condition.term) :
    ∀ Δ : List Ty, Theorem (C.axioms ∪ Ax) (Term.box (qualifiedAtoms Δ))
  | [] => by
      have h := Theorem.mp (Theorem.ofCMinus c5_necessary_qualified_nil.derivable) hc5
      exact Derivable.conv h (Conv.of_nf 4 _ _ rfl)
  | σ :: Δ => by
      have hr : Theorem (C.axioms ∪ Ax)
          (Term.imp C5Condition.term
            (Term.imp (Term.box (qualifiedAtoms Δ))
              (Term.box (qualifiedAtoms (σ :: Δ))))) :=
        qualified_necessary_cons_rule σ (qualification Δ)
      exact Theorem.mp₂ hr hc5 (necessarily_qualified_atoms hc5 Δ)

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: NecessaryQualifiedAtoms complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
