import Classicism.Results.Research.FullLogicalObserversFiniteSchemasBase

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before necessary_full_finite_entails_atomicity"
  err.flush : IO Unit)

theorem necessary_full_finite_entails_atomicity :
    (Background ∪ NecessaryFullFiniteSchema) ⟹ single AtomicCondition.term := by
  rintro p rfl
  have hr : Theorem (C.axioms ∪ (Background ∪ NecessaryFullFiniteSchema))
      (Term.imp C5Condition.term (Term.imp ActualCondition.term
        (Term.imp (necessarySeparation [.rel .t]) AtomicCondition.term))) :=
    Derivable.conv
      (Theorem.ofCMinus c5_actuality_necessary_singleton_atomicity.derivable)
      (Conv.of_nf 4 _ _ rfl)
  exact Theorem.mp
    (Theorem.mp₂ hr (Theorem.ax (Or.inl (Or.inl rfl)))
      (Theorem.ax (Or.inl (Or.inr rfl))))
    (Theorem.ax (Or.inr ⟨[.rel .t], by decide, rfl⟩))

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: NecessaryConverse complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
