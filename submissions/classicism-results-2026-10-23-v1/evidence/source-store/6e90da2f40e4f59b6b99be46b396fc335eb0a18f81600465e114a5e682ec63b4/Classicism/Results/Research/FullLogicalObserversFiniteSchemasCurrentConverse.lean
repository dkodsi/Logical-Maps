import Classicism.Results.Research.FullLogicalObserversFiniteSchemasBase

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before full_finite_entails_atomicity"
  err.flush : IO Unit)

theorem full_finite_entails_atomicity :
    (Background ∪ FullFiniteSchema) ⟹ single AtomicCondition.term := by
  rintro p rfl
  have hr : Theorem (C.axioms ∪ (Background ∪ FullFiniteSchema))
      (Term.imp C5Condition.term (Term.imp ActualCondition.term
        (Term.imp (separation [.rel .t]) AtomicCondition.term))) :=
    Derivable.conv (Theorem.ofCMinus c5_actuality_singleton_atomicity.derivable)
      (Conv.of_nf 4 _ _ rfl)
  exact Theorem.mp
    (Theorem.mp₂ hr (Theorem.ax (Or.inl (Or.inl rfl)))
      (Theorem.ax (Or.inl (Or.inr rfl))))
    (Theorem.ax (Or.inr ⟨[.rel .t], by decide, rfl⟩))

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: CurrentConverse complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
