import Classicism.Results.Research.FullLogicalObserversFiniteSchemasCurrentSeparation
import Classicism.Results.Research.FullLogicalObserversFiniteSchemasNecessarySeparation
import Classicism.Results.Research.FullLogicalObserversFiniteSchemasCurrentConverse
import Classicism.Results.Research.FullLogicalObserversFiniteSchemasNecessaryConverse

set_option Elab.async false
set_option stderrAsMessages false

/-!
# Simultaneous full logical separation: assembly and principal axiom audit

The definitions and six expensive proof declarations are factored into dependency
modules so the serial checker can cache each completed theorem. Namespace names,
statements, proof bodies, and the original eight principal reports are preserved.
-/

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before forward schema assembly"
  err.flush : IO Unit)

theorem c5_atomicity_entails_full_finite :
    (single C5Condition.term ∪ single AtomicCondition.term) ⟹ FullFiniteSchema := by
  rintro p ⟨Δ, _hc, rfl⟩
  exact atomicity_full_finite (Theorem.ax (Or.inl rfl))
    (Theorem.ax (Or.inr rfl)) Δ

theorem c5_atomicity_entails_necessary_full_finite :
    (single C5Condition.term ∪ single AtomicCondition.term) ⟹
      NecessaryFullFiniteSchema := by
  rintro p ⟨Δ, _hc, rfl⟩
  exact atomicity_necessary_full_finite (Theorem.ax (Or.inl rfl))
    (Theorem.ax (Or.inr rfl)) Δ

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before schema interderivability"
  err.flush : IO Unit)

/-- The current and necessary finite schemas are interderivable over C5 + Actuality. -/
theorem full_finite_entails_necessary :
    (Background ∪ FullFiniteSchema) ⟹ NecessaryFullFiniteSchema := by
  rintro p ⟨Δ, _hc, rfl⟩
  exact atomicity_necessary_full_finite (Theorem.ax (Or.inl (Or.inl rfl)))
    (full_finite_entails_atomicity AtomicCondition.term rfl) Δ

theorem necessary_full_finite_entails_current :
    (Background ∪ NecessaryFullFiniteSchema) ⟹ FullFiniteSchema := by
  rintro p ⟨Δ, _hc, rfl⟩
  exact atomicity_full_finite (Theorem.ax (Or.inl (Or.inl rfl)))
    (necessary_full_finite_entails_atomicity AtomicCondition.term rfl) Δ

#print axioms qualified_atoms
#print axioms necessarily_qualified_atoms
#print axioms c5_atomicity_entails_full_finite
#print axioms c5_atomicity_entails_necessary_full_finite
#print axioms full_finite_entails_atomicity
#print axioms necessary_full_finite_entails_atomicity
#print axioms full_finite_entails_necessary
#print axioms necessary_full_finite_entails_current

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
