import Classicism.Results.Research.ModalFiniteDefinitions
import Classicism.Results.Research.ModalComprehensionClassicalExtension

/-!
# Finite dependent naming over the stated classical base

Original research, misc, 23 October 2026. The open DNE schema and type-e
existence schema are exactly equivalent, in actual derivability, to the
closed theory consisting of universal DNE and closed type-e existence.
This puts the stated classical base within the finite-definition theorem's
closed-global-theory scope. Optional hypotheses remain local throughout.
-/

namespace Classicism.Research.ModalFreshConstantSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax

variable {C : Ty → Type}

/-- Universal closure of the sole propositional classical schema. -/
def closedDNE (C : Ty → Type) : Term C [] Ty.t :=
  .all (.imp (neg (neg (.var .zero))) (.var .zero))

def closedExistenceE (C : Ty → Type) : Term C [] Ty.t :=
  .ex (.eq (.var (.zero : Var [Ty.e] Ty.e)) (.var .zero))

/-- Exactly two closed global axioms, with no extra modal principles. -/
inductive ClosedClassicalTheory (C : Ty → Type) : ClosedTheory C
  | dne : ClosedClassicalTheory C (closedDNE C)
  | existence_e : ClosedClassicalTheory C (closedExistenceE C)

theorem closedDNE_at (Γ : Ctx) :
    closedAt (closedDNE C) Γ =
      .all (.imp (neg (neg (.var .zero))) (.var .zero)) := rfl

theorem closedExistenceE_at (Γ : Ctx) :
    closedAt (closedExistenceE C) Γ =
      .ex (.eq (.var (.zero : Var (Ty.e :: Γ) Ty.e)) (.var .zero)) := rfl

/-- UI supplies every open DNE instance; existence is already closed. -/
theorem classical_axiom_from_closed {Γ p} (h : ClassicalAxioms C Γ p) :
    Derives C (theoryAx (ClosedClassicalTheory C)) Γ [] p := by
  cases h with
  | dne p =>
      have hu : Derives C (theoryAx (ClosedClassicalTheory C)) Γ []
          (.all (.imp (neg (neg (.var .zero))) (.var .zero))) := by
        rw [← closedDNE_at]
        exact .ax ⟨closedDNE C, .dne, rfl⟩
      exact .allE p hu
  | exists_e =>
      rw [← closedExistenceE_at]
      exact .ax ⟨closedExistenceE C, .existence_e, rfl⟩

/-- Gen closes the open DNE axiom. It is applied with no local hypotheses. -/
theorem closed_classical_axiom_from_open {Γ p}
    (h : theoryAx (ClosedClassicalTheory C) Γ p) :
    Derives C (ClassicalAxioms C) Γ [] p := by
  rcases h with ⟨q, hq, rfl⟩
  cases hq with
  | dne =>
      rw [closedDNE_at]
      exact .allI (.ax (.dne (.var .zero)))
  | existence_e =>
      rw [closedExistenceE_at]
      exact .ax .exists_e

/-- Actual replacement of global axiom instances by their closed-hypothesis
proofs. In particular Nec never receives a proof with new local premises. -/
theorem replace_global_axioms {Ax Ay : Axioms C}
    (axiomMap : ∀ Γ p, Ax Γ p → Derives C Ay Γ [] p)
    {Γ Δ p} (proof : Derives C Ax Γ Δ p) : Derives C Ay Γ Δ p := by
  induction proof with
  | hyp h => exact .hyp h
  | ax h => exact (axiomMap _ _ h).lift
  | weaken h _ ih => exact .weaken h ih
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | iffI _ _ ih₁ ih₂ => exact .iffI ih₁ ih₂
  | iffE₁ _ _ ih₁ ih₂ => exact .iffE₁ ih₁ ih₂
  | iffE₂ _ _ ih₁ ih₂ => exact .iffE₂ ih₁ ih₂
  | topI => exact .topI
  | eqRefl a => exact .eqRefl a
  | eqSymm _ ih => exact .eqSymm ih
  | eqTrans _ _ ih₁ ih₂ => exact .eqTrans ih₁ ih₂
  | eqApp _ _ ih₁ ih₂ => exact .eqApp ih₁ ih₂
  | eqRight a _ ih => exact .eqRight a ih
  | eqTruth _ _ ih₁ ih₂ => exact .eqTruth ih₁ ih₂
  | eqSubst P a b _ _ ih₁ ih₂ => exact .eqSubst P a b ih₁ ih₂
  | allI _ ih => exact .allI ih
  | allE a _ ih => exact .allE a ih
  | exI a _ ih => exact .exI a ih
  | exE _ _ ih₁ ih₂ => exact .exE ih₁ ih₂
  | nec _ ih => exact .nec ih
  | K _ _ ih₁ ih₂ => exact .K ih₁ ih₂
  | intensionality ρ a b _ ih => exact .intensionality ρ a b ih
  | comprehension A => exact .comprehension A

/-- Exact equivalence at every variable context and list of local premises. -/
theorem classical_closed_derivability_iff {Γ Δ p} :
    Derives C (ClassicalAxioms C) Γ Δ p ↔
      Derives C (theoryAx (ClosedClassicalTheory C)) Γ Δ p :=
  ⟨replace_global_axioms (fun _ _ h => classical_axiom_from_closed h),
    replace_global_axioms (fun _ _ h => closed_classical_axiom_from_open h)⟩

/-- Finite dependent representative definitions are conservative over the
original, openly stated classical base. The final conclusion uses exactly
ClassicalAxioms, not a strengthened initial theory. -/
theorem finite_classical_representation_names_conservative {D U}
    (tower : DefinitionTower C (ClosedClassicalTheory C) D U)
    {Δ : List (Term C [] Ty.t)} {P : Term C [] Ty.t}
    (proof : Derives D (theoryAx U) [] (Δ.map tower.embed) (tower.embed P)) :
    Derives C (ClassicalAxioms C) [] Δ P :=
  classical_closed_derivability_iff.mpr (tower.conservative proof)

#print axioms classical_axiom_from_closed
#print axioms closed_classical_axiom_from_open
#print axioms replace_global_axioms
#print axioms classical_closed_derivability_iff
#print axioms finite_classical_representation_names_conservative

end Classicism.Research.ModalFreshConstantSyntax
