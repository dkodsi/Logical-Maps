import StrongPossibilityConsequencesStability
import Classicism.Syntax.StrongPossibility
import Classicism.Syntax.Pure
import Classicism.Syntax.ClosedTypes

/-!
# SP at the exact finitary sentence-schema level

These are metalogical proofs about the existing syntax and derivability relation.
Object-language steps use the generated C certificates from the two preceding
modules. No new semantic completeness or model-existence axiom is introduced.

`reflectingMaxConsistent` is deliberately defined by a C derivation of
`D p -> p`, not by an unformalized syntactic claim about all universal formulas.
The equivalence with SP is exact for this definition. The monism corollaries
retain `Consistent (Max + E1)` as an explicit dependency.
Pending serial compilation by the designated build owner.
-/

namespace Classicism.Meta.Research.StrongPossibilityConsequences

open AxiomSet
open Classicism.Research.StrongPossibilityConsequences

variable {Sig : Signature}

theorem diaNe_closedTypes {Γ : Ctx} (p : Formula Sig Γ) :
    (Term.diaNe p).closedTypes = p.closedTypes := by
  simp [Term.diaNe, Term.weaken, Term.closedTypes_rename]

theorem strongPossibility_mem {p : Sentence Sig} (hc : p.closedTypes = true)
    (hcon : Consistent (maximalist ∪ single p)) :
    strongPossibility Sig (Term.diaNe p) :=
  ⟨by rw [diaNe_closedTypes]; exact hc, p, hcon, rfl⟩

theorem strongPossibility_at {p : Sentence Sig} (hc : p.closedTypes = true)
    (hcon : Consistent (maximalist ∪ single p)) :
    Theorem (C.axioms ∪ strongPossibility Sig) (Term.diaNe p) :=
  Theorem.ax (strongPossibility_mem hc hcon)

private theorem cMinus_to_c {p : Sentence Sig} (h : C.TheoremMinus p) : C.Theorem p :=
  Derivable.mono (fun _ ha => ha.elim) h

theorem c_diaNe_intro (p : Sentence Sig) : C.Theorem (Term.imp p (Term.diaNe p)) :=
  cMinus_to_c (Derivable.allEβ
    (C.TheoremMinus.ofPure
      Classicism.Research.StrongPossibilityConsequences.diaNe_intro.derivable) p)

theorem c_diaNe_idempotent (p : Sentence Sig) :
    C.Theorem (Term.imp (Term.diaNe (Term.diaNe p)) (Term.diaNe p)) := by
  apply cMinus_to_c
  have h := Derivable.allEβ
    (C.TheoremMinus.ofPure
      Classicism.Research.StrongPossibilityConsequences.diaNe_idempotent.derivable) p
  exact Theorem.cast h (by
    simp only [Term.diaNe, Term.instantiate, Term.weaken, Term.neg, Term.exists', Term.conj,
      Term.box, Term.imp, Term.dia, Term.rename_app, Term.rename_lam,
      Term.rename_rename, Term.rename_not, Term.rename_ex, Term.rename_and,
      Term.rename_or, Term.rename_all, Term.rename_eq, Term.rename_var,
      Term.subst_app, Term.subst_lam, Term.subst_not, Term.subst_ex,
      Term.subst_and, Term.subst_or, Term.subst_all, Term.subst_eq,
      Term.subst_var, Sub.lift, Sub.cons, Term.weaken, Term.rename_rename]
    rfl)

/-- Consistency is transported by a genuine C implication; no optional
premise is necessitated. -/
theorem consistent_add_of_imp {Ax : AxiomSet Sig} {p q : Sentence Sig}
    (h : C.Theorem (Term.imp p q)) (hp : Consistent (Ax ∪ single p)) :
    Consistent (Ax ∪ single q) := by
  apply Consistent.of_entails (Ax₁ := Ax ∪ single p) ?_ hp
  intro a ha
  rcases ha with ha | ha
  · exact Theorem.ax (Or.inl ha)
  · change a = q at ha
    subst a
    exact Theorem.mp (Theorem.ofC h) (Theorem.ax (Or.inr rfl))

/-- All Max-consistent, closed-type sentences for which C proves D-reflection.
At the pure signature this is a pure schema; at other signatures both Max and
SP retain their signature-relative meanings. -/
def reflectingMaxConsistent (Sig : Signature) : AxiomSet Sig := fun p =>
  p.closedTypes = true ∧ Consistent (maximalist ∪ single p) ∧
    C.Theorem (Term.imp (Term.diaNe p) p)

theorem strongPossibility_entails_reflectingMaxConsistent :
    strongPossibility Sig ⟹ reflectingMaxConsistent Sig := by
  rintro p ⟨hc, hcon, hreflect⟩
  exact Theorem.mp (Theorem.ofC hreflect) (strongPossibility_at hc hcon)

theorem reflectingMaxConsistent_entails_strongPossibility :
    reflectingMaxConsistent Sig ⟹ strongPossibility Sig := by
  rintro a ⟨hc, p, hcon, rfl⟩
  exact Theorem.ax
    ⟨hc, consistent_add_of_imp (c_diaNe_intro p) hcon, c_diaNe_idempotent p⟩

theorem consistent_strongPossibility_iff :
    Consistent (strongPossibility Sig) ↔ Consistent (reflectingMaxConsistent Sig) :=
  ⟨Consistent.of_entails strongPossibility_entails_reflectingMaxConsistent,
    Consistent.of_entails reflectingMaxConsistent_entails_strongPossibility⟩

def monism (Sig : Signature) : Sentence Sig :=
  Term.forall' (σ := Ty.e)
    (Term.forall' (σ := Ty.e) (Term.eq' Term.v1 Term.v0))

def atLeastTwo (Sig : Signature) : Sentence Sig :=
  Term.exists' (σ := Ty.e)
    (Term.exists' (σ := Ty.e) (Term.neg (Term.eq' Term.v1 Term.v0)))

theorem monism_closedTypes : (monism Sig).closedTypes = true := rfl

theorem monism_reflection_certificate :
    C.Theorem (Term.imp (Term.diaNe (monism Sig)) (monism Sig)) :=
  cMinus_to_c (C.TheoremMinus.ofPure
    (Classicism.Research.StrongPossibilityConsequences.diaNe_monism.derivable Ty.e))

/-- Conditional only on the separately stated model-consistency fact. This
parameter must not be removed without a coalesced-model certificate. -/
theorem pureSP_monism
    (hcon : Consistent ((maximalist : AxiomSet Signature.pure) ∪
      single (monism Signature.pure))) :
    Theorem (C.axioms ∪ strongPossibility Signature.pure) (monism Signature.pure) :=
  Theorem.mp (Theorem.ofC monism_reflection_certificate)
    (strongPossibility_at monism_closedTypes hcon)

theorem pureSP_not_atLeastTwo
    (hcon : Consistent ((maximalist : AxiomSet Signature.pure) ∪
      single (monism Signature.pure))) :
    Theorem (C.axioms ∪ strongPossibility Signature.pure)
      (Term.neg (atLeastTwo Signature.pure)) :=
  Theorem.mp
    (Theorem.ofCMinus
      (Classicism.Research.StrongPossibilityConsequences.diaNe_monism_not_two.derivable Ty.e))
    (strongPossibility_at monism_closedTypes hcon)

end Classicism.Meta.Research.StrongPossibilityConsequences
