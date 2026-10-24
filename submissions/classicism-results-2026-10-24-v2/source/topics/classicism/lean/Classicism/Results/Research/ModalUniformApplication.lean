import Classicism.Results.Research.ModalComprehensionConcreteCalculus

/-!
# Applying a uniform representative through its finite binder spine

Original research, misc, 23 October 2026. These are derivations in the
independent lambda-free object calculus. A boxed defining premise remains
local: universal instantiation under the box uses theorem UI, Nec and K.
Repeated application therefore obtains literal combinator equations from
one finite-body comprehension witness, without a nested choice of names.

This module supplies that application bridge. It does not itself construct
a translation of C, interpret the entire combinator calculus, or eliminate
the finitely many fresh constants used by such a translation.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open ModalComprehensionRepresentation (diagram UniformRepresents)

variable {Const : Ty → Type}

namespace Body

/-- Saturating a term into a body commutes with genuine capture-avoiding
substitution. No object beta-conversion is used in this syntax identity. -/
theorem subst_ofTerm (ρ : RTy) : ∀ {Γ Θ} (s : Sub Const Γ Θ)
    (M : Term Const Γ ρ),
    (ofTerm ρ M).subst s = ofTerm ρ (M.subst s) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
    intros
    simp only [ofTerm, subst, ih, Term.subst, Term.subst_wk, Sub.lift]

end Body

namespace Derives

/-- Apply one argument to a necessarily represented finite body. The
conclusion retains a single outer box over all remaining arguments. -/
theorem uniform_apply {Ax : Axioms Const} {Γ Δ σ} {ρ : RTy}
    {A : Body Const (σ :: Γ) ρ} {H : Term Const Γ (σ ⇒ ρ)}
    (a : Term Const Γ σ)
    (h : Derives Const Ax Γ Δ (UniformRepresents (.bind A) H)) :
    Derives Const Ax Γ Δ
      (UniformRepresents (A.subst (Sub.cons a Sub.id)) (.app H a)) := by
  change Derives Const Ax Γ Δ
    (Term.box (.all (diagram A (.app H.wk (.var .zero))))) at h
  have hi := boxed_allE a h
  change Derives Const Ax Γ Δ
    (Term.box ((diagram A (.app H.wk (.var .zero))).subst
      (Sub.cons a Sub.id))) at hi
  rw [Body.diagram_subst] at hi
  change Derives Const Ax Γ Δ
    (Term.box (diagram (A.subst (Sub.cons a Sub.id))
      (.app (H.wk.inst a) a))) at hi
  rw [Term.inst_wk] at hi
  exact hi

/-- Once the remaining body is an admitted term, Intensionality converts
its uniform representation directly into literal object identity. -/
theorem uniform_ofTerm_eq {Ax : Axioms Const} {Γ Δ} {ρ : RTy}
    {M H : Term Const Γ ρ}
    (h : Derives Const Ax Γ Δ (UniformRepresents (Body.ofTerm ρ M) H)) :
    Derives Const Ax Γ Δ (.eq H M) := by
  change Derives Const Ax Γ Δ (Term.box (diagram (Body.ofTerm ρ M) H)) at h
  rw [Body.diagram_ofTerm] at h
  exact .intensionality ρ H M h

/-- Literal unary beta for a finite-body witness, allowing any fixed
global axiom package and retaining arbitrary local hypotheses. -/
theorem uniform_beta {Ax : Axioms Const} {Γ Δ σ} {ρ : RTy}
    {M : Term Const (σ :: Γ) ρ} {H : Term Const Γ (σ ⇒ ρ)}
    (a : Term Const Γ σ)
    (h : Derives Const Ax Γ Δ
      (UniformRepresents (.bind (Body.ofTerm ρ M)) H)) :
    Derives Const Ax Γ Δ (.eq (.app H a) (M.inst a)) := by
  have hi := uniform_apply a h
  rw [Body.subst_ofTerm] at hi
  exact uniform_ofTerm_eq hi

/-- Two arguments use the same uniform witness. The displayed right side
is the actual simultaneous capture-avoiding instantiation of the body. -/
theorem uniform_beta₂ {Ax : Axioms Const} {Γ Δ σ τ} {ρ : RTy}
    {M : Term Const (τ :: σ :: Γ) ρ}
    {H : Term Const Γ (σ ⇒ τ ⇒ ρ)}
    (a : Term Const Γ σ) (b : Term Const Γ τ)
    (h : Derives Const Ax Γ Δ
      (UniformRepresents (.bind (.bind (Body.ofTerm ρ M))) H)) :
    Derives Const Ax Γ Δ
      (.eq (.app (.app H a) b)
        ((M.subst (Sub.lift (Sub.cons a Sub.id))).inst b)) := by
  have hi := uniform_apply a h
  change Derives Const Ax Γ Δ
    (UniformRepresents (.bind ((Body.ofTerm ρ M).subst
      (Sub.lift (Sub.cons a Sub.id)))) (.app H a)) at hi
  rw [Body.subst_ofTerm] at hi
  exact uniform_beta b hi

/-- Three-argument form sufficient for the typed S and C laws. -/
theorem uniform_beta₃ {Ax : Axioms Const} {Γ Δ σ τ υ} {ρ : RTy}
    {M : Term Const (υ :: τ :: σ :: Γ) ρ}
    {H : Term Const Γ (σ ⇒ τ ⇒ υ ⇒ ρ)}
    (a : Term Const Γ σ) (b : Term Const Γ τ) (c : Term Const Γ υ)
    (h : Derives Const Ax Γ Δ
      (UniformRepresents (.bind (.bind (.bind (Body.ofTerm ρ M)))) H)) :
    Derives Const Ax Γ Δ
      (.eq (.app (.app (.app H a) b) c)
        (((M.subst (Sub.lift (Sub.lift (Sub.cons a Sub.id)))).subst
          (Sub.lift (Sub.cons b Sub.id))).inst c)) := by
  have hi := uniform_apply a h
  change Derives Const Ax Γ Δ
    (UniformRepresents (.bind (.bind ((Body.ofTerm ρ M).subst
      (Sub.lift (Sub.lift (Sub.cons a Sub.id)))))) (.app H a)) at hi
  rw [Body.subst_ofTerm] at hi
  exact uniform_beta₂ b c hi

end Derives

#print axioms Body.subst_ofTerm
#print axioms Derives.uniform_apply
#print axioms Derives.uniform_ofTerm_eq
#print axioms Derives.uniform_beta
#print axioms Derives.uniform_beta₂
#print axioms Derives.uniform_beta₃

end Classicism.Research.ModalComprehensionConcreteSyntax
