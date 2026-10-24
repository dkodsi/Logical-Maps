import Classicism.Results.Research.RelationalLambdaCompilation
import Classicism.Results.Research.ModalComprehensionClassicalExtension

/-!
# Independent finite comprehension bodies for all logical objects

Original research, misc, 23 October 2026. The thirteen families below cover
the six logical and seven relational constructors of `RelationalLambdaCompilation.Atoms`.
Their bodies contain only the original lambda-free syntax. In particular a
higher-type body does not refer to a lower-type operator name. Each finite
instance has a closed body, and its existence is the actual SC rule.

This module defines syntax and proves substitution coherence. It introduces
no object axiom and does not select a family of comprehension witnesses.
-/

namespace Classicism.Research.ModalLogicalOperators
open Classicism.Meta (Ty RTy Signature)
open ModalComprehensionConcreteSyntax
open RelationalLambdaCompilation (Atoms)

inductive LogicalOperator : RTy → Type
  | and : LogicalOperator (RTy.t ⇒ RTy.t ⇒ RTy.t)
  | or : LogicalOperator (RTy.t ⇒ RTy.t ⇒ RTy.t)
  | not : LogicalOperator (RTy.t ⇒ RTy.t)
  | all (σ : Ty) : LogicalOperator ((σ ⇒ RTy.t) ⇒ RTy.t)
  | ex (σ : Ty) : LogicalOperator ((σ ⇒ RTy.t) ⇒ RTy.t)
  | eq (σ : Ty) : LogicalOperator (σ ⇒ σ ⇒ RTy.t)
  | constR (ρ : RTy) : LogicalOperator (RTy.t ⇒ ρ)
  | negR (ρ : RTy) : LogicalOperator (ρ ⇒ ρ)
  | andR (ρ : RTy) : LogicalOperator (ρ ⇒ ρ ⇒ ρ)
  | orR (ρ : RTy) : LogicalOperator (ρ ⇒ ρ ⇒ ρ)
  | coextR (ρ : RTy) : LogicalOperator (ρ ⇒ ρ ⇒ RTy.t)
  | boxR (ρ : RTy) : LogicalOperator (ρ ⇒ ρ)
  | inclR (ρ : RTy) : LogicalOperator (ρ ⇒ ρ ⇒ RTy.t)

def LogicalOperator.atom {Sig : Signature} {ρ : RTy} :
    LogicalOperator ρ → Atoms Sig ρ
  | .and => .and
  | .or => .or
  | .not => .not
  | .all σ => .all σ
  | .ex σ => .ex σ
  | .eq σ => .eq σ
  | .constR ρ => .constR ρ
  | .negR ρ => .negR ρ
  | .andR ρ => .andR ρ
  | .orR ρ => .orR ρ
  | .coextR ρ => .coextR ρ
  | .boxR ρ => .boxR ρ
  | .inclR ρ => .inclR ρ

inductive Unary where
  | neg
  | boxEq

inductive Binary where
  | and
  | or

variable {Const : Ty → Type}

def Unary.apply {Γ} : Unary → Formula Const Γ → Formula Const Γ
  | .neg, p => ModalComprehensionConcreteSyntax.neg p
  | .boxEq, p => .eq p .top

def Binary.apply {Γ} : Binary → Formula Const Γ → Formula Const Γ → Formula Const Γ
  | .and, p, q => conjunction p q
  | .or, p, q => disjunction p q

theorem Unary.subst_apply {Γ Θ} (u : Unary) (s : Sub Const Γ Θ)
    (p : Formula Const Γ) :
    (u.apply p).subst s = u.apply (p.subst s) := by
  cases u <;> rfl

theorem Binary.subst_apply {Γ Θ} (b : Binary) (s : Sub Const Γ Θ)
    (p q : Formula Const Γ) :
    (b.apply p q).subst s = b.apply (p.subst s) (q.subst s) := by
  cases b <;> rfl

/-- Saturate the output type while retaining one original proposition. -/
def constantBody : (ρ : RTy) → {Γ : Ctx} → Formula Const Γ → Body Const Γ ρ
  | .t, _, p => .atom p
  | _ ⇒ ρ, _, p => .bind (constantBody ρ p.wk)

/-- Pointwise unary operation with an entirely primitive terminal matrix. -/
def unaryBody (u : Unary) : (ρ : RTy) → {Γ : Ctx} →
    Term Const Γ ρ → Body Const Γ ρ
  | .t, _, X => .atom (u.apply X)
  | _ ⇒ ρ, _, X => .bind (unaryBody u ρ (.app X.wk (.var .zero)))

def binaryBody (b : Binary) : (ρ : RTy) → {Γ : Ctx} →
    Term Const Γ ρ → Term Const Γ ρ → Body Const Γ ρ
  | .t, _, X, Y => .atom (b.apply X Y)
  | _ ⇒ ρ, _, X, Y => .bind (binaryBody b ρ
      (.app X.wk (.var .zero)) (.app Y.wk (.var .zero)))

/-- Inclusion here is universally quantified pointwise implication, not
the algebraic Boolean order. -/
def inclusion : (ρ : RTy) → {Γ : Ctx} →
    Term Const Γ ρ → Term Const Γ ρ → Formula Const Γ
  | .t, _, X, Y => .imp X Y
  | _ ⇒ ρ, _, X, Y => .all (inclusion ρ
      (.app X.wk (.var .zero)) (.app Y.wk (.var .zero)))

theorem constantBody_subst (ρ : RTy) : ∀ {Γ Θ} (s : Sub Const Γ Θ)
    (p : Formula Const Γ),
    (constantBody ρ p).subst s = constantBody ρ (p.subst s) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [constantBody, Body.subst, ih, Term.subst_wk]

theorem unaryBody_subst (u : Unary) (ρ : RTy) : ∀ {Γ Θ}
    (s : Sub Const Γ Θ) (X : Term Const Γ ρ),
    (unaryBody u ρ X).subst s = unaryBody u ρ (X.subst s) := by
  induction ρ using RTy.induction with
  | t => intros; simp only [unaryBody, Body.subst, Unary.subst_apply]
  | arr σ ρ ih =>
      intros
      simp only [unaryBody, Body.subst, ih, Term.subst, Term.subst_wk, Sub.lift]

theorem binaryBody_subst (b : Binary) (ρ : RTy) : ∀ {Γ Θ}
    (s : Sub Const Γ Θ) (X Y : Term Const Γ ρ),
    (binaryBody b ρ X Y).subst s = binaryBody b ρ (X.subst s) (Y.subst s) := by
  induction ρ using RTy.induction with
  | t => intros; simp only [binaryBody, Body.subst, Binary.subst_apply]
  | arr σ ρ ih =>
      intros
      simp only [binaryBody, Body.subst, ih, Term.subst, Term.subst_wk, Sub.lift]

theorem inclusion_subst (ρ : RTy) : ∀ {Γ Θ} (s : Sub Const Γ Θ)
    (X Y : Term Const Γ ρ),
    (inclusion ρ X Y).subst s = inclusion ρ (X.subst s) (Y.subst s) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [inclusion, Term.subst, ih, Term.subst_wk, Sub.lift]

/-- A finite body for each whole operator. All displayed inputs and output
tails are bound; no other operator or signature constant occurs. -/
def LogicalOperator.body {ρ : RTy} (o : LogicalOperator ρ) (Γ : Ctx) :
    Body Const Γ ρ :=
  match o with
  | .and => .bind (.bind (.atom (conjunction (.var (.succ .zero)) (.var .zero))))
  | .or => .bind (.bind (.atom (disjunction (.var (.succ .zero)) (.var .zero))))
  | .not => .bind (.atom (neg (.var .zero)))
  | .all σ => .bind (.atom (.all (.app (.var (.succ .zero)) (.var .zero))))
  | .ex σ => .bind (.atom (.ex (.app (.var (.succ .zero)) (.var .zero))))
  | .eq σ => .bind (.bind (.atom (.eq (.var (.succ .zero)) (.var .zero))))
  | .constR ρ => .bind (constantBody ρ (.var .zero))
  | .negR ρ => .bind (unaryBody .neg ρ (.var .zero))
  | .andR ρ => .bind (.bind (binaryBody .and ρ (.var (.succ .zero)) (.var .zero)))
  | .orR ρ => .bind (.bind (binaryBody .or ρ (.var (.succ .zero)) (.var .zero)))
  | .coextR ρ => .bind (.bind (.atom (Term.coext ρ (.var (.succ .zero)) (.var .zero))))
  | .boxR ρ => .bind (unaryBody .boxEq ρ (.var .zero))
  | .inclR ρ => .bind (.bind (.atom (inclusion ρ (.var (.succ .zero)) (.var .zero))))

/-- Closedness is witnessed by invariance under every ordinary substitution
of the surrounding parameters. This is a literal syntax theorem. -/
theorem LogicalOperator.body_subst {Γ Θ} {ρ : RTy} (o : LogicalOperator ρ)
    (s : Sub Const Γ Θ) : (o.body Γ).subst s = o.body Θ := by
  cases o <;>
    simp only [LogicalOperator.body, Body.subst, constantBody_subst,
      unaryBody_subst, binaryBody_subst, Term.subst_coext, inclusion_subst,
      conjunction, disjunction, neg, bottom, Term.subst, Sub.lift] <;> rfl

theorem LogicalOperator.exists_body {Ax : Axioms Const} {Γ Δ} {ρ : RTy}
    (o : LogicalOperator ρ) :
    Derives Const Ax Γ Δ (.ex (Body.code (o.body Γ))) :=
  .comprehension (o.body Γ)

#print axioms LogicalOperator.body_subst
#print axioms LogicalOperator.exists_body

end Classicism.Research.ModalLogicalOperators
