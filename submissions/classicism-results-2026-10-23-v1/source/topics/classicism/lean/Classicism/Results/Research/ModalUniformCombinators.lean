import Classicism.Results.Research.ModalUniformApplication

/-!
# Typed combinator laws from uniform modal comprehension

Original research, misc, 23 October 2026. Each of I, K, S, C and W is
represented by one explicit finite binder body in the lambda-free syntax.
The defining premise stays local while the literal application equations
are derived. Its existence is an instance of the calculus's actual SC rule.

The intermediate type of S is relational. C and W permit arbitrary input
types, so these bodies never require an inadmissible e-to-e arrow.
Interpreting a complete source calculus and eliminating the finite names
used by that interpretation are separate obligations.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open ModalComprehensionRepresentation (UniformRepresents)

variable {Const : Ty → Type}

namespace CombinatorBody

def I (ρ : RTy) (Γ : Ctx) : Body Const Γ (ρ ⇒ ρ) :=
  .bind (Body.ofTerm ρ (.var .zero))

def K (σ : Ty) (ρ : RTy) (Γ : Ctx) : Body Const Γ (ρ ⇒ σ ⇒ ρ) :=
  .bind (.bind (Body.ofTerm ρ (.var (.succ .zero))))

def S (σ : Ty) (τ ρ : RTy) (Γ : Ctx) :
    Body Const Γ ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ) :=
  .bind (.bind (.bind (Body.ofTerm ρ
    (.app (.app (.var (.succ (.succ .zero))) (.var .zero))
      (.app (.var (.succ .zero)) (.var .zero))))))

def C (σ τ : Ty) (ρ : RTy) (Γ : Ctx) :
    Body Const Γ ((σ ⇒ τ ⇒ ρ) ⇒ τ ⇒ σ ⇒ ρ) :=
  .bind (.bind (.bind (Body.ofTerm ρ
    (.app (.app (.var (.succ (.succ .zero))) (.var .zero))
      (.var (.succ .zero))))))

def W (σ : Ty) (ρ : RTy) (Γ : Ctx) :
    Body Const Γ ((σ ⇒ σ ⇒ ρ) ⇒ σ ⇒ ρ) :=
  .bind (.bind (Body.ofTerm ρ
    (.app (.app (.var (.succ .zero)) (.var .zero)) (.var .zero))))

end CombinatorBody

namespace Term

/-- A substitution presentation of the already proved weakening/instantiation
identity, convenient when calculating a finite combinator body. -/
theorem subst_cons_wk {Γ σ τ} (M : Term Const Γ τ) (a : Term Const Γ σ) :
    M.wk.subst (Sub.cons a Sub.id) = M := inst_wk M a

end Term

namespace Derives

theorem uniform_I {Ax : Axioms Const} {Γ Δ} {ρ : RTy}
    {H : Term Const Γ (ρ ⇒ ρ)} (a : Term Const Γ ρ)
    (h : Derives Const Ax Γ Δ (UniformRepresents (CombinatorBody.I ρ Γ) H)) :
    Derives Const Ax Γ Δ (.eq (.app H a) a) := by
  exact uniform_beta a h

theorem uniform_K {Ax : Axioms Const} {Γ Δ σ} {ρ : RTy}
    {H : Term Const Γ (ρ ⇒ σ ⇒ ρ)}
    (a : Term Const Γ ρ) (b : Term Const Γ σ)
    (h : Derives Const Ax Γ Δ (UniformRepresents (CombinatorBody.K σ ρ Γ) H)) :
    Derives Const Ax Γ Δ (.eq (.app (.app H a) b) a) := by
  have hi := uniform_beta₂ a b h
  simpa only [Term.inst, Term.subst, Sub.lift, Sub.cons,
    Term.subst_cons_wk] using hi

theorem uniform_S {Ax : Axioms Const} {Γ Δ σ} {τ ρ : RTy}
    {H : Term Const Γ ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)}
    (f : Term Const Γ (σ ⇒ τ ⇒ ρ)) (g : Term Const Γ (σ ⇒ τ))
    (a : Term Const Γ σ)
    (h : Derives Const Ax Γ Δ (UniformRepresents (CombinatorBody.S σ τ ρ Γ) H)) :
    Derives Const Ax Γ Δ
      (.eq (.app (.app (.app H f) g) a) (.app (.app f a) (.app g a))) := by
  have hi := uniform_beta₃ f g a h
  simpa only [Term.inst, Term.subst, Sub.lift, Sub.cons,
    Term.subst_wk, Term.subst_cons_wk] using hi

theorem uniform_C {Ax : Axioms Const} {Γ Δ σ τ} {ρ : RTy}
    {H : Term Const Γ ((σ ⇒ τ ⇒ ρ) ⇒ τ ⇒ σ ⇒ ρ)}
    (f : Term Const Γ (σ ⇒ τ ⇒ ρ)) (b : Term Const Γ τ)
    (a : Term Const Γ σ)
    (h : Derives Const Ax Γ Δ (UniformRepresents (CombinatorBody.C σ τ ρ Γ) H)) :
    Derives Const Ax Γ Δ
      (.eq (.app (.app (.app H f) b) a) (.app (.app f a) b)) := by
  have hi := uniform_beta₃ f b a h
  simpa only [Term.inst, Term.subst, Sub.lift, Sub.cons,
    Term.subst_wk, Term.subst_cons_wk] using hi

theorem uniform_W {Ax : Axioms Const} {Γ Δ σ} {ρ : RTy}
    {H : Term Const Γ ((σ ⇒ σ ⇒ ρ) ⇒ σ ⇒ ρ)}
    (f : Term Const Γ (σ ⇒ σ ⇒ ρ)) (a : Term Const Γ σ)
    (h : Derives Const Ax Γ Δ (UniformRepresents (CombinatorBody.W σ ρ Γ) H)) :
    Derives Const Ax Γ Δ
      (.eq (.app (.app H f) a) (.app (.app f a) a)) := by
  have hi := uniform_beta₂ f a h
  simpa only [Term.inst, Term.subst, Sub.lift, Sub.cons,
    Term.subst_cons_wk] using hi

/-- All five typed bodies receive the same actual comprehension existence
proof. No global selector of representatives is assumed. -/
theorem uniform_combinator_exists {Ax : Axioms Const} {Γ Δ} {ρ : RTy}
    (A : Body Const Γ ρ) : Derives Const Ax Γ Δ (.ex (Body.code A)) :=
  .comprehension A

end Derives

#print axioms Derives.uniform_I
#print axioms Derives.uniform_K
#print axioms Derives.uniform_S
#print axioms Derives.uniform_C
#print axioms Derives.uniform_W
#print axioms Derives.uniform_combinator_exists

end Classicism.Research.ModalComprehensionConcreteSyntax
