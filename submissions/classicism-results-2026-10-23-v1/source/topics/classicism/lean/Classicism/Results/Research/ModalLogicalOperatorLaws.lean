import Classicism.Results.Research.ModalLogicalOperatorBodies
import Classicism.Results.Research.ModalClassicalRules
import Classicism.Results.Research.ModalFiniteClassicalDefinitions

/-!
# Literal application and recursive delta laws for named logical objects

Original research, misc, 23 October 2026. The global definition package
contains precisely classical base axioms, the previous five combinator
definitions, and the independent SC bodies of ModalLogicalOperatorBodies.
No application equation is inserted as an axiom. Every equation below is
derived by boxed UI and Intensionality from its defining body.

The recursive laws compare partially applied relations by uniqueness of
their common uniform body. Consequently they do not infer operation
identity from an unboxed pointwise premise and require neither BF nor
choice. Finite-name elimination and raw `Meta.Term.unfoldR` transport are
separate from this module's application-level laws.
-/

namespace Classicism.Research.ModalLogicalOperators
open Classicism.Meta (Ty RTy Signature)
open ModalComprehensionConcreteSyntax
open ModalComprehensionRepresentation (UniformRepresents)
open RelationalBracketAbstraction (BasisConst)
open RelationalLambdaCompilation (Atoms)

abbrev Constants (Sig : Signature) := BasisConst (Atoms Sig)

def named {Sig : Signature} {Γ : Ctx} {ρ : RTy} (o : LogicalOperator ρ) :
    Term (Constants Sig) Γ ρ := .const (.original o.atom)

/-- Only the explicitly displayed definition axioms are added. -/
inductive ExpandedNamedAxiom (Sig : Signature) : Axioms (Constants Sig)
  | basis {Γ p} : RelationalBracketInterpretation.NamedAxiom (Atoms Sig) Γ p →
      ExpandedNamedAxiom Sig Γ p
  | classical {Γ p} : ClassicalAxioms (Constants Sig) Γ p →
      ExpandedNamedAxiom Sig Γ p
  | logical {Γ} {ρ : RTy} (o : LogicalOperator ρ) : ExpandedNamedAxiom Sig Γ
      (UniformRepresents (o.body Γ) (named o))

variable {Sig : Signature}

theorem containsClassical : ModalClassicalRules.ContainsClassical (ExpandedNamedAxiom Sig) :=
  fun _ _ h => .classical h

/-- Actual induction on derivations, via the independently implemented
global-axiom replacement theorem; no proof-preservation assumption. -/
theorem lift_basis {Γ Δ p}
    (h : Derives (Constants Sig) (RelationalBracketInterpretation.NamedAxiom (Atoms Sig)) Γ Δ p) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ p :=
  ModalFreshConstantSyntax.replace_global_axioms (fun _ _ h => .ax (.basis h)) h

theorem lift_classical {Γ Δ p}
    (h : Derives (Constants Sig) (ClassicalAxioms (Constants Sig)) Γ Δ p) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ p :=
  ModalFreshConstantSyntax.replace_global_axioms (fun _ _ h => .ax (.classical h)) h

theorem definition {Γ Δ} {ρ : RTy} (o : LogicalOperator ρ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (UniformRepresents (o.body Γ) (named o)) := .ax (.logical o)

theorem named_not {Γ Δ} (p : Formula (Constants Sig) Γ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (named .not) p) (neg p)) := by
  exact Derives.uniform_beta p (definition .not)

theorem named_and {Γ Δ} (p q : Formula (Constants Sig) Γ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (named .and) p) q) (conjunction p q)) := by
  have h := Derives.uniform_beta₂ p q (definition (Sig := Sig) (Δ := Δ) .and)
  simpa only [Term.inst, Term.subst, Sub.lift, Sub.cons, conjunction, neg,
    bottom, Term.subst_cons_wk] using h

theorem named_or {Γ Δ} (p q : Formula (Constants Sig) Γ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (named .or) p) q) (disjunction p q)) := by
  have h := Derives.uniform_beta₂ p q (definition (Sig := Sig) (Δ := Δ) .or)
  simpa only [Term.inst, Term.subst, Sub.lift, Sub.cons, disjunction, neg,
    bottom, Term.subst_cons_wk] using h

theorem named_all {Γ Δ σ} (F : Term (Constants Sig) Γ (σ ⇒ RTy.t)) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (named (.all σ)) F) (.all (.app F.wk (.var .zero)))) := by
  exact Derives.uniform_beta F (definition (.all σ))

theorem named_ex {Γ Δ σ} (F : Term (Constants Sig) Γ (σ ⇒ RTy.t)) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (named (.ex σ)) F) (.ex (.app F.wk (.var .zero)))) := by
  exact Derives.uniform_beta F (definition (.ex σ))

theorem named_eq {Γ Δ σ} (a b : Term (Constants Sig) Γ σ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (named (.eq σ)) a) b) (.eq a b)) := by
  have h := Derives.uniform_beta₂ a b (definition (Sig := Sig) (Δ := Δ) (.eq σ))
  simpa only [Term.inst, Term.subst, Sub.lift, Sub.cons, Term.subst_cons_wk] using h

def Unary.operator (u : Unary) (ρ : RTy) : LogicalOperator (ρ ⇒ ρ) :=
  match u with
  | .neg => .negR ρ
  | .boxEq => .boxR ρ

def Binary.operator (b : Binary) (ρ : RTy) : LogicalOperator (ρ ⇒ ρ ⇒ ρ) :=
  match b with
  | .and => .andR ρ
  | .or => .orR ρ

theorem unary_operator_body (u : Unary) (ρ : RTy) (Γ : Ctx) :
    (u.operator ρ).body (Const := Constants Sig) Γ =
      .bind (unaryBody u ρ (.var .zero)) := by cases u <;> rfl

theorem binary_operator_body (b : Binary) (ρ : RTy) (Γ : Ctx) :
    (b.operator ρ).body (Const := Constants Sig) Γ =
      .bind (.bind (binaryBody b ρ (.var (.succ .zero)) (.var .zero))) := by
  cases b <;> rfl

theorem named_constant_representation {Γ Δ} (ρ : RTy) (p : Formula (Constants Sig) Γ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (UniformRepresents (constantBody ρ p) (.app (named (.constR ρ)) p)) := by
  have h := Derives.uniform_apply p (definition (Sig := Sig) (Δ := Δ) (.constR ρ))
  simpa only [LogicalOperator.body, constantBody_subst, Term.subst, Sub.cons] using h

theorem named_unary_representation {Γ Δ} (u : Unary) (ρ : RTy)
    (X : Term (Constants Sig) Γ ρ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (UniformRepresents (unaryBody u ρ X) (.app (named (u.operator ρ)) X)) := by
  have hd := definition (Sig := Sig) (Δ := Δ) (Γ := Γ) (u.operator ρ)
  rw [unary_operator_body] at hd
  have h := Derives.uniform_apply X hd
  simpa only [unaryBody_subst, Term.subst, Sub.cons] using h

theorem named_binary_representation {Γ Δ} (b : Binary) (ρ : RTy)
    (X Y : Term (Constants Sig) Γ ρ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (UniformRepresents (binaryBody b ρ X Y) (.app (.app (named (b.operator ρ)) X) Y)) := by
  have hd := definition (Sig := Sig) (Δ := Δ) (Γ := Γ) (b.operator ρ)
  rw [binary_operator_body] at hd
  have hx : Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (UniformRepresents (.bind (binaryBody b ρ X.wk (.var .zero)))
        (.app (named (b.operator ρ)) X)) := by
    simpa only [Body.subst, binaryBody_subst, Term.subst, Sub.lift, Sub.cons]
      using Derives.uniform_apply X hd
  have hy := Derives.uniform_apply Y hx
  simpa only [binaryBody_subst, Term.subst, Sub.cons, Term.subst_cons_wk] using hy

theorem named_coextR {Γ Δ} (ρ : RTy) (X Y : Term (Constants Sig) Γ ρ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (named (.coextR ρ)) X) Y) (Term.coext ρ X Y)) := by
  have h := Derives.uniform_beta₂ X Y (definition (Sig := Sig) (Δ := Δ) (.coextR ρ))
  simpa only [Term.inst, Term.subst_coext, Term.subst, Sub.lift, Sub.cons,
    Term.subst_cons_wk] using h

theorem named_inclR {Γ Δ} (ρ : RTy) (X Y : Term (Constants Sig) Γ ρ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (named (.inclR ρ)) X) Y) (inclusion ρ X Y)) := by
  have h := Derives.uniform_beta₂ X Y (definition (Sig := Sig) (Δ := Δ) (.inclR ρ))
  simpa only [Term.inst, inclusion_subst, Term.subst, Sub.lift, Sub.cons,
    Term.subst_cons_wk] using h

/-- Two local boxed definitions of the same whole finite body suffice.
No local premise is necessitated or generalized. -/
theorem represented_unique {Const : Ty → Type} {Ax : Axioms Const} {Γ Δ} {ρ : RTy}
    {A : Body Const Γ ρ} {X Y : Term Const Γ ρ}
    (hx : Derives Const Ax Γ Δ (UniformRepresents A X))
    (hy : Derives Const Ax Γ Δ (UniformRepresents A Y)) :
    Derives Const Ax Γ Δ (.eq X Y) :=
  .impE (.impE (.lift ((calculus Const Ax).uniform_representative_unique A X Y)) hx) hy

theorem named_constR_t {Γ Δ} (p : Formula (Constants Sig) Γ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (named (.constR .t)) p) p) :=
  Derives.uniform_ofTerm_eq (named_constant_representation .t p)

theorem named_unary_t {Γ Δ} (u : Unary) (p : Formula (Constants Sig) Γ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (named (u.operator .t)) p) (u.apply p)) :=
  Derives.uniform_ofTerm_eq (named_unary_representation u .t p)

theorem named_binary_t {Γ Δ} (b : Binary) (p q : Formula (Constants Sig) Γ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (named (b.operator .t)) p) q) (b.apply p q)) :=
  Derives.uniform_ofTerm_eq (named_binary_representation b .t p q)

/-- Recursive constant-operation law, at literal relation identity. -/
theorem named_constR_step {Γ Δ σ} (ρ : RTy)
    (p : Formula (Constants Sig) Γ) (a : Term (Constants Sig) Γ σ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (named (.constR (σ ⇒ ρ))) p) a)
        (.app (named (.constR ρ)) p)) := by
  have h := Derives.uniform_apply a
    (named_constant_representation (Sig := Sig) (Δ := Δ) (σ ⇒ ρ) p)
  have h' : Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (UniformRepresents (constantBody ρ p)
        (.app (.app (named (.constR (σ ⇒ ρ))) p) a)) := by
    simpa only [constantBody, constantBody_subst, Term.subst_cons_wk] using h
  exact represented_unique h' (named_constant_representation ρ p)

theorem named_unary_step {Γ Δ σ} (u : Unary) (ρ : RTy)
    (X : Term (Constants Sig) Γ (σ ⇒ ρ)) (a : Term (Constants Sig) Γ σ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (named (u.operator (σ ⇒ ρ))) X) a)
        (.app (named (u.operator ρ)) (.app X a))) := by
  have h := Derives.uniform_apply a
    (named_unary_representation (Sig := Sig) (Δ := Δ) u (σ ⇒ ρ) X)
  have h' : Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (UniformRepresents (unaryBody u ρ (.app X a))
        (.app (.app (named (u.operator (σ ⇒ ρ))) X) a)) := by
    simpa only [unaryBody, unaryBody_subst, Term.subst, Sub.cons,
      Term.subst_cons_wk] using h
  exact represented_unique h' (named_unary_representation u ρ (.app X a))

theorem named_binary_step {Γ Δ σ} (b : Binary) (ρ : RTy)
    (X Y : Term (Constants Sig) Γ (σ ⇒ ρ)) (a : Term (Constants Sig) Γ σ) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (.eq (.app (.app (.app (named (b.operator (σ ⇒ ρ))) X) Y) a)
        (.app (.app (named (b.operator ρ)) (.app X a)) (.app Y a))) := by
  have h := Derives.uniform_apply a
    (named_binary_representation (Sig := Sig) (Δ := Δ) b (σ ⇒ ρ) X Y)
  have h' : Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ
      (UniformRepresents (binaryBody b ρ (.app X a) (.app Y a))
        (.app (.app (.app (named (b.operator (σ ⇒ ρ))) X) Y) a)) := by
    simpa only [binaryBody, binaryBody_subst, Term.subst, Sub.cons,
      Term.subst_cons_wk] using h
  exact represented_unique h' (named_binary_representation b ρ (.app X a) (.app Y a))

/-- Coextension and inclusion keep their entire output tuple under the
primitive binder. These are theorem-level binder identities. -/
theorem named_coextR_step {Γ σ} (ρ : RTy)
    (X Y : Term (Constants Sig) Γ (σ ⇒ ρ)) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ []
      (.eq (.app (.app (named (.coextR (σ ⇒ ρ))) X) Y)
        (.all (.app (.app (named (.coextR ρ)) (.app X.wk (.var .zero)))
          (.app Y.wk (.var .zero))))) := by
  exact .eqTrans (named_coextR (σ ⇒ ρ) X Y)
    (.eqSymm (ModalClassicalRules.all_identity
      (named_coextR ρ (.app X.wk (.var .zero)) (.app Y.wk (.var .zero)))))

theorem named_inclR_step {Γ σ} (ρ : RTy)
    (X Y : Term (Constants Sig) Γ (σ ⇒ ρ)) :
    Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ []
      (.eq (.app (.app (named (.inclR (σ ⇒ ρ))) X) Y)
        (.all (.app (.app (named (.inclR ρ)) (.app X.wk (.var .zero)))
          (.app Y.wk (.var .zero))))) := by
  exact .eqTrans (named_inclR (σ ⇒ ρ) X Y)
    (.eqSymm (ModalClassicalRules.all_identity
      (named_inclR ρ (.app X.wk (.var .zero)) (.app Y.wk (.var .zero)))))

#print axioms lift_basis
#print axioms named_all
#print axioms named_eq
#print axioms named_constR_step
#print axioms named_unary_step
#print axioms named_binary_step
#print axioms named_coextR_step
#print axioms named_inclR_step

end Classicism.Research.ModalLogicalOperators
