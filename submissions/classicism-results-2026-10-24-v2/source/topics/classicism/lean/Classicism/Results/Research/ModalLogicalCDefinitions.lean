import Classicism.Results.Research.ModalLogicalOperatorBodies
import Classicism.Results.Research.ModalConcreteToCDerivation
import Classicism.Results.Research.RelationalLambdaDecoding
import Classicism.Syntax.Blocks

/-!
# The independent logical comprehension bodies have their original C meanings

Original research implementation, misc, 23 October 2026, by Codex (OpenAI),
prompted by Daniel Kodsi. Every conclusion is an actual empty-hypothesis C
derivation. The classical implication/falsity definitions are identified by
theorem equivalence before abstraction; the seven relational families use
finite output-type induction and the original delta conversions.

No preservation interface, optional axiom, local extensionality, or new
logical constant is assumed. This source has not been compiler-checked.
-/

namespace Classicism.Research.ModalNamedToC
open Classicism.Meta
open ModalConcreteToC
open ModalLogicalOperators
open RelationalLambdaDecoding (decodeAtom)

variable {Const : Ty → Type}

private theorem logical_conv_eq {Γ σ}
    {a b : Term (signature Const) Γ σ} (h : Conv a b) :
    C.Derivable [] (Term.eq' a b) :=
  Derivable.conv (Derivable.refl a) (Conv.app_congr (Conv.refl _) h)

private theorem logical_right_conv {Γ σ}
    {a b c : Term (signature Const) Γ σ}
    (h : C.Derivable [] (Term.eq' a b)) (hc : Conv b c) :
    C.Derivable [] (Term.eq' a c) :=
  Derivable.conv h (Conv.app_congr (Conv.refl _) hc)

private theorem logical_hyp₁ {Γ} {p q : Formula (signature Const) Γ} {Δ} :
    C.Derivable (p :: q :: Δ) q :=
  Derivable.weaken₁ Derivable.hyp₀

private theorem logical_hyp₂ {Γ} {p q r : Formula (signature Const) Γ} {Δ} :
    C.Derivable (p :: q :: r :: Δ) r :=
  Derivable.weaken₁ (Derivable.weaken₁ Derivable.hyp₀)

/-- The source falsity is forall p, p, so its elimination is ordinary UI. -/
private theorem logical_false_elim {Γ Δ}
    {p : Formula (signature Const) Γ}
    (h : C.Derivable Δ (Term.forall' (Term.var .zero))) :
    C.Derivable Δ p := by
  simpa only [Term.instantiate, Term.subst_var, Sub.cons_zero] using
    Derivable.allEβ h p

private theorem logical_neg {Γ}
    (p : ModalComprehensionConcreteSyntax.Formula Const Γ) :
    C.Derivable [] (Term.eq' (toC (ModalComprehensionConcreteSyntax.neg p))
      (Term.neg (toC p))) := by
  apply c_equivalence
  · exact Derivable.notI Derivable.hyp₀
      (logical_false_elim (Derivable.impE logical_hyp₁ Derivable.hyp₀))
  · exact Derivable.impI (Derivable.notE Derivable.hyp₀ logical_hyp₁)

private theorem logical_conjunction {Γ}
    (p q : ModalComprehensionConcreteSyntax.Formula Const Γ) :
    C.Derivable [] (Term.eq'
      (toC (ModalComprehensionConcreteSyntax.conjunction p q))
      (Term.conj (toC p) (toC q))) := by
  apply c_equivalence
  · apply Derivable.andI
    · apply Derivable.orE (Derivable.em (toC p))
      · exact Derivable.hyp₀
      · apply logical_false_elim
        apply Derivable.impE logical_hyp₁
        exact Derivable.impI (Derivable.impI
          (Derivable.notE logical_hyp₁ logical_hyp₂))
    · apply Derivable.orE (Derivable.em (toC q))
      · exact Derivable.hyp₀
      · apply logical_false_elim
        apply Derivable.impE logical_hyp₁
        exact Derivable.impI (Derivable.impI
          (Derivable.notE Derivable.hyp₀ logical_hyp₂))
  · apply Derivable.impI
    exact Derivable.impE
      (Derivable.impE Derivable.hyp₀ (Derivable.andE₁ logical_hyp₁))
      (Derivable.andE₂ logical_hyp₁)

private theorem logical_disjunction {Γ}
    (p q : ModalComprehensionConcreteSyntax.Formula Const Γ) :
    C.Derivable [] (Term.eq'
      (toC (ModalComprehensionConcreteSyntax.disjunction p q))
      (Term.disj (toC p) (toC q))) := by
  apply c_equivalence
  · apply Derivable.orE (Derivable.em (toC p))
    · exact Derivable.orI₁ Derivable.hyp₀
    · exact Derivable.orI₂ (Derivable.impE logical_hyp₁
        (Derivable.impI (Derivable.notE Derivable.hyp₀ logical_hyp₁)))
  · apply Derivable.impI
    apply Derivable.orE logical_hyp₁
    · exact logical_false_elim (Derivable.impE logical_hyp₁ Derivable.hyp₀)
    · exact Derivable.hyp₀

/-- Only theorem identities are closed over a fresh argument. -/
private theorem logical_close {Γ σ} {ρ : RTy}
    (F : Term (signature Const) Γ (σ ⇒ ρ))
    {b : Term (signature Const) (σ :: Γ) ρ}
    (h : C.Derivable [] (Term.eq' b (.app F.weaken (.var .zero)))) :
    C.Derivable [] (Term.eq' (.lam b) F) :=
  logical_right_conv (c_lam_identity h) (Conv.eta F)

private theorem logical_const_body (ρ : RTy) : ∀ {Γ}
    (p : ModalComprehensionConcreteSyntax.Formula Const Γ),
    C.Derivable [] (Term.eq' (bodyWitness (constantBody ρ p))
      (.app (.constR ρ) (toC p))) := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ p
      apply logical_conv_eq
      exact Conv.symm (Conv.trans
        (Conv.app_congr (Conv.delta rfl) (Conv.refl _)) (Conv.beta _ _))
  | arr σ ρ ih =>
      intro Γ p
      have h := c_lam_identity (ih (p.wk (σ := σ)))
      have hc : Conv (.app (.constR (σ ⇒ ρ)) (toC p))
          (.lam (.app (.constR ρ) (toC p).weaken)) :=
        Conv.app_constR_block [σ] ρ (toC p)
      apply logical_right_conv (hc := Conv.symm hc)
      simpa only [constantBody, bodyWitness, toC_wk] using h

private def logical_unary (u : Unary) (ρ : RTy) {Γ} :
    Term (signature Const) Γ (ρ ⇒ ρ) :=
  match u with
  | .neg => .negR ρ
  | .boxEq => .boxR ρ

private theorem logical_unary_step (u : Unary) (σ : Ty) (ρ : RTy) {Γ}
    (X : Term (signature Const) Γ (σ ⇒ ρ)) :
    Conv (.app (logical_unary u (σ ⇒ ρ)) X)
      (.lam (.app (logical_unary u ρ) (.app X.weaken (.var .zero)))) := by
  cases u with
  | neg => exact Conv.app_negR_block [σ] ρ X
  | boxEq => exact Conv.app_boxR_block [σ] ρ X

private theorem logical_unary_body (u : Unary) (ρ : RTy) : ∀ {Γ}
    (X : ModalComprehensionConcreteSyntax.Term Const Γ ρ),
    C.Derivable [] (Term.eq' (bodyWitness (unaryBody u ρ X))
      (.app (logical_unary u ρ) (toC X))) := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ X
      cases u with
      | neg =>
          exact logical_right_conv (logical_neg X)
            (Conv.symm (Conv.app_congr (Conv.delta rfl) (Conv.refl _)))
      | boxEq =>
          apply logical_conv_eq
          exact Conv.symm (Conv.trans
            (Conv.app_congr (Conv.delta rfl) (Conv.refl _)) (Conv.beta _ _))
  | arr σ ρ ih =>
      intro Γ X
      have h := c_lam_identity (ih (.app X.wk (.var .zero)))
      apply logical_right_conv (hc := Conv.symm (logical_unary_step u σ ρ (toC X)))
      simpa only [unaryBody, bodyWitness, toC, toC_wk, toCVar] using h

private def logical_binary (b : Binary) (ρ : RTy) {Γ} :
    Term (signature Const) Γ (ρ ⇒ ρ ⇒ ρ) :=
  match b with
  | .and => .andR ρ
  | .or => .orR ρ

private theorem logical_binary_step (b : Binary) (σ : Ty) (ρ : RTy) {Γ}
    (X Y : Term (signature Const) Γ (σ ⇒ ρ)) :
    Conv (.app (.app (logical_binary b (σ ⇒ ρ)) X) Y)
      (.lam (.app (.app (logical_binary b ρ) (.app X.weaken (.var .zero)))
        (.app Y.weaken (.var .zero)))) := by
  cases b with
  | and => exact Conv.app_andR_block [σ] ρ X Y
  | or => exact Conv.app_orR_block [σ] ρ X Y

private theorem logical_binary_body (b : Binary) (ρ : RTy) : ∀ {Γ}
    (X Y : ModalComprehensionConcreteSyntax.Term Const Γ ρ),
    C.Derivable [] (Term.eq' (bodyWitness (binaryBody b ρ X Y))
      (.app (.app (logical_binary b ρ) (toC X)) (toC Y))) := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ X Y
      cases b with
      | and =>
          exact logical_right_conv (logical_conjunction X Y)
            (Conv.symm (Conv.app_congr
              (Conv.app_congr (Conv.delta rfl) (Conv.refl _)) (Conv.refl _)))
      | or =>
          exact logical_right_conv (logical_disjunction X Y)
            (Conv.symm (Conv.app_congr
              (Conv.app_congr (Conv.delta rfl) (Conv.refl _)) (Conv.refl _)))
  | arr σ ρ ih =>
      intro Γ X Y
      have h := c_lam_identity
        (ih (.app X.wk (.var .zero)) (.app Y.wk (.var .zero)))
      apply logical_right_conv
        (hc := Conv.symm (logical_binary_step b σ ρ (toC X) (toC Y)))
      simpa only [binaryBody, bodyWitness, toC, toC_wk, toCVar] using h

private theorem logical_coext_t {Γ}
    (p q : Formula (signature Const) Γ) :
    Conv (.app (.app (.coextR .t) p) q) (Term.iff p q) := by
  refine Conv.trans
    (Conv.app_congr (Conv.app_congr (Conv.delta rfl) (Conv.refl p)) (Conv.refl q)) ?_
  refine Conv.trans (Conv.app_congr (Conv.beta _ p) (Conv.refl q)) ?_
  change Conv (.app (.lam (Term.iff p.weaken (.var .zero))) q) (Term.iff p q)
  simpa only [Term.instantiate, Term.iff, Term.conj, Term.imp, Term.disj,
    Term.neg, Term.subst_app, Term.subst_and, Term.subst_or, Term.subst_not,
    Term.subst_var, Sub.cons_zero, Term.weaken, Term.subst_rename,
    Sub.compRen_cons_shift, Term.subst_id] using
      (Conv.beta (Term.iff p.weaken (.var .zero)) q)

private theorem logical_coext_body (ρ : RTy) : ∀ {Γ}
    (X Y : ModalComprehensionConcreteSyntax.Term Const Γ ρ),
    Conv (toC (ModalComprehensionConcreteSyntax.Term.coext ρ X Y))
      (.app (.app (.coextR ρ) (toC X)) (toC Y)) := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ X Y
      exact Conv.symm (logical_coext_t (toC X) (toC Y))
  | arr σ ρ ih =>
      intro Γ X Y
      have h := Conv.app_congr (Conv.refl (Term.all σ))
        (Conv.lam_congr (ih (.app X.wk (.var .zero)) (.app Y.wk (.var .zero))))
      have hc : Conv (.app (.app (.coextR (σ ⇒ ρ)) (toC X)) (toC Y))
          (Term.forall' (.app (.app (.coextR ρ)
            (.app (toC X).weaken (.var .zero)))
            (.app (toC Y).weaken (.var .zero)))) :=
        Conv.app_coextR_block [σ] ρ (toC X) (toC Y)
      apply Conv.trans (b := Term.forall' (.app (.app (.coextR ρ)
        (.app (toC X).weaken (.var .zero))) (.app (toC Y).weaken (.var .zero))))
      · simpa only [ModalComprehensionConcreteSyntax.Term.coext,
          toC, toC_wk, toCVar, Term.forall'] using h
      · exact Conv.symm hc

private theorem logical_inclusion_t {Γ}
    (p q : Formula (signature Const) Γ) :
    Conv (.app (.app (.inclR .t) p) q) (Term.imp p q) := by
  refine Conv.trans
    (Conv.app_congr (Conv.app_congr (Conv.delta rfl) (Conv.refl p)) (Conv.refl q)) ?_
  refine Conv.trans (Conv.app_congr (Conv.beta _ p) (Conv.refl q)) ?_
  change Conv (.app (.lam (Term.imp p.weaken (.var .zero))) q) (Term.imp p q)
  simpa only [Term.instantiate, Term.imp, Term.disj, Term.neg,
    Term.subst_app, Term.subst_or, Term.subst_not, Term.subst_var,
    Sub.cons_zero, Term.weaken, Term.subst_rename, Sub.compRen_cons_shift,
    Term.subst_id] using (Conv.beta (Term.imp p.weaken (.var .zero)) q)

private theorem logical_inclusion_body (ρ : RTy) : ∀ {Γ}
    (X Y : ModalComprehensionConcreteSyntax.Term Const Γ ρ),
    Conv (toC (inclusion ρ X Y))
      (.app (.app (.inclR ρ) (toC X)) (toC Y)) := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ X Y
      exact Conv.symm (logical_inclusion_t (toC X) (toC Y))
  | arr σ ρ ih =>
      intro Γ X Y
      have h := Conv.app_congr (Conv.refl (Term.all σ))
        (Conv.lam_congr (ih (.app X.wk (.var .zero)) (.app Y.wk (.var .zero))))
      have hc : Conv (.app (.app (.inclR (σ ⇒ ρ)) (toC X)) (toC Y))
          (Term.forall' (.app (.app (.inclR ρ)
            (.app (toC X).weaken (.var .zero)))
            (.app (toC Y).weaken (.var .zero)))) :=
        Conv.app_inclR_block [σ] ρ (toC X) (toC Y)
      apply Conv.trans (b := Term.forall' (.app (.app (.inclR ρ)
        (.app (toC X).weaken (.var .zero))) (.app (toC Y).weaken (.var .zero))))
      · simpa only [inclusion, toC, toC_wk, toCVar, Term.forall'] using h
      · exact Conv.symm hc

/-- Every independent logical comprehension witness has exactly its
original C meaning, including unsaturated operators at arbitrary type. -/
theorem logicalWitness_eq {ρ : RTy} (o : LogicalOperator ρ) (Γ : Ctx) :
    C.Derivable [] (Term.eq'
      (bodyWitness (o.body (Const := Const) Γ))
      (decodeAtom (Sig := signature Const) o.atom)) := by
  cases o with
  | and =>
      apply logical_close Term.and
      apply logical_close (.app Term.and (.var .zero))
      exact logical_conjunction (.var (.succ .zero)) (.var .zero)
  | or =>
      apply logical_close Term.or
      apply logical_close (.app Term.or (.var .zero))
      exact logical_disjunction (.var (.succ .zero)) (.var .zero)
  | not =>
      apply logical_close Term.not
      exact logical_neg (.var .zero)
  | all σ =>
      apply logical_conv_eq
      exact Conv.trans
        (Conv.lam_congr (Conv.app_congr (Conv.refl _) (Conv.eta (.var .zero))))
        (Conv.eta (.all σ))
  | ex σ =>
      apply logical_conv_eq
      exact Conv.trans
        (Conv.lam_congr (Conv.app_congr (Conv.refl _) (Conv.eta (.var .zero))))
        (Conv.eta (.ex σ))
  | eq σ =>
      apply logical_close (.eq σ)
      apply logical_close (.app (.eq σ) (.var .zero))
      exact Derivable.refl _
  | constR ρ =>
      apply logical_close (.constR ρ)
      exact logical_const_body ρ (.var .zero)
  | negR ρ =>
      apply logical_close (.negR ρ)
      exact logical_unary_body .neg ρ (.var .zero)
  | andR ρ =>
      apply logical_close (.andR ρ)
      apply logical_close (.app (.andR ρ) (.var .zero))
      exact logical_binary_body .and ρ (.var (.succ .zero)) (.var .zero)
  | orR ρ =>
      apply logical_close (.orR ρ)
      apply logical_close (.app (.orR ρ) (.var .zero))
      exact logical_binary_body .or ρ (.var (.succ .zero)) (.var .zero)
  | coextR ρ =>
      apply logical_close (.coextR ρ)
      apply logical_close (.app (.coextR ρ) (.var .zero))
      exact logical_conv_eq (logical_coext_body ρ (.var (.succ .zero)) (.var .zero))
  | boxR ρ =>
      apply logical_close (.boxR ρ)
      exact logical_unary_body .boxEq ρ (.var .zero)
  | inclR ρ =>
      apply logical_close (.inclR ρ)
      apply logical_close (.app (.inclR ρ) (.var .zero))
      exact logical_conv_eq (logical_inclusion_body ρ (.var (.succ .zero)) (.var .zero))

#print axioms logicalWitness_eq

end Classicism.Research.ModalNamedToC
