import Classicism.Results.Research.ModalComprehensionConcreteCalculus

/-!
# Equality in admitted lambda-free term contexts

Original research, misc, 23 October 2026. These are actual applications of
object Leibniz substitution. They permit optional local premises and do
not infer equality beneath reconstructed abstractions from local premises.
-/

namespace Classicism.Research.ModalNativeCongruence
open Classicism.Meta (Ty RTy)
open ModalComprehensionConcreteSyntax

variable {Const : Ty → Type} {Ax : Axioms Const}

private theorem subst_cons_wk {Γ σ τ} (M : Term Const Γ τ) (a : Term Const Γ σ) :
    M.wk.subst (Sub.cons a Sub.id) = M := Term.inst_wk M a

theorem context {Γ Δ σ τ} (M : Term Const (σ :: Γ) τ)
    {a b : Term Const Γ σ} (h : Derives Const Ax Γ Δ (.eq a b)) :
    Derives Const Ax Γ Δ (.eq (M.inst a) (M.inst b)) := by
  have h₀ : Derives Const Ax Γ Δ ((Term.eq (M.inst a).wk M).inst a) := by
    change Derives Const Ax Γ Δ (.eq ((M.inst a).wk.inst a) (M.inst a))
    rw [Term.inst_wk]
    exact .eqRefl _
  have h₁ := Derives.eqSubst (Term.eq (M.inst a).wk M) a b h h₀
  change Derives Const Ax Γ Δ (.eq ((M.inst a).wk.inst b) (M.inst b)) at h₁
  simpa only [Term.inst_wk] using h₁

theorem imp_identity {Γ Δ} {p p' q q' : Formula Const Γ}
    (hp : Derives Const Ax Γ Δ (.eq p p'))
    (hq : Derives Const Ax Γ Δ (.eq q q')) :
    Derives Const Ax Γ Δ (.eq (.imp p q) (.imp p' q')) := by
  have h₁ := context (Term.imp (.var .zero) q.wk) hp
  have h₂ := context (Term.imp p'.wk (.var .zero)) hq
  have h₁' : Derives Const Ax Γ Δ (.eq (.imp p q) (.imp p' q)) := by
    simpa only [Term.inst, Term.subst, Sub.cons, subst_cons_wk] using h₁
  have h₂' : Derives Const Ax Γ Δ (.eq (.imp p' q) (.imp p' q')) := by
    simpa only [Term.inst, Term.subst, Sub.cons, subst_cons_wk] using h₂
  exact .eqTrans h₁' h₂'

theorem iff_identity {Γ Δ} {p p' q q' : Formula Const Γ}
    (hp : Derives Const Ax Γ Δ (.eq p p'))
    (hq : Derives Const Ax Γ Δ (.eq q q')) :
    Derives Const Ax Γ Δ (.eq (.iff p q) (.iff p' q')) := by
  have h₁ := context (Term.iff (.var .zero) q.wk) hp
  have h₂ := context (Term.iff p'.wk (.var .zero)) hq
  have h₁' : Derives Const Ax Γ Δ (.eq (.iff p q) (.iff p' q)) := by
    simpa only [Term.inst, Term.subst, Sub.cons, subst_cons_wk] using h₁
  have h₂' : Derives Const Ax Γ Δ (.eq (.iff p' q) (.iff p' q')) := by
    simpa only [Term.inst, Term.subst, Sub.cons, subst_cons_wk] using h₂
  exact .eqTrans h₁' h₂'

theorem equality_identity {Γ Δ σ} {a a' b b' : Term Const Γ σ}
    (ha : Derives Const Ax Γ Δ (.eq a a'))
    (hb : Derives Const Ax Γ Δ (.eq b b')) :
    Derives Const Ax Γ Δ (.eq (.eq a b) (.eq a' b')) := by
  have h₁ := context (Term.eq (.var .zero) b.wk) ha
  have h₂ := context (Term.eq a'.wk (.var .zero)) hb
  have h₁' : Derives Const Ax Γ Δ (.eq (.eq a b) (.eq a' b)) := by
    simpa only [Term.inst, Term.subst, Sub.cons, subst_cons_wk] using h₁
  have h₂' : Derives Const Ax Γ Δ (.eq (.eq a' b) (.eq a' b')) := by
    simpa only [Term.inst, Term.subst, Sub.cons, subst_cons_wk] using h₂
  exact .eqTrans h₁' h₂'

#print axioms context
#print axioms imp_identity
#print axioms iff_identity
#print axioms equality_identity

end Classicism.Research.ModalNativeCongruence
