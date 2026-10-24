import Classicism.Results.Research.ActualityCoreSyntax

/-!
# Substitution in recursive local domains

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
sections 2--3 (misc, 22 October 2026, unpaginated).

These are syntactic substitution identities for the domain predicates and
their supports. They are distinct from the harder theorem that translation
preserves substitution of interpreted terms.
-/

namespace Classicism.Meta.ActualityCoreSyntax

variable {Sig : Signature}

theorem subst_weaken {Γ Δ : Ctx} {σ τ : Ty}
    (s : Sub Sig Γ Δ) (a : Term Sig Γ σ) :
    (a.weaken (τ := τ)).subst (Sub.lift s) = (a.subst s).weaken := by
  simp only [Term.weaken, Term.subst_rename, Term.rename_subst]
  rfl

mutual
  theorem domain_subst (σ : Ty) {Γ Δ : Ctx}
      (w : Formula Sig Γ) (s : Sub Sig Γ Δ) :
      (domain σ w).subst s = domain σ (w.subst s) := by
    cases σ with
    | e => simp only [domain, Term.subst_lam, subst_weaken]
    | var _ => simp only [domain, Term.subst_lam, subst_weaken]
    | rel ρ =>
      simp only [domain, Term.conj, Term.leR, Term.eq', Term.subst_lam,
        Term.subst_app, Term.subst_and, Term.subst_eq, Term.subst_orR,
        Term.subst_var, Sub.lift_zero, subst_weaken, support_subst ρ]

  theorem support_subst (ρ : RTy) {Γ Δ : Ctx}
      (w : Formula Sig Γ) (s : Sub Sig Γ Δ) :
      (support ρ w).subst s = support ρ (w.subst s) := by
    cases ρ with
    | t => rfl
    | arr σ τ =>
      simp only [support, Term.subst_lam, Term.subst_app,
        Term.subst_andR, Term.subst_constR, Term.subst_var,
        Sub.lift_zero, domain_subst σ, support_subst τ, subst_weaken]
end

theorem support_instantiate (ρ : RTy) {Γ : Ctx} {σ : Ty}
    (w : Formula Sig Γ) (a : Term Sig Γ σ) :
    (support ρ w.weaken).instantiate a = support ρ w := by
  rw [Term.instantiate, support_subst]
  exact congrArg (support ρ) (Term.instantiate_weaken w a)

theorem domain_instantiate (σ : Ty) {Γ : Ctx} {τ : Ty}
    (w : Formula Sig Γ) (a : Term Sig Γ τ) :
    (domain σ w.weaken).instantiate a = domain σ w := by
  rw [Term.instantiate, domain_subst]
  exact congrArg (domain σ) (Term.instantiate_weaken w a)

end Classicism.Meta.ActualityCoreSyntax
