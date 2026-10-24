import Classicism.Results.Research.ModalConcreteToCSyntax
import Classicism.Syntax.Entailment

/-!
# Direct C derivations for the lambda-free modal rules

Original research, misc, 23 October 2026. These are derivation trees in the
existing `Meta.C.Derivable`, not semantic arguments or an abstract rule interface.
Intensionality is proved by conditional masks and theorem-only Subst under
abstraction. No local hypothesis is lifted through abstraction or necessitated.
-/

namespace Classicism.Research.ModalConcreteToC
open Classicism.Meta

variable {Const : Ty → Type}

theorem c_equivalence {Γ} {p q : Formula (signature Const) Γ}
    (hpq : C.Derivable [p] q) (hqp : C.Derivable [q] p) :
    C.Derivable [] (Term.eq' p q) :=
  Classicism.Meta.Derivable.subst (P := p) (Q := q) (Hole.appR (.app (.eq _) p) .hole)
    (Classicism.Meta.Derivable.mono (fun _ h => ⟨h, h⟩) hpq)
    (Classicism.Meta.Derivable.mono (fun _ h => ⟨h, h⟩) hqp) (Classicism.Meta.Derivable.refl p)

theorem c_nec {Γ} {p : Formula (signature Const) Γ}
    (h : C.Derivable [] p) : C.Derivable [] (Term.box p) :=
  Classicism.Meta.Derivable.eqSymm (c_equivalence (Classicism.Meta.Derivable.weaken₁ h) Classicism.Meta.Derivable.top)

theorem c_lam_identity {Γ σ} {ρ : RTy} {a b : Term (signature Const) (σ :: Γ) ρ}
    (h : C.Derivable [] (Term.eq' a b)) :
    C.Derivable [] (Term.eq' (.lam a) (.lam b)) :=
  Classicism.Meta.Derivable.substEq ρ (Hole.appR (.app (.eq _) (.lam a)) (.lam .hole))
    (Classicism.Meta.Derivable.mono (fun _ h => ⟨h, h⟩) h) (Classicism.Meta.Derivable.refl (.lam a))

theorem c_K {Γ Δ} {p q : Formula (signature Const) Γ}
    (hpq : C.Derivable Δ (Term.box (Term.imp p q)))
    (hp : C.Derivable Δ (Term.box p)) : C.Derivable Δ (Term.box q) := by
  have ht : C.Derivable [] (Term.eq' (Term.imp Term.top q) q) :=
    c_equivalence (Classicism.Meta.Derivable.impE Classicism.Meta.Derivable.hyp₀ Classicism.Meta.Derivable.top) (Classicism.Meta.Derivable.impI (Classicism.Meta.Derivable.hyp (by simp)))
  have he := Classicism.Meta.Derivable.eqCongrβ (Term.imp (.var .zero) q.weaken) hp
  have he' : C.Derivable Δ (Term.eq' (Term.imp p q) (Term.imp Term.top q)) := by
    simpa only [Term.instantiate, Term.imp, Term.disj, Term.neg,
      Term.subst_app, Term.subst_not, Term.subst_or, Term.subst_var,
      Sub.cons_zero, Term.subst_rename, Sub.compRen_cons_shift, Term.subst_id] using he
  exact Classicism.Meta.Derivable.eqTrans (Classicism.Meta.Derivable.eqSymm (Classicism.Meta.Derivable.weaken ht (List.nil_subset _)))
    (Classicism.Meta.Derivable.eqTrans (Classicism.Meta.Derivable.eqSymm he') hpq)

theorem c_subst_weaken {Γ Θ σ τ} (s : Sub (signature Const) Γ Θ)
    (a : Term (signature Const) Γ τ) :
    a.weaken.subst (Sub.lift (σ := σ) s) = (a.subst s).weaken := by
  simp only [Term.weaken, Term.subst_rename, Term.rename_subst]
  rfl

theorem coextC_subst (ρ : RTy) : ∀ {Γ Θ}
    (s : Sub (signature Const) Γ Θ) (a b : Term (signature Const) Γ ρ),
    (coextC ρ a b).subst s = coextC ρ (a.subst s) (b.subst s) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [coextC, Term.forall', Term.subst_app, Term.subst_all,
        Term.subst_lam, ih, c_subst_weaken, Term.subst_var, Sub.lift_zero]

theorem c_fresh_inst {Γ σ τ} (p : Term (signature Const) (σ :: Γ) τ) :
    (p.rename (Ren.lift (Ren.shift (σ := σ)))).instantiate (.var .zero) = p := by
  rw [Term.instantiate, Term.subst_rename]
  have hs : Sub.compRen (Sub.cons (Term.var (Sig := signature Const)
      (Var.zero (Γ := Γ) (σ := σ))) Sub.id)
      (Ren.lift (Ren.shift (σ := σ))) = (Sub.id : Sub (signature Const) (σ :: Γ) (σ :: Γ)) := by
    funext τ v
    cases v <;> rfl
  rw [hs, Term.subst_id]

theorem c_all_fresh {Γ Δ σ} {p : Formula (signature Const) (σ :: Γ)}
    (h : C.Derivable Δ (Term.forall' p)) :
    C.Derivable (Hyps.weaken Δ) p := by
  have h' : C.Derivable (Hyps.weaken Δ)
      ((p.rename (Ren.lift (Ren.shift (σ := σ)))).instantiate (.var .zero)) :=
    Classicism.Meta.Derivable.allEβ
      (Classicism.Meta.Derivable.rename (Ren.shift (σ := σ)) h) (.var .zero)
  rw [c_fresh_inst] at h'
  exact h'

/-- A relation intersected pointwise with one proposition. -/
def maskC : (ρ : RTy) → {Γ : Ctx} → Formula (signature Const) Γ →
    Term (signature Const) Γ ρ → Term (signature Const) Γ ρ
  | .t, _, p, a => Term.conj p a
  | .arr σ ρ, _, p, a => .lam (maskC ρ p.weaken (.app a.weaken (.var .zero)))

theorem maskC_subst (ρ : RTy) : ∀ {Γ Θ}
    (s : Sub (signature Const) Γ Θ) (p : Formula (signature Const) Γ)
    (a : Term (signature Const) Γ ρ),
    (maskC ρ p a).subst s = maskC ρ (p.subst s) (a.subst s) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [maskC, Term.subst_lam, ih, c_subst_weaken,
        Term.subst_app, Term.subst_var, Sub.lift_zero]

theorem maskC_congr {Γ Δ} (ρ : RTy) {p q : Formula (signature Const) Γ}
    (a : Term (signature Const) Γ ρ) (h : C.Derivable Δ (Term.eq' p q)) :
    C.Derivable Δ (Term.eq' (maskC ρ p a) (maskC ρ q a)) := by
  have h' := Classicism.Meta.Derivable.eqCongrβ (maskC ρ (.var .zero) a.weaken) h
  simpa only [Term.instantiate, maskC_subst, Term.subst_var, Sub.cons_zero,
    Term.subst_rename, Sub.compRen_cons_shift, Term.subst_id] using h'

theorem maskC_top (ρ : RTy) : ∀ {Γ} (a : Term (signature Const) Γ ρ),
    C.Derivable [] (Term.eq' (maskC ρ Term.top a) a) := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ a
      exact c_equivalence (Classicism.Meta.Derivable.andE₂ Classicism.Meta.Derivable.hyp₀) (Classicism.Meta.Derivable.andI Classicism.Meta.Derivable.top Classicism.Meta.Derivable.hyp₀)
  | arr σ ρ ih =>
      intro Γ a
      have h := c_lam_identity (ih (.app a.weaken (.var .zero)))
      exact Classicism.Meta.Derivable.conv h (Conv.app_congr (Conv.refl _) (Conv.eta a))

/-- Crucially, only the single condition P is used to establish coextension.
The conclusion is a theorem before abstraction congruence is applied. -/
theorem maskC_coext (ρ : RTy) : ∀ {Γ} {p : Formula (signature Const) Γ}
    {a b : Term (signature Const) Γ ρ},
    C.Derivable [p] (coextC ρ a b) →
    C.Derivable [] (Term.eq' (maskC ρ p a) (maskC ρ p b)) := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ p a b h
      have hab : C.Derivable [] (Term.imp p (Term.iff a b)) := Classicism.Meta.Derivable.impI h
      apply c_equivalence
      · have hp : C.Derivable [Term.conj p a] p := Classicism.Meta.Derivable.andE₁ Classicism.Meta.Derivable.hyp₀
        have hi := Classicism.Meta.Derivable.impE (Classicism.Meta.Derivable.weaken hab (List.nil_subset _)) hp
        exact Classicism.Meta.Derivable.andI hp (Classicism.Meta.Derivable.iffE₁ hi (Classicism.Meta.Derivable.andE₂ Classicism.Meta.Derivable.hyp₀))
      · have hp : C.Derivable [Term.conj p b] p := Classicism.Meta.Derivable.andE₁ Classicism.Meta.Derivable.hyp₀
        have hi := Classicism.Meta.Derivable.impE (Classicism.Meta.Derivable.weaken hab (List.nil_subset _)) hp
        exact Classicism.Meta.Derivable.andI hp (Classicism.Meta.Derivable.iffE₂ hi (Classicism.Meta.Derivable.andE₂ Classicism.Meta.Derivable.hyp₀))
  | arr σ ρ ih =>
      intro Γ p a b h
      exact c_lam_identity (ih (c_all_fresh h))

/-- All-type Intensionality derived inside the existing C calculus. -/
theorem c_intensionality {Γ Δ} (ρ : RTy) (a b : Term (signature Const) Γ ρ)
    (h : C.Derivable Δ (Term.box (coextC ρ a b))) :
    C.Derivable Δ (Term.eq' a b) := by
  have hab := maskC_coext ρ (a := a) (b := b) Classicism.Meta.Derivable.hyp₀
  have ha := maskC_congr ρ a h
  have hb := maskC_congr ρ b h
  have hat := Classicism.Meta.Derivable.weaken (maskC_top ρ a) (List.nil_subset Δ)
  have hbt := Classicism.Meta.Derivable.weaken (maskC_top ρ b) (List.nil_subset Δ)
  exact Classicism.Meta.Derivable.eqTrans (Classicism.Meta.Derivable.eqSymm (Classicism.Meta.Derivable.eqTrans ha hat))
    (Classicism.Meta.Derivable.eqTrans (Classicism.Meta.Derivable.weaken hab (List.nil_subset Δ)) (Classicism.Meta.Derivable.eqTrans hb hbt))

#print axioms c_nec
#print axioms c_K
#print axioms c_intensionality

end Classicism.Research.ModalConcreteToC
