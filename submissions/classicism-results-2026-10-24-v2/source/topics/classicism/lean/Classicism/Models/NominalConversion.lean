import Classicism.Models.NominalSubstitution

/-!
# Conversion and holes in the supported hierarchy

The beta/eta/delta rules and arbitrary typed one-hole contexts preserve the
actual supported denotations. The box delta case uses the proved interpretation
of the syntactic top term; it does not replace box with pointwise truth.

Source: nominal-choice-classification-20261022.md §2, original local research,
unpaginated, misc. These interface proofs are new; uncompiled candidate.
-/

namespace Classicism.Meta.Nominal.Hierarchy
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}
variable (W : Nom A I) {Sig : Signature} (C : FixedConstants W Sig)

theorem beta_denote {Γ σ} {a b : Term Sig Γ σ} (h : Beta a b) (η : env W Γ) :
    (denote W C a).fn η = (denote W C b).fn η := by
  cases h with
  | intro b a =>
    rw [denote_app, denote_lam, denote_instantiate]

theorem eta_denote {Γ σ} {a b : Term Sig Γ σ} (h : Eta a b) (η : env W Γ) :
    (denote W C a).fn η = (denote W C b).fn η := by
  cases h with
  | intro f =>
    apply Subtype.ext
    funext x
    rw [denote_lam, denote_app, denote_weaken]
    rfl

theorem delta_denote : ∀ {Γ σ} {a b : Term Sig Γ σ}, Delta a b →
    ∀ η : env W Γ, (denote W C a).fn η = (denote W C b).fn η
  | _, _, .constR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .negR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .andR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .orR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .coextR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .inclR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .boxR (.arr _ _), _, h, _ => by cases h; rfl
  | _, _, .boxR .t, _, h, η => by
    cases h
    apply Subtype.ext
    funext p
    apply Subtype.ext
    funext w
    change (p = truthConst W True) =
      (p = (denote W C (Term.top : Formula Sig (Ty.t :: _))).fn (p, η))
    rw [denote_top]
  | _, _, .var _, _, h, _ | _, _, .const _, _, h, _ | _, _, .app _ _, _, h, _
  | _, _, .lam _, _, h, _ | _, _, .and, _, h, _ | _, _, .or, _, h, _
  | _, _, .not, _, h, _ | _, _, .all _, _, h, _ | _, _, .ex _, _, h, _
  | _, _, .eq _, _, h, _ => nomatch h

theorem step_denote
    {R : ∀ {Γ σ}, Term Sig Γ σ → Term Sig Γ σ → Prop}
    (hR : ∀ {Γ σ} {a b : Term Sig Γ σ}, R a b →
      ∀ η : env W Γ, (denote W C a).fn η = (denote W C b).fn η) :
    ∀ {Γ σ} {a b : Term Sig Γ σ}, Step R a b →
      ∀ η : env W Γ, (denote W C a).fn η = (denote W C b).fn η
  | _, _, _, _, .here h, η => hR h η
  | _, _, _, _, .appL h, η => by
    simp only [denote_app, step_denote hR h η] <;> rfl
  | _, _, _, _, .appR h, η => by
    simp only [denote_app, step_denote hR h η] <;> rfl
  | _, _, _, _, .lam h, η => by
    apply Subtype.ext
    funext x
    simp only [denote_lam, step_denote hR h (x, η)] <;> rfl

theorem conv_denote {Γ σ} {a b : Term Sig Γ σ} (h : a ≡ b) (η : env W Γ) :
    (denote W C a).fn η = (denote W C b).fn η := by
  induction h with
  | rel h =>
    exact step_denote W C (fun h η => h.elim (fun h => beta_denote W C h η)
      (fun h => h.elim (fun h => eta_denote W C h η) (fun h => delta_denote W C h η))) h η
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem hole_denote : ∀ {Γ Γ' σ τ} (K : Hole Sig Γ σ Γ' τ) {a b : Term Sig Γ' τ},
    (∀ η', (denote W C a).fn η' = (denote W C b).fn η') →
    ∀ η : env W Γ, (denote W C (K.plug a)).fn η = (denote W C (K.plug b)).fn η
  | _, _, _, _, .hole, _, _, h, η => h η
  | _, _, _, _, .appL K _, _, _, h, η => by
    simp only [Hole.plug, denote_app, hole_denote K h η] <;> rfl
  | _, _, _, _, .appR _ K, _, _, h, η => by
    simp only [Hole.plug, denote_app, hole_denote K h η] <;> rfl
  | _, _, _, _, .lam K, _, _, h, η => by
    apply Subtype.ext
    funext x
    simp only [Hole.plug, denote_lam, hole_denote K h (x, η)] <;> rfl

end
end Classicism.Meta.Nominal.Hierarchy
