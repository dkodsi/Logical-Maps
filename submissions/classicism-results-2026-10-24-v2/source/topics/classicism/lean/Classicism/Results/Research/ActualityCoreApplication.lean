import Classicism.Results.Research.ActualityCoreMembership

/-!
# Application in the recursively indexed current core

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
sections 2--3 (misc, 22 October 2026, unpaginated).

The statements below concern genuine C derivations. The arbitrary input
and relational output indices are the existing deep `Ty` and `RTy`. The
application theorem does not posit external function-space closure.
-/

#classicism_derive Classicism.Research.ActualityCore.cut_fixed

namespace Classicism.Meta.ActualityCoreSyntax

variable {Sig : Signature} {Γ : Ctx}

private theorem allE₄β {Ax : AxiomSet Sig} {Δ : List (Formula Sig Γ)}
    {σ τ υ κ : Ty} {b : Formula Sig (κ :: υ :: τ :: σ :: Γ)}
    (h : Derivable Ax Δ (Term.forall' (Term.forall' (Term.forall' (Term.forall' b)))))
    (a₁ : Term Sig Γ σ) (a₂ : Term Sig Γ τ) (a₃ : Term Sig Γ υ) (a₄ : Term Sig Γ κ) :
    Derivable Ax Δ (b.subst (Sub.cons a₄ (Sub.cons a₃ (Sub.cons a₂ (Sub.cons a₁ Sub.id))))) := by
  have h₄ : Derivable Ax Δ
      ((b.subst (Sub.lift (Sub.cons a₃ (Sub.cons a₂ (Sub.cons a₁ Sub.id))))).subst
        (Sub.cons a₄ Sub.id)) :=
    Derivable.allEβ (Derivable.allE₃β h a₁ a₂ a₃) a₄
  rw [Term.subst_subst, Sub.comp_cons_lift] at h₄
  exact h₄

private theorem allE₅β {Ax : AxiomSet Sig} {Δ : List (Formula Sig Γ)}
    {σ τ υ κ μ : Ty} {b : Formula Sig (μ :: κ :: υ :: τ :: σ :: Γ)}
    (h : Derivable Ax Δ (Term.forall' (Term.forall' (Term.forall' (Term.forall' (Term.forall' b))))))
    (a₁ : Term Sig Γ σ) (a₂ : Term Sig Γ τ) (a₃ : Term Sig Γ υ)
    (a₄ : Term Sig Γ κ) (a₅ : Term Sig Γ μ) :
    Derivable Ax Δ (b.subst
      (Sub.cons a₅ (Sub.cons a₄ (Sub.cons a₃ (Sub.cons a₂ (Sub.cons a₁ Sub.id)))))) := by
  have h₅ : Derivable Ax Δ
      ((b.subst (Sub.lift
        (Sub.cons a₄ (Sub.cons a₃ (Sub.cons a₂ (Sub.cons a₁ Sub.id)))))).subst
        (Sub.cons a₅ Sub.id)) :=
    Derivable.allEβ (allE₄β h a₁ a₂ a₃ a₄) a₅
  rw [Term.subst_subst, Sub.comp_cons_lift] at h₅
  exact h₅

def rectangle (σ : Ty) (ρ : RTy) (D : Term Sig Γ (σ ⇒ RTy.t))
    (A : Term Sig Γ ρ) : Term Sig Γ (σ ⇒ ρ) :=
  .lam (.app (.app (.andR ρ)
    (.app (.constR ρ) (.app D.weaken .v0))) A.weaken)

private def expandedOr (σ : Ty) (ρ : RTy) :
    Term Sig Γ ((σ ⇒ ρ) ⇒ (σ ⇒ ρ) ⇒ (σ ⇒ ρ)) :=
  .lam (.lam (.lam (.app (.app (.orR ρ) (.app .v2 .v0)) (.app .v1 .v0))))

theorem support_arr (σ : Ty) (ρ : RTy) (w : Formula Sig Γ) :
    support (σ ⇒ ρ) w = rectangle σ ρ (domain σ w) (support ρ w) := by
  simp only [support, rectangle, Term.weaken, domain_rename, support_rename]

/-- A represented function's section is again a represented core relation. -/
theorem section_memberRel (σ : Ty) (ρ : RTy) (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (D : Term Sig Γ (σ ⇒ RTy.t)) (A : Term Sig Γ ρ)
    (F : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ)
    (hF : C.Derivable Δ (memberRel (σ ⇒ ρ) w (rectangle σ ρ D A) F)) :
    C.Derivable Δ (memberRel ρ w A (.app F a)) := by
  have h := allE₅β (Δ := Δ)
    (C.Derivable.of_minus (Derivable.ofTheorem (C.TheoremMinus.ofPure
      (Classicism.Research.ActualityCore.interpretation_section_rule.derivable ρ σ))))
    w D A F a
  change C.Derivable Δ (Term.imp
    (Term.conj w (Term.eq' (rectangle σ ρ D A)
      (.app (.app (expandedOr σ ρ) F) (rectangle σ ρ D A))))
    (memberRel ρ w A (.app F a))) at h
  have hd : Conv (Term.orR (σ ⇒ ρ) : Term Sig Γ _)
      (expandedOr σ ρ) := Conv.delta (by rfl)
  have ho := Conv.app_congr (Conv.app_congr hd (Conv.refl F))
    (Conv.refl (rectangle σ ρ D A))
  have he := Conv.app_congr (Conv.refl (Term.app (Term.eq (σ ⇒ ρ))
    (rectangle σ ρ D A))) ho
  have hc := Conv.app_congr (Conv.refl (Term.app Term.and w)) he
  exact Derivable.impE h (Derivable.conv hF hc)

theorem application_member (σ : Ty) (ρ : RTy) (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (F : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ)
    (hF : C.Derivable Δ (member (σ ⇒ ρ) w F)) :
    C.Derivable Δ (member ρ w (.app F a)) := by
  apply section_memberRel σ ρ Δ w (domain σ w) (support ρ w) F a
  simpa only [member, support_arr] using hF

theorem member_cut_identity (ρ : RTy) (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (a : Term Sig Γ ρ)
    (ha : C.Derivable Δ (member ρ w a)) :
    C.Derivable Δ (Term.eq' (cut ρ w a) a) := by
  have h := Derivable.allE₂β (Δ := Δ)
    (C.Derivable.of_minus (Derivable.ofTheorem (C.TheoremMinus.ofPure
      (Classicism.Research.ActualityCore.cut_fixed.derivable ρ))))
    (support ρ w) a
  exact Derivable.impE h (Derivable.andE₂ ha)

/-- The normalization inserted by the actual term translation is literally
the identity after applying a core function. No coextension-to-identity axiom
is used here; the already certified cut law discharges it. -/
theorem translate_application (σ : Ty) (ρ : RTy) (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (F : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ)
    (hw : C.Derivable Δ (actualWorld w))
    (hv : ∀ (τ : Ty) (v : Var Γ τ), C.Derivable Δ (member τ w (.var v))) :
    C.Derivable Δ (Term.eq' (translate w (.app F a))
      (.app (translate w F) (translate w a))) :=
  member_cut_identity ρ Δ w _
    (application_member σ ρ Δ w _ _ (translate_member Δ w F hw hv))

end Classicism.Meta.ActualityCoreSyntax

#print axioms Classicism.Meta.ActualityCoreSyntax.application_member
#print axioms Classicism.Meta.ActualityCoreSyntax.translate_application
