import Classicism.Results.Research.ActualityCoreApplication
import Classicism.Results.Research.ActualityCoreSubstitution

/-!
# Domain conversion and the core eta identity

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
sections 2--3 (misc, 22 October 2026, unpaginated).

The typing theorem has the finite translated context as its literal list of
object-language hypotheses. The eta result below is for a core function;
full beta/eta preservation of the syntax translation remains separate.
-/

namespace Classicism.Meta.ActualityCoreSyntax

variable {Sig : Signature} {Γ : Ctx}

theorem domain_app_conv (σ : Ty) (w : Formula Sig Γ) (a : Term Sig Γ σ) :
    Conv (.app (domain σ w) a) (member σ w a) := by
  cases σ with
  | e =>
    have h := Conv.beta w.weaken a
    simpa only [Term.instantiate_weaken] using h
  | var _ =>
    have h := Conv.beta w.weaken a
    simpa only [Term.instantiate_weaken] using h
  | rel ρ =>
    have h : Conv (.app (domain (.rel ρ) w) a)
        (Term.conj (w.weaken.instantiate a)
          (Term.leR ρ a ((support ρ w.weaken).instantiate a))) :=
      Conv.beta (Term.conj w.weaken (Term.leR ρ .v0 (support ρ w.weaken))) a
    rw [Term.instantiate_weaken, support_instantiate] at h
    exact h

/-- Every term of the original admitted language translates to a member of
its recursive core domain, under exactly the actual-world hypothesis and
the finite list of core-domain hypotheses for its variables. -/
theorem translate_typing {σ : Ty} (w : Formula Sig Γ) (a : Term Sig Γ σ) :
    C.Derivable (actualWorld w :: context Γ w) (member σ w (translate w a)) := by
  apply translate_member _ w a Derivable.hyp₀
  intro τ v
  exact Derivable.conv (Derivable.hyp (List.mem_cons_of_mem _ (mem_context w v)))
    (domain_app_conv τ w (.var v))

/-- Supported eta expansion is literally equal to the original core object. -/
theorem core_eta (σ : Ty) (ρ : RTy) (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (F : Term Sig Γ (σ ⇒ ρ))
    (hF : C.Derivable Δ (member (σ ⇒ ρ) w F)) :
    C.Derivable Δ (Term.eq'
      (cut (σ ⇒ ρ) w (.lam (.app F.weaken .v0))) F) := by
  have he := member_cut_identity (σ ⇒ ρ) Δ w F hF
  have hc : Conv (cut (σ ⇒ ρ) w (.lam (.app F.weaken .v0)))
      (cut (σ ⇒ ρ) w F) :=
    Conv.app_congr (Conv.refl _) (Conv.eta F)
  exact Derivable.conv he
    (Conv.symm (Conv.app_congr (Conv.app_congr (Conv.refl _) hc) (Conv.refl F)))

end Classicism.Meta.ActualityCoreSyntax

#print axioms Classicism.Meta.ActualityCoreSyntax.translate_typing
#print axioms Classicism.Meta.ActualityCoreSyntax.core_eta
