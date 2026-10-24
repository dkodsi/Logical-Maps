import Classicism.Results.Research.ActualityCoreSyntax
import Classicism.Results.Research.ActualityCoreInterpretationRules
import Classicism.Syntax.Pure

/-!
# Deep local-domain membership rules

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
sections 2--3 (misc, 22 October 2026, unpaginated).

These statements are actual object-language derivations at arbitrary contexts
and signatures. Their premises are derivations, rather than ambient Lean
truth assumptions. This module starts the domain-membership induction; it
does not assert the full term interpretation before that induction is closed.
-/

namespace Classicism.Meta.ActualityCoreSyntax

variable {Sig : Signature} {Γ : Ctx}

def actualWorld (w : Formula Sig Γ) : Formula Sig Γ :=
  Term.conj w (Term.forall' (Term.imp .v0 (Term.leR .t w.weaken .v0)))

def memberRel (ρ : RTy) (w : Formula Sig Γ) (A a : Term Sig Γ ρ) :
    Formula Sig Γ := Term.conj w (Term.leR ρ a A)

def member (σ : Ty) (w : Formula Sig Γ) (a : Term Sig Γ σ) : Formula Sig Γ :=
  match σ with
  | .e => w
  | .var _ => w
  | .rel ρ => memberRel ρ w (support ρ w) a

/-- Instantiate the certified cut rule with actual deep-language terms. -/
theorem cut_memberRel (ρ : RTy) (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (A a : Term Sig Γ ρ)
    (hw : C.Derivable Δ (actualWorld w)) :
    C.Derivable Δ (memberRel ρ w A (.app (.app (.andR ρ) A) a)) := by
  have h := Derivable.allE₃β
    (C.Derivable.of_minus (Derivable.ofTheorem (C.TheoremMinus.ofPure
      (Classicism.Research.ActualityCore.interpretation_cut_rule.derivable ρ))))
    w A a
  exact Derivable.impE h hw

theorem cut_member (ρ : RTy) (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (a : Term Sig Γ ρ)
    (hw : C.Derivable Δ (actualWorld w)) :
    C.Derivable Δ (member ρ w (cut ρ w a)) :=
  cut_memberRel ρ Δ w (support ρ w) a hw

theorem normalize_member (σ : Ty) (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (a : Term Sig Γ σ)
    (hw : C.Derivable Δ (actualWorld w)) :
    C.Derivable Δ (member σ w (normalize σ w a)) := by
  cases σ with
  | e => exact Derivable.andEL hw
  | var _ => exact Derivable.andEL hw
  | rel ρ => exact cut_member ρ Δ w a hw

/-- Every translated term lies in its recursive core domain, from the actual
world premise and the membership of its free variables. This is a theorem
about the complete existing `Term` datatype, at arbitrary contexts/signatures.
The normalization of application outputs makes the constructor proof local;
it does not discharge application preservation or beta/eta conversion. -/
theorem translate_member {σ : Ty} (Δ : List (Formula Sig Γ))
    (w : Formula Sig Γ) (a : Term Sig Γ σ)
    (hw : C.Derivable Δ (actualWorld w))
    (hv : ∀ (τ : Ty) (v : Var Γ τ),
      C.Derivable Δ (member τ w (.var v))) :
    C.Derivable Δ (member σ w (translate w a)) := by
  cases a with
  | var v => exact hv _ v
  | const c => exact normalize_member _ Δ w (.const c) hw
  | app _ _ => exact cut_member _ Δ w _ hw
  | lam _ => exact cut_member _ Δ w _ hw
  | and => exact cut_member _ Δ w _ hw
  | or => exact cut_member _ Δ w _ hw
  | not => exact cut_member _ Δ w _ hw
  | all _ => exact cut_member _ Δ w _ hw
  | ex _ => exact cut_member _ Δ w _ hw
  | eq _ => exact cut_member _ Δ w _ hw
  | constR _ => exact cut_member _ Δ w _ hw
  | negR _ => exact cut_member _ Δ w _ hw
  | andR _ => exact cut_member _ Δ w _ hw
  | orR _ => exact cut_member _ Δ w _ hw
  | coextR _ => exact cut_member _ Δ w _ hw
  | inclR _ => exact cut_member _ Δ w _ hw
  | boxR _ => exact cut_member _ Δ w _ hw

end Classicism.Meta.ActualityCoreSyntax
