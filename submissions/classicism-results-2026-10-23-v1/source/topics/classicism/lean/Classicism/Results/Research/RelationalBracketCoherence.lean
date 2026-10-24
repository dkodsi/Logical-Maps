import Classicism.Results.Research.RelationalBracketRenaming
import Classicism.Results.Research.RelationalBracketInterpretation

/-!
# Abstraction congruence and eta from object Intensionality

Original research, misc, 23 October 2026. The five combinator equations
provide beta; the actual calculus's theorem-level zeta supplies abstraction
congruence and eta. Only an equality THEOREM is generalized/necessitated.
Arbitrary local hypotheses are not allowed through that boundary.

These conclusions still use the explicitly named comprehension definitions
of RelationalBracketInterpretation. Finite-name elimination and the full
translation of C derivations are not claimed here.
-/

namespace Classicism.Research.RelationalBracketInterpretation
open Classicism.Meta (Ty RTy Ctx)
open RelationalBracketAbstraction (BasisConst)
open ModalComprehensionConcreteSyntax

variable {Const : Ty → Type}

theorem embed_wk {Γ σ τ} (M : BTerm Const Γ τ) :
    embed (M.wk (σ := σ)) = (embed M).wk := by
  induction M with
  | var v =>
      simp only [RelationalBracketAbstraction.Term.wk,
        RelationalBracketAbstraction.Term.rename, Classicism.Meta.Ren.shift,
        embed, embedVar, Term.wk, Term.rename, Ren.shift]
  | const c =>
      simp only [RelationalBracketAbstraction.Term.wk,
        RelationalBracketAbstraction.Term.rename, embed, Term.wk, Term.rename]
  | app f a ihf iha =>
      simpa only [RelationalBracketAbstraction.Term.wk,
        RelationalBracketAbstraction.Term.rename, embed, Term.wk, Term.rename] using
        congr (congrArg Term.app ihf) iha

theorem bracket_fresh_beta_derives {Γ σ} {ρ : RTy}
    (M : BTerm Const (σ :: Γ) ρ) :
    Derives (BasisConst Const) (NamedAxiom Const) (σ :: Γ) []
      (.eq (.app (embed M.bracket).wk (.var .zero)) (embed M)) := by
  have h := equal_derives (RelationalBracketAbstraction.Term.bracket_fresh_beta M) []
  simpa only [embed, embedVar, embed_wk] using h

/-- Theorem equality of bodies gives literal identity of their compiled
abstractions. This is derived zeta, not a combinator equality constructor. -/
theorem bracket_congruence_derives {Γ σ} {ρ : RTy}
    (M N : BTerm Const (σ :: Γ) ρ)
    (h : Derives (BasisConst Const) (NamedAxiom Const) (σ :: Γ) []
      (.eq (embed M) (embed N))) :
    Derives (BasisConst Const) (NamedAxiom Const) Γ []
      (.eq (embed M.bracket) (embed N.bracket)) := by
  apply (calculus (BasisConst Const) (NamedAxiom Const)).theorem_zeta
  exact .eqTrans (bracket_fresh_beta_derives M)
    (.eqTrans h (.eqSymm (bracket_fresh_beta_derives N)))

/-- Eta identity follows from fresh-argument beta plus derived zeta. -/
theorem bracket_eta_derives {Γ σ} {ρ : RTy}
    (F : BTerm Const Γ (σ ⇒ ρ)) :
    Derives (BasisConst Const) (NamedAxiom Const) Γ []
      (.eq (embed (RelationalBracketAbstraction.Term.app F.wk (.var .zero)).bracket)
        (embed F)) := by
  apply (calculus (BasisConst Const) (NamedAxiom Const)).theorem_zeta
  change Derives (BasisConst Const) (NamedAxiom Const) (σ :: Γ) []
    (.eq (.app (embed (RelationalBracketAbstraction.Term.app F.wk (.var .zero)).bracket).wk
      (.var .zero)) (.app (embed F).wk (.var .zero)))
  have h := bracket_fresh_beta_derives
    (RelationalBracketAbstraction.Term.app F.wk (.var .zero))
  simpa only [embed, embedVar, embed_wk] using h

#print axioms embed_wk
#print axioms bracket_fresh_beta_derives
#print axioms bracket_congruence_derives
#print axioms bracket_eta_derives

end Classicism.Research.RelationalBracketInterpretation
