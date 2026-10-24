import Classicism.Results.Research.RelationalBracketCoherence

/-!
# Substitution coherence of bracket abstraction as object identity

Original research, misc, 23 October 2026. An old variable can be replaced
by a composite expression, changing K into an S expression, so the two
compiled terms need not be literally identical syntax. Their fresh-argument
values are nevertheless equal by the proved combinator beta law. Actual
theorem-level Intensionality then gives the required object identity.

As in the imported interpretation, named SC definitions are explicit
global axioms. Their finite erasure and full C transport remain separate.
-/

namespace Classicism.Research.RelationalBracketAbstraction
open Classicism.Meta (Ty RTy Ctx Var Ren)

namespace Sub

def lift (s : Sub Const Γ Δ) : Sub Const (σ :: Γ) (σ :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => (s _ v).wk

end Sub

namespace Term
variable {Const : Ty → Type}

theorem rename_subst {Γ Δ Θ σ} (r : Ren Δ Θ) (s : Sub Const Γ Δ)
    (M : Term Const Γ σ) :
    (M.subst s).rename r = M.subst (fun τ v => (s τ v).rename r) := by
  induction M <;> simp_all only [subst, rename]

theorem subst_wk {Γ Δ σ τ} (s : Sub Const Γ Δ) (M : Term Const Γ τ) :
    (M.wk (σ := σ)).subst (Sub.lift s) = (M.subst s).wk := by
  simp only [wk, subst_rename, rename_subst]
  rfl

end Term
end Classicism.Research.RelationalBracketAbstraction

namespace Classicism.Research.RelationalBracketInterpretation
open Classicism.Meta (Ty RTy Ctx)
open RelationalBracketAbstraction (BasisConst)
open ModalComprehensionConcreteSyntax

variable {Const : Ty → Type}

/-- The coherence statement uses literal object equality, proved from
fresh-argument beta and theorem zeta. No syntactic substitution-commutation
axiom for bracket abstraction is postulated. -/
theorem bracket_substitution_derives {Γ Θ σ} {ρ : RTy}
    (s : RelationalBracketAbstraction.Sub Const Γ Θ)
    (M : BTerm Const (σ :: Γ) ρ) :
    Derives (BasisConst Const) (NamedAxiom Const) Θ []
      (.eq (embed (M.subst (RelationalBracketAbstraction.Sub.lift s)).bracket)
        (embed (M.bracket.subst s))) := by
  apply (calculus (BasisConst Const) (NamedAxiom Const)).theorem_zeta
  have raw := RelationalBracketAbstraction.Equal.subst
    (RelationalBracketAbstraction.Sub.lift s)
    (RelationalBracketAbstraction.Term.bracket_fresh_beta M)
  have right := equal_derives raw []
  have hr : Derives (BasisConst Const) (NamedAxiom Const) (σ :: Θ) []
      (.eq (.app (embed (M.bracket.subst s)).wk (.var .zero))
        (embed (M.subst (RelationalBracketAbstraction.Sub.lift s)))) := by
    simpa only [RelationalBracketAbstraction.Term.subst,
      RelationalBracketAbstraction.Sub.lift,
      RelationalBracketAbstraction.Term.subst_wk, embed, embedVar, embed_wk] using right
  exact .eqTrans
    (bracket_fresh_beta_derives (M.subst (RelationalBracketAbstraction.Sub.lift s)))
    (.eqSymm hr)

#print axioms bracket_substitution_derives

end Classicism.Research.RelationalBracketInterpretation
