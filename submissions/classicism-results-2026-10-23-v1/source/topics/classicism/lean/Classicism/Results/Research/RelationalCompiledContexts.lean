import Classicism.Results.Research.RelationalLambdaCompilation
import Classicism.Syntax.Derivation
import Classicism.Results.Research.ModalClassicalRules
import Classicism.Results.Research.ModalFiniteClassicalDefinitions

/-!
# Actual contextual equality and Subst after bracket compilation

Original research, misc, 23 October 2026. This handles arbitrary raw C
one-hole contexts, including holes under abstractions. Its equivalence
premises have exactly one local hypothesis each. The proof uses theorem
necessitation only after those hypotheses have been discharged.

The final conversion helper isolates the remaining delta obligation; it
is not itself an unconditional certificate of the full C translation.
-/

namespace Classicism.Research.RelationalCompiledContexts
open Classicism.Meta (Ty RTy Ctx Signature)
open RelationalLambdaCompilation (Atoms compile)
open RelationalBracketAbstraction (BasisConst)
open RelationalBracketInterpretation (embed NamedAxiom BTerm)
open ModalComprehensionConcreteSyntax (Derives Axioms calculus)

variable {Sig : Signature}

abbrev TargetConst (Sig : Signature) := BasisConst (Atoms Sig)
abbrev TargetTerm (Sig : Signature) := ModalComprehensionConcreteSyntax.Term (TargetConst Sig)

def translate {Γ : Ctx} {σ : Ty} (M : Classicism.Meta.Term Sig Γ σ) :
    TargetTerm Sig Γ σ := embed (compile M)

def ContainsBasis (Ax : Axioms (TargetConst Sig)) : Prop :=
  ∀ Γ p, NamedAxiom (Atoms Sig) Γ p → Ax Γ p

theorem lift_basis {Ax : Axioms (TargetConst Sig)} (hb : ContainsBasis Ax)
    {Γ Δ p} (h : Derives (TargetConst Sig) (NamedAxiom (Atoms Sig)) Γ Δ p) :
    Derives (TargetConst Sig) Ax Γ Δ p :=
  ModalFreshConstantSyntax.replace_global_axioms (fun Γ p hp => .ax (hb Γ p hp)) h

theorem translate_weaken {Γ : Ctx} {σ τ : Ty}
    (M : Classicism.Meta.Term Sig Γ τ) :
    translate (M.weaken (τ := σ)) = (translate M).wk := by
  simp only [translate, RelationalLambdaCompilation.compile_weaken,
    RelationalBracketInterpretation.embed_wk]

theorem abstraction_identity {Ax : Axioms (TargetConst Sig)}
    (hb : ContainsBasis Ax) {Γ σ} {ρ : RTy}
    {M N : BTerm (Atoms Sig) (σ :: Γ) ρ}
    (h : Derives (TargetConst Sig) Ax (σ :: Γ) [] (.eq (embed M) (embed N))) :
    Derives (TargetConst Sig) Ax Γ [] (.eq (embed M.bracket) (embed N.bracket)) := by
  apply (calculus (TargetConst Sig) Ax).theorem_zeta
  exact Derives.eqTrans
    (lift_basis hb (RelationalBracketInterpretation.bracket_fresh_beta_derives M))
    (Derives.eqTrans h (Derives.eqSymm
      (lift_basis hb (RelationalBracketInterpretation.bracket_fresh_beta_derives N))))

/-- Induction on the actual raw C context, with no assumed lambda
congruence in the target language. -/
theorem hole_identity {Ax : Axioms (TargetConst Sig)} (hb : ContainsBasis Ax)
    {Γ Γ' : Ctx} {σ τ : Ty} (H : Classicism.Meta.Hole Sig Γ σ Γ' τ)
    {a b : Classicism.Meta.Term Sig Γ' τ}
    (h : Derives (TargetConst Sig) Ax Γ' [] (.eq (translate a) (translate b))) :
    Derives (TargetConst Sig) Ax Γ []
      (.eq (translate (H.plug a)) (translate (H.plug b))) := by
  induction H with
  | hole => exact h
  | appL H M ih =>
      simpa only [Classicism.Meta.Hole.plug, translate, compile, embed] using
        Derives.eqApp (ih h) (.eqRefl (translate M))
  | appR F H ih =>
      simpa only [Classicism.Meta.Hole.plug, translate, compile, embed] using
        Derives.eqApp (.eqRefl (translate F)) (ih h)
  | lam H ih => exact abstraction_identity hb (ih h)

/-- The contextual Subst step is proved in the target calculus itself.
The equivalence proofs have no optional premises besides P or Q. -/
theorem contextual_subst {Ax : Axioms (TargetConst Sig)} (hb : ContainsBasis Ax)
    {Γ Γ' : Ctx} {Δ : List (TargetTerm Sig Γ Ty.t)}
    (H : Classicism.Meta.Hole Sig Γ Ty.t Γ' Ty.t)
    {P Q : Classicism.Meta.Formula Sig Γ'}
    (hpq : Derives (TargetConst Sig) Ax Γ' [translate P] (translate Q))
    (hqp : Derives (TargetConst Sig) Ax Γ' [translate Q] (translate P))
    (h : Derives (TargetConst Sig) Ax Γ Δ (translate (H.plug P))) :
    Derives (TargetConst Sig) Ax Γ Δ (translate (H.plug Q)) :=
  .eqTruth (hole_identity hb H
    (ModalClassicalRules.equivalence_identity hpq hqp)).lift h

theorem beta_identity {Ax : Axioms (TargetConst Sig)} (hb : ContainsBasis Ax)
    {Γ σ} {ρ : RTy} (M : Classicism.Meta.Term Sig (σ :: Γ) ρ)
    (a : Classicism.Meta.Term Sig Γ σ) :
    Derives (TargetConst Sig) Ax Γ []
      (.eq (translate (.app (.lam M) a)) (translate (M.instantiate a))) :=
  lift_basis hb (RelationalLambdaCompilation.eqProof_derives (.beta M a))

theorem eta_identity {Ax : Axioms (TargetConst Sig)} (hb : ContainsBasis Ax)
    {Γ σ} {ρ : RTy} (F : Classicism.Meta.Term Sig Γ (σ ⇒ ρ)) :
    Derives (TargetConst Sig) Ax Γ []
      (.eq (translate (.lam (.app F.weaken (.var .zero)))) (translate F)) := by
  have h := lift_basis hb (RelationalBracketInterpretation.bracket_eta_derives (compile F))
  simpa only [translate, compile, RelationalLambdaCompilation.compile_weaken] using h

/-- A separate one-step induction avoids carrying irrelevant endpoints from
an outer equivalence-closure induction through the context cases. -/
theorem step_identity {Ax : Axioms (TargetConst Sig)} (hb : ContainsBasis Ax)
    (delta : ∀ {Γ σ} {a b : Classicism.Meta.Term Sig Γ σ},
      a.unfoldR = some b → Derives (TargetConst Sig) Ax Γ []
        (.eq (translate a) (translate b)))
    {Γ σ} {a b : Classicism.Meta.Term Sig Γ σ} (h : Classicism.Meta.BetaEtaStep a b) :
    Derives (TargetConst Sig) Ax Γ [] (.eq (translate a) (translate b)) := by
  induction h with
  | here h =>
      rcases h with hβ | hη | hδ
      · cases hβ
        exact beta_identity hb _ _
      · cases hη with
        | intro F => exact eta_identity hb F
      · exact delta hδ
  | appL _ ih =>
      simp only [translate, compile, embed]
      exact Derives.eqApp ih (.eqRefl _)
  | appR _ ih =>
      simp only [translate, compile, embed]
      exact Derives.eqApp (.eqRefl _) ih
  | lam _ ih => exact abstraction_identity hb ih

/-- Structural closure of the ACTUAL beta/eta/delta conversion relation.
The separate delta premise must be discharged by explicit logical
definitions before this helper can yield the full reconstruction theorem. -/
theorem conversion_identity {Ax : Axioms (TargetConst Sig)} (hb : ContainsBasis Ax)
    (delta : ∀ {Γ σ} {a b : Classicism.Meta.Term Sig Γ σ},
      a.unfoldR = some b → Derives (TargetConst Sig) Ax Γ []
        (.eq (translate a) (translate b)))
    {Γ σ} {a b : Classicism.Meta.Term Sig Γ σ} (h : Classicism.Meta.Conv a b) :
    Derives (TargetConst Sig) Ax Γ [] (.eq (translate a) (translate b)) := by
  induction h with
  | refl a => exact .eqRefl _
  | symm _ ih => exact .eqSymm ih
  | trans _ _ ih₁ ih₂ => exact .eqTrans ih₁ ih₂
  | rel hs => exact step_identity hb delta hs

#print axioms hole_identity
#print axioms contextual_subst
#print axioms beta_identity
#print axioms eta_identity
#print axioms conversion_identity

end Classicism.Research.RelationalCompiledContexts
