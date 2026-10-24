import Classicism.Results.Research.RelationalBracketAbstraction
import Classicism.Results.Research.ModalUniformCombinators

/-!
# Interpreting the bracket algorithm by actual comprehension definitions

Original research, misc, 23 October 2026. The five laws of the independent
combinator equality calculus are interpreted by derivations from the five
explicit uniform-body definitions. No arbitrary proof-preservation field
or abstraction-congruence axiom is used.

The definitions below are global named axioms of an extended signature.
This module does not assert their simultaneous conservative availability:
each finite proof still needs finite-name elimination to yield an old-
language theorem. Nor does this establish full contextual C conversion.
-/

namespace Classicism.Research.RelationalBracketInterpretation
open Classicism.Meta (Ty RTy)
open RelationalBracketAbstraction (BasisConst Equal)
open ModalComprehensionConcreteSyntax
open ModalComprehensionRepresentation (UniformRepresents)

abbrev BTerm := RelationalBracketAbstraction.Term

def embedVar : {Γ : Ctx} → {σ : Ty} → Classicism.Meta.Var Γ σ → Var Γ σ
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (embedVar v)

variable {Const : Ty → Type}

def embed : {Γ : Ctx} → {σ : Ty} → BTerm Const Γ σ → Term (BasisConst Const) Γ σ
  | _, _, .var v => .var (embedVar v)
  | _, _, .const c => .const c
  | _, _, .app f a => .app (embed f) (embed a)

/-- Translation commutes with actual argument substitution. This does not
claim that the bracket algorithm itself commutes literally with substitution. -/
theorem embed_inst : {Γ : Ctx} → {σ τ : Ty} →
    (M : BTerm Const (σ :: Γ) τ) → (a : BTerm Const Γ σ) →
    embed (M.inst a) = (embed M).inst (embed a)
  | _, _, _, .var .zero, _ => by
      simp only [RelationalBracketAbstraction.Term.inst,
        RelationalBracketAbstraction.Term.subst, RelationalBracketAbstraction.Sub.cons,
        embed, embedVar, Term.inst, Term.subst, Sub.cons]
  | _, _, _, .var (.succ _), _ => by
      simp only [RelationalBracketAbstraction.Term.inst,
        RelationalBracketAbstraction.Term.subst, RelationalBracketAbstraction.Sub.cons,
        RelationalBracketAbstraction.Sub.id, embed, embedVar,
        Term.inst, Term.subst, Sub.cons, Sub.id]
  | _, _, _, .const _, _ => by
      simp only [RelationalBracketAbstraction.Term.inst,
        RelationalBracketAbstraction.Term.subst, embed, Term.inst, Term.subst]
  | _, _, _, .app f b, a => by
    simpa only [RelationalBracketAbstraction.Term.inst,
      RelationalBracketAbstraction.Term.subst, embed, Term.inst, Term.subst] using
      congr (congrArg Term.app (embed_inst f a)) (embed_inst b a)

/-- Exactly the five uniform definitions, with no conversion or equality
conclusions inserted as extra axioms. -/
inductive NamedAxiom (Const : Ty → Type) :
    (Γ : Ctx) → Formula (BasisConst Const) Γ → Prop
  | I {Γ} (ρ : RTy) : NamedAxiom Const Γ
      (UniformRepresents (CombinatorBody.I ρ Γ) (.const (.I ρ)))
  | K {Γ} (σ : Ty) (ρ : RTy) : NamedAxiom Const Γ
      (UniformRepresents (CombinatorBody.K σ ρ Γ) (.const (.K σ ρ)))
  | S {Γ} (σ : Ty) (τ ρ : RTy) : NamedAxiom Const Γ
      (UniformRepresents (CombinatorBody.S σ τ ρ Γ) (.const (.S σ τ ρ)))
  | C {Γ} (σ τ : Ty) (ρ : RTy) : NamedAxiom Const Γ
      (UniformRepresents (CombinatorBody.C σ τ ρ Γ) (.const (.C σ τ ρ)))
  | W {Γ} (σ : Ty) (ρ : RTy) : NamedAxiom Const Γ
      (UniformRepresents (CombinatorBody.W σ ρ Γ) (.const (.W σ ρ)))

/-- Actual induction on every constructor of combinator equality. The
target derives its five law cases from the comprehension definitions. -/
theorem equal_derives {Γ σ} {a b : BTerm Const Γ σ}
    (h : Equal Const a b) (Δ : List (Formula (BasisConst Const) Γ)) :
    Derives (BasisConst Const) (NamedAxiom Const) Γ Δ (.eq (embed a) (embed b)) := by
  induction h with
  | refl a => exact .eqRefl _
  | symm h ih => exact .eqSymm ih
  | trans h₁ h₂ ih₁ ih₂ => exact .eqTrans ih₁ ih₂
  | app hf ha ihf iha => simpa only [embed] using Derives.eqApp ihf iha
  | lawI a =>
      simpa only [embed] using Derives.uniform_I (Ax := NamedAxiom Const) (Δ := Δ)
        (embed a) (Derives.ax (NamedAxiom.I _))
  | lawK a b =>
      simpa only [embed] using Derives.uniform_K (Ax := NamedAxiom Const) (Δ := Δ)
        (embed a) (embed b) (Derives.ax (NamedAxiom.K _ _))
  | lawS f g a =>
      simpa only [embed] using Derives.uniform_S (Ax := NamedAxiom Const) (Δ := Δ)
        (embed f) (embed g) (embed a) (Derives.ax (NamedAxiom.S _ _ _))
  | lawC f b a =>
      simpa only [embed] using Derives.uniform_C (Ax := NamedAxiom Const) (Δ := Δ)
        (embed f) (embed b) (embed a) (Derives.ax (NamedAxiom.C _ _ _))
  | lawW f a =>
      simpa only [embed] using Derives.uniform_W (Ax := NamedAxiom Const) (Δ := Δ)
        (embed f) (embed a) (Derives.ax (NamedAxiom.W _ _))

/-- Literal beta identity of the implemented bracket abstraction, in the
actual lambda-free calculus with the displayed named definitions. -/
theorem bracket_beta_derives {Γ σ} {ρ : RTy}
    (M : BTerm Const (σ :: Γ) ρ) (a : BTerm Const Γ σ)
    (Δ : List (Formula (BasisConst Const) Γ)) :
    Derives (BasisConst Const) (NamedAxiom Const) Γ Δ
      (.eq (.app (embed M.bracket) (embed a)) ((embed M).inst (embed a))) := by
  have h := equal_derives (RelationalBracketAbstraction.Term.bracket_beta M a) Δ
  simpa only [embed, embed_inst] using h

#print axioms embed_inst
#print axioms equal_derives
#print axioms bracket_beta_derives

end Classicism.Research.RelationalBracketInterpretation
