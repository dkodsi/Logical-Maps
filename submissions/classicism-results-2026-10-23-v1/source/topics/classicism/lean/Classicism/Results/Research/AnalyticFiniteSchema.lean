import Classicism.Results.Research.AnalyticPowerVocabulary
import Classicism.Results.Research.AnalyticFinitePacking
import Classicism.Syntax.Pure

/-!
# C5 and necessary rigid comprehension give the full finite analytic schema

For every admitted closed type and every positive finite arity bound, possible
real structure implies one actual rigid, necessarily real structure with all
its internal represented powers through that bound. The arity bound and lists
below are indices of syntax, not new sorts or quantifiers of the object language.

The source is Zachary Goodsell / Claude Fable 5.1 (Anthropic), 23 October 2026,
`c5-and-necessary-rigid-comprehension-imply-second-order-analytic-necessitism`,
unpaginated, after the S5 part of Andrew Bacon, Corollary 5.1, draft 9 October
2025. This formal transcription uses the user-approved nonempty completeness
clause. No Atomicity or external powerset assumption is added.
-/

noncomputable section

namespace Classicism.Meta.Analytic

open AxiomSet

def powerTypes (σ : Ty) : List Nat → List Ty
  | [] => []
  | k :: ks => (relArity σ k ⇒ RTy.t) :: powerTypes σ ks

def powerPredicates (σ : Ty) {Γ : Ctx}
    (X : Term Signature.pure Γ (σ ⇒ RTy.t)) :
    (ks : List Nat) → Predicates Signature.pure Γ (powerTypes σ ks)
  | [] => .nil
  | k :: ks => .cons (represented (relArity σ k) (domain σ k X).weaken Term.v0)
      (powerPredicates σ X ks)

theorem powerPredicates_exist (σ : Ty) (hσ : σ.Closed) {Γ : Ctx}
    {Δ : List (Formula Signature.pure Γ)} (X : Term Signature.pure Γ (σ ⇒ RTy.t))
    (hX : Derivable Ax Δ (persist (σ ⇒ RTy.t) X)) :
    (ks : List Nat) → Predicates.AllExistentials (Ax := Ax) Δ (powerPredicates σ X ks)
  | [] => trivial
  | k :: ks => ⟨tuple_hasPower σ hσ k X hX, powerPredicates_exist σ hσ X hX ks⟩

def coreX (σ : Ty) :
    Term Signature.pure (Ctx.block (structureTypes σ) []) (σ ⇒ RTy.t) :=
  (Terms.vars (structureTypes σ) []).head

theorem core_persistent (σ : Ty)
    {Δ : List (Formula Signature.pure (Ctx.block (structureTypes σ) []))}
    (h : Derivable Ax Δ (realCore σ)) :
    Derivable Ax Δ (persist (σ ⇒ RTy.t) (coreX σ)) := by
  have raw := Derivable.andE₁ (Derivable.andE₁ (Derivable.andE₁ h))
  have hX : Derivable Ax Δ (persistUnary σ (coreX σ)) :=
    Derivable.conv raw (Conv.of_nf_left 3 _ _ rfl)
  exact Derivable.conv hX (persist_unary_conversion σ (coreX σ)).symm

/-- Exactly the positive arities one through `n`, in source order. -/
def arities (n : Nat) : List Nat := (List.range n).map Nat.succ

/-- The whole rigid-real matrix and every represented power occur inside one
simultaneous finite block of power witnesses. -/
def fullMatrix (σ : Ty) (n : Nat) :
    Formula Signature.pure (Ctx.block (structureTypes σ) []) :=
  Term.existsBlock (powerTypes σ (arities n))
    (Term.conj ((realCore σ).rename (Ren.wkBlock (powerTypes σ (arities n))))
      (Predicates.body (powerPredicates σ (coreX σ) (arities n))))

def conclusion (σ : Ty) (n : Nat) : Sentence Signature.pure :=
  Term.existsBlock (structureTypes σ) (fullMatrix σ n)

def instanceFormula (σ : Ty) (n : Nat) : Sentence Signature.pure :=
  Term.imp (Term.dia (Classicism.Research.Analytic.HasReal.term σ)) (conclusion σ n)

theorem fullMatrix_rule (σ : Ty) (hσ : σ.Closed) (n : Nat)
    {Δ : List (Formula Signature.pure (Ctx.block (structureTypes σ) []))}
    (h : Derivable Ax Δ (realCore σ)) : Derivable Ax Δ (fullMatrix σ n) :=
  existsBlock_conj_left (powerTypes σ (arities n)) h
    (Predicates.pack_of_exists (powerPredicates σ (coreX σ) (arities n))
      (powerPredicates_exist σ hσ (coreX σ) (core_persistent σ h) (arities n)))

/-- Object-language derivation of every finite instance. -/
theorem instance_derivable (σ : Ty) (hσ : σ.Closed) (n : Nat) :
    Theorem Ax (instanceFormula σ n) := by
  apply Derivable.impI
  have hr := rigid_real_rule σ hσ (Γ := [])
    (Δ := [Term.dia (Classicism.Research.Analytic.HasReal.term σ)]) Derivable.hyp₀
  change Derivable Ax _ (Term.existsBlock (structureTypes σ) (realCore σ)) at hr
  apply Derivable.exEBlock (structureTypes σ) hr
  exact Derivable.exIBlock_vars (structureTypes σ)
    (fullMatrix_rule σ hσ n Derivable.hyp₀)

/-- The schema has one ordinary finite sentence for each type and positive bound. -/
def schema : AxiomSet Signature.pure := fun a =>
  ∃ σ : Ty, σ.Closed ∧ ∃ n : Nat, 1 ≤ n ∧ a = instanceFormula σ n

/-- C5 plus necessary rigid comprehension entail the full finite schema. -/
theorem c5_rc_entails : Entails Premises schema := by
  rintro a ⟨σ, hσ, n, _, rfl⟩
  exact instance_derivable σ hσ n

/-- The same schema in an arbitrary signature, by the inclusion of pure syntax. -/
def schemaIn {Sig : Signature} : AxiomSet Sig := schema.ofPure

/-- Signature-uniform form matching the map's convention for principles. -/
theorem c5_rc_entails_in (Sig : Signature) :
    Entails (AxiomSet.ofPure P.NecNecessityOfDistinctness.schema ∪
      AxiomSet.ofPure P.NecRigidComprehension.schema) (schemaIn (Sig := Sig)) := by
  rintro a ⟨p, hp, rfl⟩
  apply Derivable.mono (Ax := Ax.ofPure) _ (Theorem.ofPure (c5_rc_entails p hp))
  rintro b ⟨q, hq, rfl⟩
  rcases hq with hq | hq | hq
  · exact Or.inl (logical_ofPure_subset _ ⟨q, hq, rfl⟩)
  · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
  · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

end Classicism.Meta.Analytic

#print axioms Classicism.Meta.Analytic.instance_derivable
#print axioms Classicism.Meta.Analytic.c5_rc_entails
#print axioms Classicism.Meta.Analytic.c5_rc_entails_in
