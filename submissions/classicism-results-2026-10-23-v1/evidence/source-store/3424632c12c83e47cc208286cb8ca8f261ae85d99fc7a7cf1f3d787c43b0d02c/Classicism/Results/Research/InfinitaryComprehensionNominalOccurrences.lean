import Classicism.Results.Research.InfinitaryComprehensionNominal
import Mathlib.Data.Set.Finite.Lattice

/-!
# Occurring parameters, evaluation locality, and supported matrices

Only parameters which occur in a matrix need a common support. Unused
members of an arbitrarily large ambient parameter family impose no condition.
This file proves evaluation locality by induction over the actual infinitary
syntax, then supports the matrix's external evaluation function directly.
Finite currying of that supported function yields the actual Comprehension
formula; the entire parameter assignment is never asserted supported.

Source: the nominal fixed-bound strictness construction in
research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md,
misc, 23 October 2026, unpaginated. Source-only, compilation held.
-/

namespace Classicism.Research.InfinitaryComprehension.Nominal

open Classicism.Meta
open Classicism.Meta.Nominal

noncomputable section

/-- Distinct typed parameter symbols which actually occur in a term. -/
def occurring {Param : Ty → Type} : {Γ : Ctx} → {σ : Ty} →
    Term Param Γ σ → Set (Σ τ, Param τ)
  | _, _, .var _ => ∅
  | _, σ, .param p => {⟨σ, p⟩}
  | _, _, .app f a => occurring f ∪ occurring a
  | _, _, .top => ∅
  | _, _, .bot => ∅
  | _, _, .neg p => occurring p
  | _, _, .conj p q => occurring p ∪ occurring q
  | _, _, .disj p q => occurring p ∪ occurring q
  | _, _, .imp p q => occurring p ∪ occurring q
  | _, _, .iff p q => occurring p ∪ occurring q
  | _, _, .eq a b => occurring a ∪ occurring b
  | _, _, .boxOp => ∅
  | _, _, .all p => occurring p
  | _, _, .ex p => occurring p
  | _, _, .iAnd J p => ⋃ j : J, occurring (p j)
  | _, _, .iOr J p => ⋃ j : J, occurring (p j)

/-- The semantics depends only on the typed parameter values actually used. -/
theorem eval_parameter_congr (M : Henkin.Model.{0}) {Param : Ty → Type}
    {Γ σ} (a : Term Param Γ σ)
    (η θ : Henkin.Assignment M Param)
    (ha : ∀ p : Σ τ, Param τ, p ∈ occurring a → η p.2 = θ p.2)
    (xs : Henkin.Env M Γ) : Henkin.eval M η a xs = Henkin.eval M θ a xs := by
  induction a with
  | var => rfl
  | @param Γ σ p => exact ha ⟨σ, p⟩ (Set.mem_singleton _)
  | app f a ihf iha =>
      change M.app _ _ = M.app _ _
      rw [ihf (fun p hp => ha p (Or.inl hp)), iha (fun p hp => ha p (Or.inr hp))]
  | top => rfl
  | bot => rfl
  | neg p ih => exact congrArg M.neg (ih ha xs)
  | conj p q ihp ihq =>
      change M.conj _ _ = M.conj _ _
      rw [ihp (fun r hr => ha r (Or.inl hr)), ihq (fun r hr => ha r (Or.inr hr))]
  | disj p q ihp ihq =>
      change M.disj _ _ = M.disj _ _
      rw [ihp (fun r hr => ha r (Or.inl hr)), ihq (fun r hr => ha r (Or.inr hr))]
  | imp p q ihp ihq =>
      change M.imp _ _ = M.imp _ _
      rw [ihp (fun r hr => ha r (Or.inl hr)), ihq (fun r hr => ha r (Or.inr hr))]
  | iff p q ihp ihq =>
      change M.iff _ _ = M.iff _ _
      rw [ihp (fun r hr => ha r (Or.inl hr)), ihq (fun r hr => ha r (Or.inr hr))]
  | eq a b iha ihb =>
      change M.eq _ _ = M.eq _ _
      rw [iha (fun r hr => ha r (Or.inl hr)), ihb (fun r hr => ha r (Or.inr hr))]
  | boxOp => rfl
  | all p ih =>
      apply congrArg (M.iAnd _)
      funext x
      exact ih ha (Henkin.Env.cons x xs)
  | ex p ih =>
      apply congrArg (M.iOr _)
      funext x
      exact ih ha (Henkin.Env.cons x xs)
  | iAnd J p ih =>
      apply congrArg (M.iAnd J)
      funext j
      exact ih j (fun r hr => ha r (Set.mem_iUnion.mpr ⟨j, hr⟩)) xs
  | iOr J p ih =>
      apply congrArg (M.iOr J)
      funext j
      exact ih j (fun r hr => ha r (Set.mem_iUnion.mpr ⟨j, hr⟩)) xs

/-- A finite-branching fragment of the actual grammar; no ambient signature
finiteness is required, and finite conjunctions/disjunctions are included. -/
def finitelyBranching {Param : Ty → Type} : {Γ : Ctx} → {σ : Ty} →
    Term Param Γ σ → Prop
  | _, _, .var _ => True
  | _, _, .param _ => True
  | _, _, .app f a => finitelyBranching f ∧ finitelyBranching a
  | _, _, .top => True
  | _, _, .bot => True
  | _, _, .neg p => finitelyBranching p
  | _, _, .conj p q => finitelyBranching p ∧ finitelyBranching q
  | _, _, .disj p q => finitelyBranching p ∧ finitelyBranching q
  | _, _, .imp p q => finitelyBranching p ∧ finitelyBranching q
  | _, _, .iff p q => finitelyBranching p ∧ finitelyBranching q
  | _, _, .eq a b => finitelyBranching a ∧ finitelyBranching b
  | _, _, .boxOp => True
  | _, _, .all p => finitelyBranching p
  | _, _, .ex p => finitelyBranching p
  | _, _, .iAnd J p => Finite J ∧ ∀ j, finitelyBranching (p j)
  | _, _, .iOr J p => Finite J ∧ ∀ j, finitelyBranching (p j)

theorem finite_occurring_of_finitelyBranching {Param : Ty → Type} {Γ σ}
    (a : Term Param Γ σ) (ha : finitelyBranching a) : (occurring a).Finite := by
  induction a with
  | var => exact Set.finite_empty
  | param => exact Set.finite_singleton _
  | app f a ihf iha => exact (ihf ha.1).union (iha ha.2)
  | top => exact Set.finite_empty
  | bot => exact Set.finite_empty
  | neg p ih => exact ih ha
  | conj p q ihp ihq => exact (ihp ha.1).union (ihq ha.2)
  | disj p q ihp ihq => exact (ihp ha.1).union (ihq ha.2)
  | imp p q ihp ihq => exact (ihp ha.1).union (ihq ha.2)
  | iff p q ihp ihq => exact (ihp ha.1).union (ihq ha.2)
  | eq a b iha ihb => exact (iha ha.1).union (ihb ha.2)
  | boxOp => exact Set.finite_empty
  | all p ih => exact ih ha
  | ex p ih => exact ih ha
  | iAnd J p ih =>
      letI : Finite J := ha.1
      exact Set.finite_iUnion (fun j => ih j (ha.2 j))
  | iOr J p ih =>
      letI : Finite J := ha.1
      exact Set.finite_iUnion (fun j => ih j (ha.2 j))

namespace Hierarchy

variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}
variable (E : Nom A I)

/-- Direct support of the matrix evaluator, without supporting its entire
ambient assignment. This is the occurrence-sensitive equivariance step. -/
theorem eval_function_supported {Param : Ty → Type} {Γ}
    (a : Formula Param Γ) (η : Henkin.Assignment (model E) Param)
    (S : Set A) (hS : I.Small S)
    (hp : ∀ p : Σ τ, Param τ, p ∈ occurring a →
      Supports A (dom E p.1).obj S (η p.2)) :
    Supported A (function (env E Γ).obj (rdom E .t).obj) I
      (fun xs => Henkin.eval (model E) η a (toEnv E Γ xs)) := by
  refine ⟨S, hS, (function_support_iff (env E Γ) (rdom E .t) S _).2 ?_⟩
  intro g hg xs
  change Henkin.eval (model E) η a (toEnv E Γ ((env E Γ).obj.act g xs)) =
    Henkin.eval (model E) η a (toEnv E Γ xs)
  rw [toEnv_act]
  have hl := eval_parameter_congr (model E) a
    ((assignmentAction E Param).act g η) η
    (fun p hpa => hp p hpa g hg) (actEnv E g (toEnv E Γ xs))
  exact hl.symm.trans (eval_equivariant E a g η (toEnv E Γ xs))

/-- Currying the admitted supported evaluator produces the requested relation. -/
theorem comprehension_of_supported_evaluation {Param : Ty → Type} {Γ}
    (a : Formula Param Γ) (η : Henkin.Assignment (model E) Param)
    (hs : Supported A (function (env E Γ).obj (rdom E .t).obj) I
      (fun xs => Henkin.eval (model E) η a (toEnv E Γ xs)))
    (w : (model E).World) :
    (model E).truth (Henkin.eval (model E) η a.comprehension Henkin.Env.nil) w := by
  let f : exponential (env E Γ) (rdom E .t) :=
    ⟨fun xs => Henkin.eval (model E) η a (toEnv E Γ xs), hs⟩
  apply (Henkin.eval_comprehension_iff (model E) η a w).2
  refine ⟨(curryMany E Γ (evaluation (env E Γ) (rdom E .t))).fn f, ?_⟩
  intro xs v
  have h := curryMany_spec E Γ (evaluation (env E Γ) (rdom E .t)) f (ofEnv E Γ xs)
  change Henkin.uncurry (model E) Γ _ (toEnv E Γ (ofEnv E Γ xs)) =
    Henkin.eval (model E) η a (toEnv E Γ (ofEnv E Γ xs)) at h
  rw [toEnv_ofEnv] at h
  exact Iff.of_eq h

end Hierarchy

#print axioms eval_parameter_congr
#print axioms finite_occurring_of_finitelyBranching
#print axioms Hierarchy.eval_function_supported
#print axioms Hierarchy.comprehension_of_supported_evaluation

end
end Classicism.Research.InfinitaryComprehension.Nominal
