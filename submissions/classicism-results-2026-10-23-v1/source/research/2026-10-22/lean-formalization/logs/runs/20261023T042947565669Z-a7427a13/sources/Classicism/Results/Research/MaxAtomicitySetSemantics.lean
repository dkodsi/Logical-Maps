import Classicism.Results.Research.MaxAtomicitySetSyntax
import Classicism.Semantics.BooleanValued

/-!
# Correctness of the finite set-formula translation

Direct source: `research/2026-10-22/lean-formalization/
max-atomicity-inconsistency-proof.md`, §§3–5, and the finite translation in
`MaxAtomicitySetSyntax` (unpaginated local sources, category misc).

The main theorem evaluates the actual `SetFormula.translate` syntax in the
full Boolean-valued interpretation. Its proof is structural induction, including
the two quantified cases and the change of environment under their binders.
The only relation hypothesis identifies the value of the supplied membership
term with the crisp interpretation of an ordinary relation. Translation
correctness is proved here, not assumed.

This does not construct a membership code, prove Mostowski collapse, supply a
constructible-order formula, or prove existence of a rigid algebra. Classical
reasoning in this file belongs to the external metatheory, not to the C language.
Compilation and axiom inspection remain with the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicitySetSemantics

open BooleanValued MaxAtomicitySyntax MaxAtomicitySetSyntax

noncomputable section

variable {B : Type} [CompleteBooleanAlgebra B]

/-- The crisp Boolean value of an ordinary external proposition. -/
def truth (P : Prop) : B := by
  classical
  exact if P then ⊤ else ⊥

@[simp] theorem truth_false : (truth False : B) = ⊥ := by simp [truth]
@[simp] theorem truth_true : (truth True : B) = ⊤ := by simp [truth]

@[simp] theorem compl_truth (P : Prop) : (truth P : B)ᶜ = truth (¬ P) := by
  classical
  by_cases h : P <;> simp [truth, h]

@[simp] theorem inf_truth (P Q : Prop) :
    (truth P : B) ⊓ truth Q = truth (P ∧ Q) := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [truth, hp, hq]

@[simp] theorem sup_truth (P Q : Prop) :
    (truth P : B) ⊔ truth Q = truth (P ∨ Q) := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [truth, hp, hq]

@[simp] theorem imp_truth (P Q : Prop) :
    (truth P : B)ᶜ ⊔ truth Q = truth (P → Q) := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [truth, hp, hq]

@[simp] theorem iff_truth (P Q : Prop) :
    ((truth P : B)ᶜ ⊔ truth Q) ⊓ ((truth Q : B)ᶜ ⊔ truth P) =
      truth (P ↔ Q) := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [truth, hp, hq]

/-- Universal quantification over crisp values agrees with the actual infimum.
The proof includes empty domains and does not extract witnesses from arbitrary
Boolean-valued quantifiers. -/
@[simp] theorem iInf_truth {D : Type*} (P : D → Prop) :
    (⨅ x : D, (truth (P x) : B)) = truth (∀ x : D, P x) := by
  classical
  by_cases h : ∀ x : D, P x
  · rw [show (truth (∀ x : D, P x) : B) = ⊤ by simp [truth, h]]
    apply top_unique
    apply le_iInf
    intro x
    simp [truth, h x]
  · obtain ⟨x, hx⟩ := not_forall.mp h
    rw [show (truth (∀ x : D, P x) : B) = ⊥ by simp [truth, h]]
    apply bot_unique
    calc
      (⨅ y : D, (truth (P y) : B)) ≤ truth (P x) := iInf_le _ x
      _ = ⊥ := by simp [truth, hx]

/-- Existential quantification over crisp values agrees with the actual
supremum. A witness is obtained only from the ordinary existential proposition. -/
@[simp] theorem iSup_truth {D : Type*} (P : D → Prop) :
    (⨆ x : D, (truth (P x) : B)) = truth (∃ x : D, P x) := by
  classical
  by_cases h : ∃ x : D, P x
  · rw [show (truth (∃ x : D, P x) : B) = ⊤ by simp [truth, h]]
    obtain ⟨x, hx⟩ := h
    apply top_unique
    calc
      (⊤ : B) = truth (P x) := by simp [truth, hx]
      _ ≤ ⨆ y : D, (truth (P y) : B) :=
        le_iSup (fun y : D => (truth (P y) : B)) x
  · rw [show (truth (∃ x : D, P x) : B) = ⊥ by simp [truth, h]]
    apply bot_unique
    apply iSup_le
    intro x
    simp [truth, not_exists.mp h x]

@[simp] theorem truth_eq_top_iff [Nontrivial B] (P : Prop) :
    (truth P : B) = ⊤ ↔ P := by
  classical
  by_cases h : P <;> simp [truth, h]

@[simp] theorem truth_eq_bot_iff [Nontrivial B] (P : Prop) :
    (truth P : B) = ⊥ ↔ ¬ P := by
  classical
  by_cases h : P <;> simp [truth, h]

/-- Literal equality in the Boolean interpretation is exactly crisp truth. -/
@[simp] theorem crisp_eq_truth {D : Type} (x y : D) :
    (BooleanValued.crisp x y : B) = truth (x = y) := by
  classical
  rfl

/-- The ordinary semantics of the finite first-order formula datatype.
The relation argument interprets membership; equality is actual equality.
At each binder `Fin.cases` inserts the fresh element at index zero. -/
def satisfies {D : Type} {n : Nat} (φ : SetFormula n)
    (R : D → D → Prop) (ρ : Fin n → D) : Prop :=
  match φ with
  | .bot => False
  | .top => True
  | .eq i j => ρ i = ρ j
  | .mem i j => R (ρ i) (ρ j)
  | .neg p => ¬ satisfies p R ρ
  | .conj p q => satisfies p R ρ ∧ satisfies q R ρ
  | .disj p q => satisfies p R ρ ∨ satisfies q R ρ
  | .imp p q => satisfies p R ρ → satisfies q R ρ
  | .iff p q => satisfies p R ρ ↔ satisfies q R ρ
  | .all p => ∀ x : D, satisfies p R (Fin.cases x ρ)
  | .ex p => ∃ x : D, satisfies p R (Fin.cases x ρ)

/-- Evaluating the syntactically extended environment inserts precisely the
fresh semantic value, while weakening keeps every old variable's value. -/
theorem eval_liftEnv (I : Interpretation Signature.pure B)
    {n : Nat} {Γ : Ctx} (ρ : Fin n → PT Γ U)
    (env : IEnv (Dom I.E B) Γ) (x : Dom I.E B U) :
    (fun i => eval I (liftEnv ρ i) (.cons x env)) =
      Fin.cases x (fun i => eval I (ρ i) env) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    change eval I (ρ j).weaken (.cons x env) = eval I (ρ j) env
    exact eval_weaken I (ρ j) x env

/-- The actual finite translation is semantically correct under a crisp
interpretation of its membership parameter. This statement is uniform in
the surrounding typed variable context and its assignment, which is needed
to justify the quantified induction steps. -/
theorem eval_translate (I : Interpretation Signature.pure B)
    {n : Nat} (φ : SetFormula n)
    (R : Dom I.E B U → Dom I.E B U → Prop) :
    ∀ {Γ : Ctx} (E : PT Γ ER) (ρ : Fin n → PT Γ U)
      (env : IEnv (Dom I.E B) Γ),
      (∀ x y : Dom I.E B U, eval I E env x y = truth (R x y)) →
      eval I (translate φ E ρ) env =
        truth (satisfies φ R (fun i => eval I (ρ i) env)) := by
  induction φ with
  | bot =>
    intro Γ E ρ env hE
    simpa only [translate, satisfies, truth_false] using eval_bot I env
  | top =>
    intro Γ E ρ env hE
    simpa only [translate, satisfies, truth_true] using eval_top I env
  | eq i j =>
    intro Γ E ρ env hE
    exact crisp_eq_truth (eval I (ρ i) env) (eval I (ρ j) env)
  | mem i j =>
    intro Γ E ρ env hE
    exact hE (eval I (ρ i) env) (eval I (ρ j) env)
  | neg p ih =>
    intro Γ E ρ env hE
    change (eval I (translate p E ρ) env)ᶜ =
      truth (¬ satisfies p R (fun i => eval I (ρ i) env))
    rw [ih E ρ env hE, compl_truth]
  | conj p q ihp ihq =>
    intro Γ E ρ env hE
    change eval I (translate p E ρ) env ⊓ eval I (translate q E ρ) env =
      truth (satisfies p R (fun i => eval I (ρ i) env) ∧
        satisfies q R (fun i => eval I (ρ i) env))
    rw [ihp E ρ env hE, ihq E ρ env hE, inf_truth]
  | disj p q ihp ihq =>
    intro Γ E ρ env hE
    change eval I (translate p E ρ) env ⊔ eval I (translate q E ρ) env =
      truth (satisfies p R (fun i => eval I (ρ i) env) ∨
        satisfies q R (fun i => eval I (ρ i) env))
    rw [ihp E ρ env hE, ihq E ρ env hE, sup_truth]
  | imp p q ihp ihq =>
    intro Γ E ρ env hE
    change (eval I (translate p E ρ) env)ᶜ ⊔ eval I (translate q E ρ) env =
      truth (satisfies p R (fun i => eval I (ρ i) env) →
        satisfies q R (fun i => eval I (ρ i) env))
    rw [ihp E ρ env hE, ihq E ρ env hE, imp_truth]
  | iff p q ihp ihq =>
    intro Γ E ρ env hE
    change
      ((eval I (translate p E ρ) env)ᶜ ⊔ eval I (translate q E ρ) env) ⊓
        ((eval I (translate q E ρ) env)ᶜ ⊔ eval I (translate p E ρ) env) =
      truth (satisfies p R (fun i => eval I (ρ i) env) ↔
        satisfies q R (fun i => eval I (ρ i) env))
    simp only [ihp E ρ env hE, ihq E ρ env hE, iff_truth]
  | all p ih =>
    intro Γ E ρ env hE
    change
      (⨅ x : Dom I.E B U,
        eval I (translate p E.weaken (liftEnv ρ)) (.cons x env)) =
      truth (∀ x : Dom I.E B U,
        satisfies p R (Fin.cases x (fun i => eval I (ρ i) env)))
    calc
      (⨅ x : Dom I.E B U,
          eval I (translate p E.weaken (liftEnv ρ)) (.cons x env)) =
          ⨅ x : Dom I.E B U,
            truth (satisfies p R (Fin.cases x (fun i => eval I (ρ i) env))) := by
        apply iInf_congr
        intro x
        have hE' : ∀ u v : Dom I.E B U,
            eval I E.weaken (.cons x env) u v = truth (R u v) := by
          intro u v
          rw [eval_weaken]
          exact hE u v
        simpa only [eval_liftEnv] using
          ih E.weaken (liftEnv ρ) (.cons x env) hE'
      _ = _ := iInf_truth _
  | ex p ih =>
    intro Γ E ρ env hE
    change
      (⨆ x : Dom I.E B U,
        eval I (translate p E.weaken (liftEnv ρ)) (.cons x env)) =
      truth (∃ x : Dom I.E B U,
        satisfies p R (Fin.cases x (fun i => eval I (ρ i) env)))
    calc
      (⨆ x : Dom I.E B U,
          eval I (translate p E.weaken (liftEnv ρ)) (.cons x env)) =
          ⨆ x : Dom I.E B U,
            truth (satisfies p R (Fin.cases x (fun i => eval I (ρ i) env))) := by
        apply iSup_congr
        intro x
        have hE' : ∀ u v : Dom I.E B U,
            eval I E.weaken (.cons x env) u v = truth (R u v) := by
          intro u v
          rw [eval_weaken]
          exact hE u v
        simpa only [eval_liftEnv] using
          ih E.weaken (liftEnv ρ) (.cons x env) hE'
      _ = _ := iSup_truth _

/-- Under a nontrivial Boolean algebra, the translation is top exactly when
the ordinary finite set formula is satisfied. -/
theorem eval_translate_eq_top_iff [Nontrivial B]
    (I : Interpretation Signature.pure B) {n : Nat} (φ : SetFormula n)
    (R : Dom I.E B U → Dom I.E B U → Prop)
    {Γ : Ctx} (E : PT Γ ER) (ρ : Fin n → PT Γ U)
    (env : IEnv (Dom I.E B) Γ)
    (hE : ∀ x y : Dom I.E B U, eval I E env x y = truth (R x y)) :
    eval I (translate φ E ρ) env = ⊤ ↔
      satisfies φ R (fun i => eval I (ρ i) env) := by
  rw [eval_translate I φ R E ρ env hE, truth_eq_top_iff]

end
end Classicism.Meta.Research.MaxAtomicitySetSemantics

#print axioms Classicism.Meta.Research.MaxAtomicitySetSemantics.iInf_truth
#print axioms Classicism.Meta.Research.MaxAtomicitySetSemantics.iSup_truth
#print axioms Classicism.Meta.Research.MaxAtomicitySetSemantics.eval_liftEnv
#print axioms Classicism.Meta.Research.MaxAtomicitySetSemantics.eval_translate
#print axioms Classicism.Meta.Research.MaxAtomicitySetSemantics.eval_translate_eq_top_iff
