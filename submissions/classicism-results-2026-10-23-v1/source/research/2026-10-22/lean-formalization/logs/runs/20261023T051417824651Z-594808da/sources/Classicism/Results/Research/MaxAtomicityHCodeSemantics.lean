import Classicism.Results.Research.MaxAtomicitySetSemantics
import Classicism.Results.Research.MaxAtomicityHCodeSyntax
import Classicism.Results.Research.MaxAtomicityEvalTools
import Mathlib.Order.WellFounded

/-!
# Crisp predicates, small subsets, and well-founded membership

Direct source: `research/2026-10-22/lean-formalization/
max-atomicity-inconsistency-proof.md`, §3 (unpaginated local proof, misc).

These are external semantic proofs for the actual finite HCode syntax. Smallness
uses arbitrary B-valued functions, and is identified with an actual embedding
of the subset into B. The well-foundedness proof quantifies over ALL B-valued
predicates: noncrisp predicates are handled by the explicit crispness guard,
and every ordinary subset is represented by its characteristic truth predicate.

No membership code, collapse, cardinal equation, or rigid algebra is assumed
to exist. This file does not by itself establish the HCode characterization.
Compilation and axiom inspection are pending the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityHCodeSemantics

open BooleanValued MaxAtomicitySyntax MaxAtomicitySetSemantics
open MaxAtomicityEvalTools

noncomputable section

set_option maxHeartbeats 800000

variable {B : Type} [CompleteBooleanAlgebra B]

def Crisp {D : Type} (X : D → B) : Prop :=
  ∀ x, X x = ⊥ ∨ X x = ⊤

/-- A total B-valued function injective on the specified subset. The values
of this function are not restricted to bottom and top. -/
def Small {D : Type} (P : D → Prop) : Prop :=
  ∃ f : D → B, ∀ u v, ((P u ∧ P v) ∧ f u = f v) → u = v

theorem small_iff_embedding {D : Type} (P : D → Prop) :
    Small (B := B) P ↔ Nonempty ({x : D // P x} ↪ B) := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨⟨fun x => f x.val, ?_⟩⟩
    intro x y hxy
    exact Subtype.ext (hf x.val y.val ⟨⟨x.property, y.property⟩, hxy⟩)
  · rintro ⟨j⟩
    let f : D → B := fun x => if hx : P x then j ⟨x, hx⟩ else ⊥
    refine ⟨f, ?_⟩
    intro x y hxy
    have he : j ⟨x, hxy.1.1⟩ = j ⟨y, hxy.1.2⟩ := by
      simpa only [f, dif_pos hxy.1.1, dif_pos hxy.1.2] using hxy.2
    exact congrArg Subtype.val (j.injective he)

theorem truth_predicate_crisp {D : Type} (P : D → Prop) :
    Crisp (fun x => (truth (P x) : B)) := by
  classical
  intro x
  by_cases hx : P x
  · exact Or.inr (by simp [truth, hx])
  · exact Or.inl (by simp [truth, hx])

theorem crisp_value [Nontrivial B] {D : Type} {X : D → B}
    (hX : Crisp X) (x : D) : X x = truth (X x = ⊤) := by
  rcases hX x with hx | hx <;> simp [hx, truth]

theorem truth_injective [Nontrivial B] (P Q : Prop) :
    (truth P : B) = truth Q ↔ (P ↔ Q) := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [truth, hp, hq]

/-- The exact value of the syntactic crispness test, for arbitrary X. -/
theorem eval_crisp (I : Interpretation Signature.pure B) {Γ : Ctx}
    (X : PT Γ UP) (env : IEnv (Dom I.E B) Γ) :
    eval I (MaxAtomicitySyntax.crisp X) env = truth (Crisp (eval I X env)) := by
  change (⨅ x : Dom I.E B U,
    (BooleanValued.crisp (eval I X.weaken (.cons x env) x)
      (eval I Term.bot (.cons x env)) : B) ⊔
    BooleanValued.crisp (eval I X.weaken (.cons x env) x)
      (eval I Term.top (.cons x env))) = _
  simp only [eval_weaken, eval_bot, eval_top, crisp_eq_truth, sup_truth, iInf_truth]
  rfl

/-- The binary crispness test also has a crisp value for every relation,
including relations that fail the test. -/
theorem eval_crispRelation (I : Interpretation Signature.pure B) {Γ : Ctx}
    (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ) :
    eval I (crispRelation E) env =
      truth (∀ x y : Dom I.E B U,
        eval I E env x y = ⊥ ∨ eval I E env x y = ⊤) := by
  change (⨅ x : Dom I.E B U, ⨅ y : Dom I.E B U,
    (BooleanValued.crisp (eval I E.weaken.weaken (.cons y (.cons x env)) x y)
      (eval I Term.bot (.cons y (.cons x env))) : B) ⊔
    BooleanValued.crisp (eval I E.weaken.weaken (.cons y (.cons x env)) x y)
      (eval I Term.top (.cons y (.cons x env)))) = _
  simp only [eval_weaken, eval_bot, eval_top, crisp_eq_truth, sup_truth, iInf_truth]

def smallValue {D : Type} (X : D → B) : B :=
  ⨆ f : D → B, ⨅ u : D, ⨅ v : D,
    ((X u ⊓ X v) ⊓ (BooleanValued.crisp (f u) (f v) : B))ᶜ ⊔
      BooleanValued.crisp u v

theorem smallValue_eq_truth [Nontrivial B] {D : Type} (X : D → B)
    (hX : Crisp X) : smallValue X = truth (Small (B := B) (fun x => X x = ⊤)) := by
  let P : D → Prop := fun x => X x = ⊤
  change smallValue X = truth (Small (B := B) P)
  have hx : ∀ x, X x = truth (P x) := crisp_value hX
  simp only [smallValue, hx, crisp_eq_truth, inf_truth, compl_truth,
    sup_truth, iInf_truth, iSup_truth, Small, imp_iff_not_or]

/-- The Boolean value of Small is defined even for a noncrisp predicate. -/
theorem eval_small_value (I : Interpretation Signature.pure B)
    {Γ : Ctx} (X : PT Γ UP) (env : IEnv (Dom I.E B) Γ) :
    eval I (small X) env = smallValue (eval I X env) := by
  -- Expand logical macros before the generic application equation: otherwise
  -- eval_app also matches the application implementing an outer quantifier.
  simp only [small, eval_exists, eval_forall, eval_imp, eval_conj,
    eval_eq]
  simp only [eval_app, eval_weaken, eval_v0, eval_v1, eval_v2, smallValue]

/-- Exact smallness semantics for a crisp predicate. -/
theorem eval_small [Nontrivial B] (I : Interpretation Signature.pure B)
    {Γ : Ctx} (X : PT Γ UP) (env : IEnv (Dom I.E B) Γ)
    (hX : Crisp (eval I X env)) :
    eval I (small X) env =
      truth (Small (B := B) (fun x : Dom I.E B U => eval I X env x = ⊤)) := by
  rw [eval_small_value]
  exact smallValue_eq_truth (eval I X env) hX

theorem eval_small_eq_top_iff_embedding [Nontrivial B]
    (I : Interpretation Signature.pure B) {Γ : Ctx}
    (X : PT Γ UP) (env : IEnv (Dom I.E B) Γ)
    (hX : Crisp (eval I X env)) :
    eval I (small X) env = ⊤ ↔
      Nonempty ({x : Dom I.E B U // eval I X env x = ⊤} ↪ B) := by
  rw [eval_small I X env hX, truth_eq_top_iff, small_iff_embedding]

def Extensional {D : Type} (R : D → D → Prop) : Prop :=
  ∀ u v, (∀ z, R z u ↔ R z v) → u = v

/-- Extensionality compares complete predecessor rows of the crisp relation. -/
theorem eval_extensional (I : Interpretation Signature.pure B)
    {Γ : Ctx} (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ)
    (R : Dom I.E B U → Dom I.E B U → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (extensional E) env = truth (Extensional R) := by
  change (⨅ u : Dom I.E B U, ⨅ v : Dom I.E B U,
    (⨅ z : Dom I.E B U,
      ((eval I E.weaken.weaken.weaken (.cons z (.cons v (.cons u env))) z u)ᶜ ⊔
        eval I E.weaken.weaken.weaken (.cons z (.cons v (.cons u env))) z v) ⊓
      ((eval I E.weaken.weaken.weaken (.cons z (.cons v (.cons u env))) z v)ᶜ ⊔
        eval I E.weaken.weaken.weaken (.cons z (.cons v (.cons u env))) z u))ᶜ ⊔
      (BooleanValued.crisp u v : B)) = _
  simp only [eval_weaken, hE, crisp_eq_truth]
  simp only [iff_truth]
  simp only [iInf_truth, imp_truth]
  rfl

/-- The row clause quantifies over all elements and applies the proved smallness
semantics to the lambda term for each predecessor row. -/
theorem eval_rows [Nontrivial B] (I : Interpretation Signature.pure B)
    {Γ : Ctx} (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ)
    (R : Dom I.E B U → Dom I.E B U → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (MaxAtomicityHCodeSyntax.rows E) env =
      truth (∀ u : Dom I.E B U, Small (B := B) (fun v => R v u)) := by
  change (⨅ u : Dom I.E B U,
    eval I (small (.lam (member E.weaken.weaken Term.v0 Term.v1))) (.cons u env)) = _
  calc
    (⨅ u : Dom I.E B U,
        eval I (small (.lam (member E.weaken.weaken Term.v0 Term.v1))) (.cons u env)) =
        ⨅ u : Dom I.E B U, truth (Small (B := B) (fun v => R v u)) := by
      apply iInf_congr
      intro u
      let X : PT ((U : Ty) :: Γ) UP :=
        .lam (member E.weaken.weaken Term.v0 Term.v1)
      have hx (v : Dom I.E B U) : eval I X (.cons u env) v = truth (R v u) := by
        change eval I E.weaken.weaken (.cons v (.cons u env)) v u = _
        rw [eval_weaken, eval_weaken]
        exact hE v u
      have hX : Crisp (eval I X (.cons u env)) := by
        intro v
        rw [hx]
        exact truth_predicate_crisp (fun w => R w u) v
      simpa only [hx, truth_eq_top_iff] using eval_small I X (.cons u env) hX
    _ = _ := iInf_truth _

def MinimalFor {D : Type} (R : D → D → Prop) (P : D → Prop) : Prop :=
  (∃ x, P x) → ∃ u, P u ∧ ∀ v, R v u → ¬ P v

def MinimalSubset {D : Type} (R : D → D → Prop) : Prop :=
  ∀ P : D → Prop, MinimalFor R P

/-- The subset-minimality condition is actual well-foundedness, not merely
absence of a particular represented descending sequence. -/
theorem minimalSubset_iff_wellFounded {D : Type} (R : D → D → Prop) :
    MinimalSubset R ↔ WellFounded R := by
  constructor
  · intro h
    apply (WellFounded.wellFounded_iff_has_min (r := R)).2
    intro s hs
    obtain ⟨u, hu, hm⟩ := h s hs
    exact ⟨u, hu, fun v hv hR => hm v hR hv⟩
  · intro h P hP
    obtain ⟨u, hu, hm⟩ := h.has_min {x | P x} hP
    exact ⟨u, hu, fun v hR hv => hm v hv hR⟩

def wellFoundedValue {D : Type} (R : D → D → Prop) : B :=
  ⨅ X : D → B,
    (truth (Crisp X) ⊓ (⨆ x : D, X x))ᶜ ⊔
      ⨆ u : D, X u ⊓ (⨅ v : D, (truth (R v u) : B)ᶜ ⊔ (X v)ᶜ)

/-- Every arbitrary predicate is accounted for: a noncrisp predicate contributes
top to the guarded universal, while a crisp one contributes its ordinary
subset-minimality condition. -/
theorem wellFoundedValue_eq_truth [Nontrivial B] {D : Type}
    (R : D → D → Prop) : wellFoundedValue (B := B) R = truth (MinimalSubset R) := by
  classical
  have hbody (X : D → B) :
      (truth (Crisp X) ⊓ (⨆ x : D, X x))ᶜ ⊔
          (⨆ u : D, X u ⊓ (⨅ v : D, (truth (R v u) : B)ᶜ ⊔ (X v)ᶜ)) =
        truth (Crisp X → MinimalFor R (fun x => X x = ⊤)) := by
    let P : D → Prop := fun x => X x = ⊤
    change (truth (Crisp X) ⊓ (⨆ x : D, X x))ᶜ ⊔
        (⨆ u : D, X u ⊓ (⨅ v : D, (truth (R v u) : B)ᶜ ⊔ (X v)ᶜ)) =
      truth (Crisp X → MinimalFor R P)
    by_cases hX : Crisp X
    · have hx : ∀ x, X x = truth (P x) := crisp_value hX
      simp only [hX, truth_true, top_inf_eq, hx, compl_truth,
        sup_truth, inf_truth, iInf_truth, iSup_truth,
        MinimalFor, true_implies, imp_iff_not_or, not_true_eq_false, false_or]
    · simp only [hX, truth_false, bot_inf_eq, compl_bot, top_sup_eq,
        false_implies, truth_true]
  have hsets : (∀ X : D → B, Crisp X → MinimalFor R (fun x => X x = ⊤)) ↔
      MinimalSubset R := by
    constructor
    · intro h P
      simpa only [truth_eq_top_iff] using
        h (fun x => truth (P x)) (truth_predicate_crisp P)
    · intro h X hX
      exact h (fun x => X x = ⊤)
  calc
    wellFoundedValue (B := B) R =
        ⨅ X : D → B, truth (Crisp X → MinimalFor R (fun x => X x = ⊤)) :=
      iInf_congr hbody
    _ = truth (∀ X : D → B, Crisp X → MinimalFor R (fun x => X x = ⊤)) :=
      iInf_truth _
    _ = truth (MinimalSubset R) := congrArg (fun p : Prop => (truth p : B)) (propext hsets)

/-- Exact interpretation of the actual WF term, under a crisp relation.
No restriction on the syntactically quantified predicates is assumed. -/
theorem eval_wellFounded [Nontrivial B] (I : Interpretation Signature.pure B)
    {Γ : Ctx} (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ)
    (R : Dom I.E B U → Dom I.E B U → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (MaxAtomicitySyntax.wellFounded E) env = truth (WellFounded R) := by
  simp only [MaxAtomicitySyntax.wellFounded, eval_forall, eval_imp,
    eval_conj, eval_exists, eval_neg, eval_crisp]
  simp only [member, eval_app, eval_weaken, eval_v0, eval_v1, eval_v2, hE]
  change wellFoundedValue (B := B) R = truth (WellFounded R)
  rw [wellFoundedValue_eq_truth]
  exact congrArg (fun p : Prop => (truth p : B))
    (propext (minimalSubset_iff_wellFounded R))

def Fill {D : Type} (R : D → D → Prop) : Prop :=
  ∀ P : D → Prop, Small (B := B) P → ∃ u, ∀ v, R v u ↔ P v

def fillValue {D : Type} (R : D → D → Prop) : B :=
  ⨅ X : D → B,
    (truth (Crisp X) ⊓ smallValue X)ᶜ ⊔
      ⨆ u : D, ⨅ v : D, (BooleanValued.crisp (truth (R v u) : B) (X v) : B)

/-- The Fill guard is also checked on every B-valued predicate. Noncrisp
predicates contribute top, independently of their unguarded Small value. -/
theorem fillValue_eq_truth [Nontrivial B] {D : Type}
    (R : D → D → Prop) : fillValue (B := B) R = truth (Fill (B := B) R) := by
  classical
  have hbody (X : D → B) :
      (truth (Crisp X) ⊓ smallValue X)ᶜ ⊔
          (⨆ u : D, ⨅ v : D, (BooleanValued.crisp (truth (R v u) : B) (X v) : B)) =
        truth (Crisp X →
          (Small (B := B) (fun x => X x = ⊤) → ∃ u, ∀ v, R v u ↔ X v = ⊤)) := by
    let P : D → Prop := fun x => X x = ⊤
    change (truth (Crisp X) ⊓ smallValue X)ᶜ ⊔
        (⨆ u : D, ⨅ v : D, (BooleanValued.crisp (truth (R v u) : B) (X v) : B)) =
      truth (Crisp X → (Small (B := B) P → ∃ u, ∀ v, R v u ↔ P v))
    by_cases hX : Crisp X
    · have hx : ∀ x, X x = truth (P x) := crisp_value hX
      have hs : smallValue X = truth (Small (B := B) P) := smallValue_eq_truth X hX
      simp only [hX, truth_true, top_inf_eq, hs, hx, crisp_eq_truth,
        truth_injective, iInf_truth, iSup_truth, imp_truth, true_implies]
    · simp only [hX, truth_false, bot_inf_eq, compl_bot, top_sup_eq,
        false_implies, truth_true]
  have hsets :
      (∀ X : D → B, Crisp X →
        (Small (B := B) (fun x => X x = ⊤) → ∃ u, ∀ v, R v u ↔ X v = ⊤)) ↔
      Fill (B := B) R := by
    constructor
    · intro h P
      simpa only [truth_eq_top_iff] using
        h (fun x => truth (P x)) (truth_predicate_crisp P)
    · intro h X hX
      exact h (fun x => X x = ⊤)
  calc
    fillValue (B := B) R =
        ⨅ X : D → B, truth (Crisp X →
          (Small (B := B) (fun x => X x = ⊤) → ∃ u, ∀ v, R v u ↔ X v = ⊤)) :=
      iInf_congr hbody
    _ = truth (∀ X : D → B, Crisp X →
        (Small (B := B) (fun x => X x = ⊤) → ∃ u, ∀ v, R v u ↔ X v = ⊤)) :=
      iInf_truth _
    _ = truth (Fill (B := B) R) :=
      congrArg (fun p : Prop => (truth p : B)) (propext hsets)

theorem eval_fill [Nontrivial B] (I : Interpretation Signature.pure B)
    {Γ : Ctx} (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ)
    (R : Dom I.E B U → Dom I.E B U → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (fill E) env = truth (Fill (B := B) R) := by
  simp only [fill, eval_forall, eval_imp, eval_conj, eval_exists,
    eval_eq, eval_crisp, eval_small_value]
  simp only [member, eval_app, eval_weaken, eval_v0, eval_v1, eval_v2, hE]
  exact fillValue_eq_truth (B := B) R

/-- The ordinary properties asserted by the crisp HCode relation. -/
def GoodRelation {D : Type} (R : D → D → Prop) : Prop :=
  (Extensional R ∧ (WellFounded R ∧ Fill (B := B) R)) ∧
    ∀ u, Small (B := B) (fun v => R v u)

theorem eval_hCode [Nontrivial B] (I : Interpretation Signature.pure B)
    {Γ : Ctx} (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ)
    (R : Dom I.E B U → Dom I.E B U → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (MaxAtomicityHCodeSyntax.hCode E) env = truth (GoodRelation (B := B) R) := by
  have hc : eval I (crispRelation E) env = ⊤ := by
    rw [eval_crispRelation, truth_eq_top_iff]
    intro x y
    rw [hE]
    exact truth_predicate_crisp (fun z => R x z) y
  change
    (eval I (crispRelation E) env ⊓
      (eval I (extensional E) env ⊓
        (eval I (MaxAtomicitySyntax.wellFounded E) env ⊓ eval I (fill E) env))) ⊓
      eval I (MaxAtomicityHCodeSyntax.rows E) env = _
  rw [hc, eval_extensional I E env R hE, eval_wellFounded I E env R hE,
    eval_fill I E env R hE, eval_rows I E env R hE, top_inf_eq]
  simp only [inf_truth]
  rfl

/-- A noncrisp relation is rejected before any other HCode clause matters. -/
theorem eval_hCode_noncrisp (I : Interpretation Signature.pure B)
    {Γ : Ctx} (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ)
    (hE : ¬ ∀ x y : Dom I.E B U, eval I E env x y = ⊥ ∨ eval I E env x y = ⊤) :
    eval I (MaxAtomicityHCodeSyntax.hCode E) env = ⊥ := by
  have hc : eval I (crispRelation E) env = ⊥ := by
    rw [eval_crispRelation]
    simp [truth, hE]
  change
    (eval I (crispRelation E) env ⊓
      (eval I (extensional E) env ⊓
        (eval I (MaxAtomicitySyntax.wellFounded E) env ⊓ eval I (fill E) env))) ⊓
      eval I (MaxAtomicityHCodeSyntax.rows E) env = ⊥
  rw [hc, bot_inf_eq, bot_inf_eq]

/-- The complete HCode test has this exact crisp value for every supplied
relation term. No crispness premise on that term is needed. -/
theorem eval_hCode_exact [Nontrivial B] (I : Interpretation Signature.pure B)
    {Γ : Ctx} (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ) :
    eval I (MaxAtomicityHCodeSyntax.hCode E) env =
      truth ((∀ x y : Dom I.E B U,
        eval I E env x y = ⊥ ∨ eval I E env x y = ⊤) ∧
        GoodRelation (B := B) (fun x y => eval I E env x y = ⊤)) := by
  classical
  by_cases hc : ∀ x y : Dom I.E B U,
      eval I E env x y = ⊥ ∨ eval I E env x y = ⊤
  · have hrel (x y : Dom I.E B U) :
        eval I E env x y = truth (eval I E env x y = ⊤) :=
      crisp_value (hc x) y
    rw [eval_hCode I E env (fun x y => eval I E env x y = ⊤) hrel]
    simp only [hc, forall_const, true_and]
  · rw [eval_hCode_noncrisp I E env hc]
    simp only [hc, false_and, truth_false]

end
end Classicism.Meta.Research.MaxAtomicityHCodeSemantics

#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.small_iff_embedding
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_crisp
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_crispRelation
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_small
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_small_eq_top_iff_embedding
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_extensional
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_rows
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.minimalSubset_iff_wellFounded
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.wellFoundedValue_eq_truth
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_wellFounded
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.fillValue_eq_truth
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_fill
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_hCode
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_hCode_noncrisp
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSemantics.eval_hCode_exact
