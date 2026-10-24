import Classicism.Models.BooleanTypedTermSemantics
import Classicism.Models.ChoiceFirstOrderSmall

/-!
# Boolean semantics and comprehension for the actual small typed syntax

Original supporting formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md`, sections 3--4
(unpaginated). The actual `ChoiceFirstOrder.SmallFormula` is evaluated on
the project's `IEnv`, with Boolean equality and actual domain quantifiers.
The interpretation is proved coherent at every Boolean degree and
semilinear under the supplied action. Each comprehension instance is
witnessed by a constructed supported coherent profile.

There is no assumed comprehension, model-existence, extraction, or Choice
verdict. The later tagged first-order bridge connects these Boolean values
to the ordinary first-order extraction machinery.
-/

namespace Classicism.Meta.ChoiceBoolean.SmallFormulaSemantics

open ChoiceFirstOrder TypedHierarchy TypedTermSemantics

variable {K B : Type} [CompleteBooleanAlgebra B]
variable (a : BooleanAction K B) (E : Type)

noncomputable section

/-- Convert the project's inductive environment to the product action space. -/
def ofIEnv : ∀ {Γ : Ctx}, IEnv (Dom a E) Γ → Env.{0} a E Γ
  | [], .nil => PUnit.unit
  | _ :: _, .cons x g => (x, ofIEnv g)

theorem varMap_ofIEnv : ∀ {Γ : Ctx} {σ : Ty} (v : Var Γ σ)
    (g : IEnv (Dom a E) Γ), varMap a E v (ofIEnv a E g) = g.get v
  | _, _, .zero, .cons _ _ => rfl
  | _, _, .succ v, .cons _ g => varMap_ofIEnv v g

/-- The componentwise permutation of an actual typed environment. -/
def envAction (π : Equiv.Perm K) {Γ : Ctx} (g : IEnv (Dom a E) Γ) :
    IEnv (Dom a E) Γ :=
  g.map (fun σ x => (DomSpace a E σ).action.act π x)

theorem ofIEnv_action (π : Equiv.Perm K) : ∀ {Γ : Ctx} (g : IEnv (Dom a E) Γ),
    ofIEnv a E (envAction a E π g) = (EnvSpace.{0} a E Γ).action.act π (ofIEnv a E g)
  | [], .nil => rfl
  | σ :: Γ, .cons x g => by
    change ((DomSpace a E σ).action.act π x, ofIEnv a E (envAction a E π g)) =
      ((DomSpace a E σ).action.act π x, (EnvSpace.{0} a E Γ).action.act π (ofIEnv a E g))
    rw [ofIEnv_action π g]

/-- Arbitrary degree agreement on the variables bounds product-environment equality. -/
theorem envEq_of_get {q : B} : ∀ {Γ : Ctx} (g h : IEnv (Dom a E) Γ),
    (∀ σ (v : Var Γ σ), q ≤ (DomSpace a E σ).space.eqv (g.get v) (h.get v)) →
    q ≤ (EnvSpace.{0} a E Γ).space.eqv (ofIEnv a E g) (ofIEnv a E h)
  | [], .nil, .nil, _ => by
    exact le_top.trans (le_of_eq
      ((EnvSpace.{0} a E []).space.refl (ofIEnv a E .nil)).symm)
  | σ :: Γ, .cons x g, .cons y h, hg =>
      le_inf (hg σ .zero)
        (envEq_of_get g h (fun τ v => hg τ (.succ v)))

/-- A tuple of typed variables denotes a coherent equivariant tuple map. -/
def argsMap {Γ : Ctx} : ∀ ρ, Args (fun σ => Var Γ σ) ρ →
    Map (EnvSpace.{0} a E Γ) (TupleSpace a E ρ)
  | .t, _ => Map.unit _
  | .arr _ ρ, xs => (varMap a E xs.1).pair (argsMap ρ xs.2)

theorem argsMap_ofIEnv {Γ : Ctx} : ∀ ρ (xs : Args (fun σ => Var Γ σ) ρ)
    (g : IEnv (Dom a E) Γ),
    argsMap a E ρ xs (ofIEnv a E g) =
      toTuple a E ρ (mapArgs (fun _ v => g.get v) ρ xs)
  | .t, _, _ => rfl
  | .arr σ ρ, xs, g => by
    change Var Γ σ × Args (fun τ => Var Γ τ) ρ at xs
    rcases xs with ⟨x, xs⟩
    change (varMap a E x (ofIEnv a E g), argsMap a E ρ xs (ofIEnv a E g)) =
      (g.get x, toTuple a E ρ (mapArgs (fun _ v => g.get v) ρ xs))
    exact congrArg₂ Prod.mk (varMap_ofIEnv a E x g) (argsMap_ofIEnv ρ xs g)

/-- Insert a tuple block ahead of the existing context, respecting both structures. -/
def blockMap (Γ : Ctx) : ∀ ρ,
    Map (ActionSpace.product (EnvSpace.{0} a E Γ) (TupleSpace a E ρ))
      (EnvSpace.{0} a E (ρ.args ++ Γ))
  | .t => Map.fst _ _
  | .arr σ ρ =>
      let X := EnvSpace.{0} a E Γ
      let Y := DomSpace a E σ
      let T := TupleSpace a E ρ
      let outer := Map.fst X (ActionSpace.product Y T)
      let head := (Map.fst Y T).comp (Map.snd X (ActionSpace.product Y T))
      let rest := (Map.snd Y T).comp (Map.snd X (ActionSpace.product Y T))
      head.pair ((blockMap Γ ρ).comp (outer.pair rest))

theorem blockMap_ofIEnv (Γ : Ctx) : ∀ ρ (xs : Args (Dom a E) ρ)
    (g : IEnv (Dom a E) Γ),
    blockMap a E Γ ρ (ofIEnv a E g, toTuple a E ρ xs) =
      ofIEnv a E (appendEnv (argsEnv ρ xs) g)
  | .t, _, _ => rfl
  | .arr σ ρ, xs, g => by
    change (xs.1, blockMap a E Γ ρ (ofIEnv a E g, toTuple a E ρ xs.2)) =
      (xs.1, ofIEnv a E (appendEnv (argsEnv ρ xs.2) g))
    rw [blockMap_ofIEnv Γ ρ xs.2 g]

private def falseForm (X : ActionSpace a) : Form X where
  pred := Predicate.const ⊥
  equivariant π _ := (a.map π).map_bot.symm

/-- Coherent, equivariant interpretation of the actual small formula constructors. -/
def smallForm : ∀ {Γ : Ctx}, SmallFormula Γ → Form (EnvSpace.{0} a E Γ)
  | _, .equal (σ := σ) x y =>
      (Form.equality (DomSpace a E σ)).pullback ((varMap a E x).pair (varMap a E y))
  | _, .rel ρ x xs => applyForm a E ρ (varMap a E x) (argsMap a E ρ xs)
  | _, .falsum => falseForm a _
  | _, .neg p => (smallForm p).neg
  | _, .conj p q => (smallForm p).inf (smallForm q)
  | _, .disj p q => (smallForm p).sup (smallForm q)
  | Γ, .all ρ p => ((smallForm p).pullback (blockMap a E Γ ρ)).allRight
  | Γ, .ex ρ p => ((smallForm p).pullback (blockMap a E Γ ρ)).exRight

/-- Direct Boolean semantics on project environments. Its clauses are definitional. -/
def smallValue : ∀ {Γ : Ctx}, SmallFormula Γ → IEnv (Dom a E) Γ → B
  | _, .equal (σ := σ) x y, g => (DomSpace a E σ).space.eqv (g.get x) (g.get y)
  | _, .rel ρ x xs, g => profile a E ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ xs)
  | _, .falsum, _ => ⊥
  | _, .neg p, g => (smallValue p g)ᶜ
  | _, .conj p q, g => smallValue p g ⊓ smallValue q g
  | _, .disj p q, g => smallValue p g ⊔ smallValue q g
  | _, .all ρ p, g => ⨅ xs : Args (Dom a E) ρ,
      smallValue p (appendEnv (argsEnv ρ xs) g)
  | _, .ex ρ p, g => ⨆ xs : Args (Dom a E) ρ,
      smallValue p (appendEnv (argsEnv ρ xs) g)

/-- Agreement of the compositional coherent construction and the direct clauses. -/
theorem smallForm_correct : ∀ {Γ : Ctx} (φ : SmallFormula Γ) (g : IEnv (Dom a E) Γ),
    smallForm a E φ (ofIEnv a E g) = smallValue a E φ g
  | _, .equal (σ := σ) x y, g => by
    change (DomSpace a E σ).space.eqv (varMap a E x (ofIEnv a E g))
      (varMap a E y (ofIEnv a E g)) = (DomSpace a E σ).space.eqv (g.get x) (g.get y)
    rw [varMap_ofIEnv, varMap_ofIEnv]
  | _, .rel ρ x xs, g => by
    change Predicate.toFun (X := (TupleSpace a E ρ).space)
        (varMap a E x (ofIEnv a E g)).val (argsMap a E ρ xs (ofIEnv a E g)) =
      Predicate.toFun (X := (TupleSpace a E ρ).space)
        (g.get x).val (toTuple a E ρ (mapArgs (fun _ v => g.get v) ρ xs))
    exact congrArg₂
      (fun (F : Dom a E (.rel ρ)) (ys : Tuple a E ρ) =>
        Predicate.toFun (X := (TupleSpace a E ρ).space) F.val ys)
      (varMap_ofIEnv a E x g) (argsMap_ofIEnv a E ρ xs g)
  | _, .falsum, _ => rfl
  | _, .neg p, g => by
    change (smallForm a E p (ofIEnv a E g))ᶜ = (smallValue a E p g)ᶜ
    rw [smallForm_correct p g]
  | _, .conj p q, g => by
    change smallForm a E p (ofIEnv a E g) ⊓ smallForm a E q (ofIEnv a E g) =
      smallValue a E p g ⊓ smallValue a E q g
    rw [smallForm_correct p g, smallForm_correct q g]
  | _, .disj p q, g => by
    change smallForm a E p (ofIEnv a E g) ⊔ smallForm a E q (ofIEnv a E g) =
      smallValue a E p g ⊔ smallValue a E q g
    rw [smallForm_correct p g, smallForm_correct q g]
  | Γ, .all ρ p, g => by
    change (⨅ xs : Tuple a E ρ,
      smallForm a E p (blockMap a E Γ ρ (ofIEnv a E g, xs))) =
      ⨅ xs : Args (Dom a E) ρ, smallValue a E p (appendEnv (argsEnv ρ xs) g)
    calc
      _ = ⨅ xs : Args (Dom a E) ρ,
          smallForm a E p (blockMap a E Γ ρ (ofIEnv a E g, toTuple a E ρ xs)) :=
        (tupleEquiv a E ρ).iInf_comp.symm
      _ = _ := by
        apply iInf_congr
        intro xs
        rw [blockMap_ofIEnv, smallForm_correct p]
  | Γ, .ex ρ p, g => by
    change (⨆ xs : Tuple a E ρ,
      smallForm a E p (blockMap a E Γ ρ (ofIEnv a E g, xs))) =
      ⨆ xs : Args (Dom a E) ρ, smallValue a E p (appendEnv (argsEnv ρ xs) g)
    calc
      _ = ⨆ xs : Args (Dom a E) ρ,
          smallForm a E p (blockMap a E Γ ρ (ofIEnv a E g, toTuple a E ρ xs)) :=
        (tupleEquiv a E ρ).iSup_comp.symm
      _ = _ := by
        apply iSup_congr
        intro xs
        rw [blockMap_ofIEnv, smallForm_correct p]

/-- Substitution respects an arbitrary Boolean degree of componentwise equality. -/
theorem smallValue_congr {Γ : Ctx} (φ : SmallFormula Γ) (g h : IEnv (Dom a E) Γ)
    {q : B} (hgh : ∀ σ (v : Var Γ σ),
      q ≤ (DomSpace a E σ).space.eqv (g.get v) (h.get v)) :
    q ≤ iffValue (smallValue a E φ g) (smallValue a E φ h) := by
  have hc := (smallForm a E φ).pred.congr (ofIEnv a E g) (ofIEnv a E h)
  change (EnvSpace.{0} a E Γ).space.eqv (ofIEnv a E g) (ofIEnv a E h) ≤
    iffValue (smallForm a E φ (ofIEnv a E g)) (smallForm a E φ (ofIEnv a E h)) at hc
  rw [smallForm_correct, smallForm_correct] at hc
  exact (envEq_of_get a E g h hgh).trans hc

theorem smallValue_semilinear {Γ : Ctx} (φ : SmallFormula Γ)
    (π : Equiv.Perm K) (g : IEnv (Dom a E) Γ) :
    smallValue a E φ (envAction a E π g) = a.map π (smallValue a E φ g) := by
  rw [← smallForm_correct, ofIEnv_action, (smallForm a E φ).equivariant,
    smallForm_correct]

theorem smallValue_finitelySupported {Γ : Ctx} (φ : SmallFormula Γ)
    (g : IEnv (Dom a E) Γ) : a.toAction.FinitelySupported (smallValue a E φ g) := by
  obtain ⟨S, hS, hg⟩ := env_finitelySupported.{0} a E Γ (ofIEnv a E g)
  refine ⟨S, hS, ?_⟩
  intro π hπ
  change a.map π (smallValue a E φ g) = smallValue a E φ g
  calc
    _ = a.map π (smallForm a E φ (ofIEnv a E g)) :=
      congrArg (a.map π) (smallForm_correct a E φ g).symm
    _ = smallForm a E φ ((EnvSpace.{0} a E Γ).action.act π (ofIEnv a E g)) :=
      ((smallForm a E φ).equivariant π (ofIEnv a E g)).symm
    _ = smallForm a E φ (ofIEnv a E g) := congrArg (smallForm a E φ) (hg π hπ)
    _ = smallValue a E φ g := smallForm_correct a E φ g

/-- Every actual small formula has an admitted profile, with its exact Boolean values. -/
theorem small_comprehension (Γ : Ctx) (ρ : RTy)
    (φ : SmallFormula (ρ.args ++ Γ)) (g : IEnv (Dom a E) Γ) :
    ∃ F : Dom a E (.rel ρ), ∀ xs : Args (Dom a E) ρ,
      profile a E ρ F xs = smallValue a E φ (appendEnv (argsEnv ρ xs) g) := by
  let body := (smallForm a E φ).pullback (blockMap a E Γ ρ)
  let F := body.curry (env_finitelySupported.{0} a E Γ) (ofIEnv a E g)
  refine ⟨F, ?_⟩
  intro xs
  change smallForm a E φ (blockMap a E Γ ρ (ofIEnv a E g, toTuple a E ρ xs)) = _
  rw [blockMap_ofIEnv, smallForm_correct]

end

end Classicism.Meta.ChoiceBoolean.SmallFormulaSemantics
