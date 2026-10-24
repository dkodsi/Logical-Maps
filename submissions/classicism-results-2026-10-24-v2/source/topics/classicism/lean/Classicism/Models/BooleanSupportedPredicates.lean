import Classicism.Models.BooleanValuedEquality
import Mathlib.Algebra.Group.End
import Mathlib.Data.Set.Finite.Basic

/-!
# Semilinear actions and supported coherent predicates

Original supporting formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md`, sections 3--4
(unpaginated). Boolean automorphisms act on both the carrier and truth
values. The predicate action is the actual conjugation formula, and its
finite-support restriction contains every coherent predicate with some
finite support.

These constructors make no mixing, Choice, model-existence, or separating
verdict assumption. They do not construct the condition Boolean algebra,
prove the protected-table coverage lemma, or assemble the typed hierarchy.
-/

namespace Classicism.Meta.ChoiceBoolean

universe u v w z

variable {K : Type z} {B : Type u} [CompleteBooleanAlgebra B]

/-- A permutation action with its actual action laws. -/
structure PermutationAction (K : Type z) (M : Type v) where
  act : Equiv.Perm K → M → M
  one_act : ∀ x, act 1 x = x
  mul_act : ∀ π σ x, act (π * σ) x = act π (act σ x)

namespace PermutationAction

variable {M : Type v} (a : PermutationAction K M)

theorem inv_act_act (π : Equiv.Perm K) (x : M) :
    a.act π⁻¹ (a.act π x) = x := by
  rw [← a.mul_act, inv_mul_cancel, a.one_act]

theorem act_inv_act (π : Equiv.Perm K) (x : M) :
    a.act π (a.act π⁻¹ x) = x := by
  rw [← a.mul_act, mul_inv_cancel, a.one_act]

def actEquiv (π : Equiv.Perm K) : M ≃ M where
  toFun := a.act π
  invFun := a.act π⁻¹
  left_inv := a.inv_act_act π
  right_inv := a.act_inv_act π

/-- A permutation fixes each member of the indicated set of indices. -/
def Fixes (π : Equiv.Perm K) (S : Set K) : Prop := ∀ k ∈ S, π k = k

/-- Support is literal invariance of an entity under its pointwise stabilizer. -/
def Supports (S : Set K) (x : M) : Prop :=
  ∀ π, Fixes π S → a.act π x = x

def FinitelySupported (x : M) : Prop :=
  ∃ S : Set K, S.Finite ∧ a.Supports S x

theorem supports_mono {S T : Set K} {x : M}
    (h : a.Supports S x) (hST : S ⊆ T) : a.Supports T x := by
  intro π hπ
  exact h π (fun k hk => hπ k (hST hk))

/-- Conjugating a pointwise stabilizer transports its support by the permutation. -/
theorem supports_act {S : Set K} {x : M} (h : a.Supports S x)
    (π : Equiv.Perm K) : a.Supports (π '' S) (a.act π x) := by
  intro σ hσ
  have hc : Fixes (π⁻¹ * σ * π) S := by
    intro k hk
    change π.symm (σ (π k)) = k
    rw [hσ (π k) ⟨k, hk, rfl⟩]
    exact π.symm_apply_apply k
  have hm : π * (π⁻¹ * σ * π) = σ * π := by
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  calc
    a.act σ (a.act π x) = a.act (σ * π) x := (a.mul_act σ π x).symm
    _ = a.act π (a.act (π⁻¹ * σ * π) x) := by rw [← a.mul_act, hm]
    _ = a.act π x := congrArg (a.act π) (h _ hc)

theorem finitelySupported_act {x : M} (h : a.FinitelySupported x)
    (π : Equiv.Perm K) : a.FinitelySupported (a.act π x) := by
  obtain ⟨S, hS, hx⟩ := h
  exact ⟨π '' S, hS.image π, a.supports_act hx π⟩

end PermutationAction

/-- An action by order automorphisms of the complete Boolean algebra.
Order isomorphisms preserve all Boolean operations and all indexed meets/joins. -/
structure BooleanAction (K : Type z) (B : Type u) [CompleteBooleanAlgebra B] where
  map : Equiv.Perm K → B ≃o B
  map_one : ∀ b, map 1 b = b
  map_mul : ∀ π σ b, map (π * σ) b = map π (map σ b)

namespace BooleanAction

variable (a : BooleanAction K B)

def toAction : PermutationAction K B where
  act π b := a.map π b
  one_act := a.map_one
  mul_act := a.map_mul

theorem map_inv_map (π : Equiv.Perm K) (b : B) :
    a.map π⁻¹ (a.map π b) = b := a.toAction.inv_act_act π b

theorem map_map_inv (π : Equiv.Perm K) (b : B) :
    a.map π (a.map π⁻¹ b) = b := a.toAction.act_inv_act π b

private theorem map_iffValue_le (e : B ≃o B) (b c : B) :
    e (iffValue b c) ≤ iffValue (e b) (e c) := by
  apply le_iffValue_iff.mpr
  constructor
  · rw [← e.map_inf]
    exact e.monotone (iffValue_inf_left b c)
  · rw [← e.map_inf]
    exact e.monotone (iffValue_inf_right b c)

theorem map_iffValue (π : Equiv.Perm K) (b c : B) :
    a.map π (iffValue b c) = iffValue (a.map π b) (a.map π c) := by
  apply le_antisymm (map_iffValue_le _ _ _)
  have h := (a.map π).monotone
    (map_iffValue_le (a.map π).symm (a.map π b) (a.map π c))
  simpa only [OrderIso.apply_symm_apply, OrderIso.symm_apply_apply] using h

end BooleanAction

/-- An actual equality space with a semilinear permutation action. -/
structure ActionSpace (a : BooleanAction K B) where
  space : EqualitySpace.{u, v} B
  action : PermutationAction K space.Carrier
  semilinear : ∀ π x y,
    space.eqv (action.act π x) (action.act π y) = a.map π (space.eqv x y)

namespace ActionSpace

variable {a : BooleanAction K B}

/-- The crisp base with the trivial carrier action. -/
noncomputable def crisp (a : BooleanAction K B) (M : Type v) : ActionSpace a := by
  classical
  exact
    { space := crispSpace M
      action :=
        { act := fun _ x => x
          one_act := fun _ => rfl
          mul_act := fun _ _ _ => rfl }
      semilinear := by
        intro π x y
        change (if x = y then (⊤ : B) else ⊥) =
          a.map π (if x = y then (⊤ : B) else ⊥)
        by_cases h : x = y
        · simp only [if_pos h, (a.map π).map_top]
        · simp only [if_neg h, (a.map π).map_bot] }

theorem crisp_finitelySupported (a : BooleanAction K B) (M : Type v) (x : M) :
    (crisp a M).action.FinitelySupported x :=
  ⟨∅, Set.finite_empty, fun _ _ => rfl⟩

/-- Boolean values carry the supplied Boolean action. -/
def truth (a : BooleanAction K B) : ActionSpace a where
  space := truthSpace
  action := a.toAction
  semilinear π x y := (a.map_iffValue π x y).symm

/-- The diagonal action on a product of equality spaces. -/
def product (X : ActionSpace a) (Y : ActionSpace a) : ActionSpace a where
  space := prod X.space Y.space
  action :=
    { act := fun π p => (X.action.act π p.1, Y.action.act π p.2)
      one_act := by intro p; exact Prod.ext (X.action.one_act p.1) (Y.action.one_act p.2)
      mul_act := by
        intro π σ p
        exact Prod.ext (X.action.mul_act π σ p.1) (Y.action.mul_act π σ p.2) }
  semilinear π p q := by
    change X.space.eqv (X.action.act π p.1) (X.action.act π q.1) ⊓
      Y.space.eqv (Y.action.act π p.2) (Y.action.act π q.2) =
      a.map π (X.space.eqv p.1 q.1 ⊓ Y.space.eqv p.2 q.2)
    rw [X.semilinear, Y.semilinear, (a.map π).map_inf]

theorem product_supports (X : ActionSpace a) (Y : ActionSpace a) {S T : Set K}
    {x : X.space.Carrier} {y : Y.space.Carrier}
    (hx : X.action.Supports S x) (hy : Y.action.Supports T y) :
    (product X Y).action.Supports (S ∪ T) (x, y) := by
  intro π hπ
  exact Prod.ext (hx π (fun k hk => hπ k (Or.inl hk)))
    (hy π (fun k hk => hπ k (Or.inr hk)))

theorem product_finitelySupported (X : ActionSpace a) (Y : ActionSpace a)
    {x : X.space.Carrier} {y : Y.space.Carrier}
    (hx : X.action.FinitelySupported x) (hy : Y.action.FinitelySupported y) :
    (product X Y).action.FinitelySupported (x, y) := by
  obtain ⟨S, hS, hx⟩ := hx
  obtain ⟨T, hT, hy⟩ := hy
  exact ⟨S ∪ T, hS.union hT, product_supports X Y hx hy⟩

/-- Restrict any action space to all of its finitely supported entities. -/
def finitePart (X : ActionSpace a) : ActionSpace a where
  space :=
    { Carrier := {x : X.space.Carrier // X.action.FinitelySupported x}
      eqv := fun x y => X.space.eqv x.val y.val
      refl := fun x => X.space.refl x.val
      symm := fun x y => X.space.symm x.val y.val
      trans := fun x y z => X.space.trans x.val y.val z.val }
  action :=
    { act := fun π x => ⟨X.action.act π x.val, X.action.finitelySupported_act x.property π⟩
      one_act := by intro x; apply Subtype.ext; exact X.action.one_act x.val
      mul_act := by intro π σ x; apply Subtype.ext; exact X.action.mul_act π σ x.val }
  semilinear π x y := X.semilinear π x.val y.val

theorem finitePart_finitelySupported (X : ActionSpace a)
    (x : (finitePart X).space.Carrier) :
    (finitePart X).action.FinitelySupported x := by
  obtain ⟨S, hS, hx⟩ := x.property
  refine ⟨S, hS, ?_⟩
  intro π hπ
  apply Subtype.ext
  exact hx π hπ

end ActionSpace

variable {a : BooleanAction K B}

/-- The semilinear conjugation action on the actual coherent profile. -/
def actPredicate (X : ActionSpace a) (π : Equiv.Perm K) (f : Predicate X.space) :
    Predicate X.space where
  toFun x := a.map π (f (X.action.act π⁻¹ x))
  coherent x y := by
    have he : a.map π (X.space.eqv (X.action.act π⁻¹ x) (X.action.act π⁻¹ y)) =
        X.space.eqv x y := by
      rw [← X.semilinear, X.action.act_inv_act, X.action.act_inv_act]
    have h := (a.map π).monotone
      (f.coherent (X.action.act π⁻¹ x) (X.action.act π⁻¹ y))
    rw [(a.map π).map_inf, he] at h
    exact h

theorem actPredicate_one (X : ActionSpace a) (f : Predicate X.space) :
    actPredicate X 1 f = f := by
  apply Predicate.ext
  intro x
  change a.map 1 (f (X.action.act (1 : Equiv.Perm K)⁻¹ x)) = f x
  rw [inv_one, X.action.one_act, a.map_one]

theorem actPredicate_mul (X : ActionSpace a) (π σ : Equiv.Perm K)
    (f : Predicate X.space) :
    actPredicate X (π * σ) f = actPredicate X π (actPredicate X σ f) := by
  apply Predicate.ext
  intro x
  change a.map (π * σ) (f (X.action.act (π * σ)⁻¹ x)) =
    a.map π (a.map σ (f (X.action.act σ⁻¹ (X.action.act π⁻¹ x))))
  rw [a.map_mul, mul_inv_rev, X.action.mul_act]

def predicateAction (X : ActionSpace a) : PermutationAction K (Predicate X.space) where
  act := actPredicate X
  one_act := actPredicate_one X
  mul_act := actPredicate_mul X

/-- The full coherent predicate space, with its derived semilinear action. -/
def predicateActionSpace (X : ActionSpace a) : ActionSpace a where
  space := predicateSpace X.space
  action := predicateAction X
  semilinear π f g := by
    change Predicate X.space at f g
    change (⨅ x, iffValue (a.map π (f (X.action.act π⁻¹ x)))
        (a.map π (g (X.action.act π⁻¹ x)))) =
      a.map π (⨅ x, iffValue (f x) (g x))
    calc
      _ = ⨅ x, a.map π (iffValue (f (X.action.act π⁻¹ x))
          (g (X.action.act π⁻¹ x))) := by
        apply iInf_congr
        intro x
        exact (a.map_iffValue π _ _).symm
      _ = a.map π (⨅ x, iffValue (f (X.action.act π⁻¹ x))
          (g (X.action.act π⁻¹ x))) := ((a.map π).map_iInf _).symm
      _ = a.map π (⨅ x, iffValue (f x) (g x)) := by
        exact congrArg (a.map π)
          ((X.action.actEquiv π⁻¹).iInf_comp
            (g := fun x : X.space.Carrier => iffValue (f x) (g x)))

/-- All finitely supported coherent predicates, with restricted pointwise equality. -/
def supportedPredicateSpace (X : ActionSpace a) : ActionSpace a :=
  ActionSpace.finitePart (predicateActionSpace X)

abbrev SupportedPredicate (X : ActionSpace a) := (supportedPredicateSpace X).space.Carrier

theorem supportedPredicate_finitelySupported (X : ActionSpace a)
    (f : SupportedPredicate X) :
    (supportedPredicateSpace X).action.FinitelySupported f :=
  ActionSpace.finitePart_finitelySupported (predicateActionSpace X) f

theorem const_supports (X : ActionSpace a) {S : Set K} {b : B}
    (hb : a.toAction.Supports S b) :
    (predicateAction X).Supports S (Predicate.const b) := by
  intro π hπ
  apply Predicate.ext
  intro x
  change a.map π b = b
  exact hb π hπ

/-- Every supported Boolean constant gives an admitted constant profile. -/
def supportedConst (X : ActionSpace a) (b : B)
    (hb : a.toAction.FinitelySupported b) : SupportedPredicate X := by
  refine ⟨Predicate.const b, ?_⟩
  obtain ⟨S, hS, hb⟩ := hb
  exact ⟨S, hS, const_supports X hb⟩

/-- In particular the supported predicate domain is nonempty. -/
def supportedZero (X : ActionSpace a) : SupportedPredicate X :=
  supportedConst X ⊥ ⟨∅, Set.finite_empty, fun π _ => (a.map π).map_bot⟩

/-- Evaluation is semilinear in the predicate and its argument together. -/
theorem actPredicate_eval (X : ActionSpace a) (π : Equiv.Perm K)
    (f : Predicate X.space) (x : X.space.Carrier) :
    actPredicate X π f (X.action.act π x) = a.map π (f x) := by
  change a.map π (f (X.action.act π⁻¹ (X.action.act π x))) = _
  rw [X.action.inv_act_act]

theorem evaluation_supports (X : ActionSpace a) {S T : Set K}
    {f : Predicate X.space} {x : X.space.Carrier}
    (hf : (predicateAction X).Supports S f) (hx : X.action.Supports T x) :
    a.toAction.Supports (S ∪ T) (f x) := by
  intro π hπ
  change a.map π (f x) = f x
  calc
    _ = actPredicate X π f (X.action.act π x) := (actPredicate_eval X π f x).symm
    _ = f x := by
      have hf' : actPredicate X π f = f := hf π (fun k hk => hπ k (Or.inl hk))
      rw [hf', hx π (fun k hk => hπ k (Or.inr hk))]

theorem evaluation_finitelySupported (X : ActionSpace a) (f : SupportedPredicate X)
    {x : X.space.Carrier} (hx : X.action.FinitelySupported x) :
    a.toAction.FinitelySupported (Predicate.toFun (X := X.space) f.val x) := by
  obtain ⟨S, hS, hf⟩ := f.property
  obtain ⟨T, hT, hx⟩ := hx
  exact ⟨S ∪ T, hS.union hT, evaluation_supports X hf hx⟩

/-- Slicing commutes with the semilinear action. -/
theorem actPredicate_sectionLeft (X : ActionSpace a) (Y : ActionSpace a) (π : Equiv.Perm K)
    (f : Predicate (prod X.space Y.space)) (x : X.space.Carrier) :
    actPredicate Y π (Predicate.sectionLeft f x) =
      Predicate.sectionLeft (actPredicate (ActionSpace.product X Y) π f)
        (X.action.act π x) := by
  apply Predicate.ext
  intro y
  change a.map π (f (x, Y.action.act π⁻¹ y)) =
    a.map π (f (X.action.act π⁻¹ (X.action.act π x), Y.action.act π⁻¹ y))
  rw [X.action.inv_act_act]

theorem sectionLeft_supports (X : ActionSpace a) (Y : ActionSpace a) {S T : Set K}
    {f : Predicate (prod X.space Y.space)} {x : X.space.Carrier}
    (hf : (predicateAction (ActionSpace.product X Y)).Supports S f)
    (hx : X.action.Supports T x) :
    (predicateAction Y).Supports (S ∪ T) (Predicate.sectionLeft f x) := by
  intro π hπ
  change actPredicate Y π (Predicate.sectionLeft f x) = _
  rw [actPredicate_sectionLeft]
  exact congrArg₂
    (fun (F : Predicate (prod X.space Y.space)) (u : X.space.Carrier) => F.sectionLeft u)
    (hf π (fun k hk => hπ k (Or.inl hk)))
    (hx π (fun k hk => hπ k (Or.inr hk)))

/-- Slicing a supported profile at a supported argument is an admitted profile. -/
def supportedSectionLeft (X : ActionSpace a) (Y : ActionSpace a)
    (f : SupportedPredicate (ActionSpace.product X Y))
    (x : X.space.Carrier) (hx : X.action.FinitelySupported x) : SupportedPredicate Y := by
  refine ⟨Predicate.sectionLeft f.val x, ?_⟩
  obtain ⟨S, hS, hf⟩ := f.property
  obtain ⟨T, hT, hx⟩ := hx
  exact ⟨S ∪ T, hS.union hT, sectionLeft_supports X Y hf hx⟩

/-- The admitted slicing operation respects equality in both arguments. -/
theorem supportedSectionLeft_congr (X : ActionSpace a) (Y : ActionSpace a)
    (f g : SupportedPredicate (ActionSpace.product X Y))
    (x y : X.space.Carrier)
    (hx : X.action.FinitelySupported x) (hy : X.action.FinitelySupported y) :
    (supportedPredicateSpace (ActionSpace.product X Y)).space.eqv f g ⊓
      X.space.eqv x y ≤
      (supportedPredicateSpace Y).space.eqv
        (supportedSectionLeft X Y f x hx) (supportedSectionLeft X Y g y hy) := by
  change (predicateSpace (prod X.space Y.space)).eqv f.val g.val ⊓ X.space.eqv x y ≤
    ⨅ z, iffValue (Predicate.toFun (X := prod X.space Y.space) f.val (x, z))
      (Predicate.toFun (X := prod X.space Y.space) g.val (y, z))
  apply le_iInf
  intro z
  have h := eval_congr (X := prod X.space Y.space) f.val g.val (x, z) (y, z)
  simpa only [prod, Y.space.refl, inf_top_eq] using h

/-- Evaluation on the restricted predicate space is itself empty-supported. -/
def supportedEvaluation (X : ActionSpace a) :
    SupportedPredicate (ActionSpace.product (supportedPredicateSpace X) X) := by
  let f : Predicate (prod (supportedPredicateSpace X).space X.space) :=
    { toFun := fun p => Predicate.toFun (X := X.space) p.1.val p.2
      coherent := fun p q => eval_subst p.1.val q.1.val p.2 q.2 }
  refine ⟨f, ∅, Set.finite_empty, ?_⟩
  intro π _
  apply Predicate.ext
  intro p
  change SupportedPredicate X × X.space.Carrier at p
  rcases p with ⟨P, x⟩
  change a.map π (actPredicate X π⁻¹ P.val (X.action.act π⁻¹ x)) =
    Predicate.toFun (X := X.space) P.val x
  exact (congrArg (a.map π) (actPredicate_eval X π⁻¹ P.val x)).trans
    (a.map_map_inv π (Predicate.toFun (X := X.space) P.val x))

end Classicism.Meta.ChoiceBoolean
