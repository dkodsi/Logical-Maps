import Classicism.Models.BooleanSupportedPredicates
import Classicism.Models.ChoiceFirstOrder

/-!
# The actual supported Boolean hierarchy at every project type

Original supporting formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md`, section 3
(unpaginated). The mutual project type recursor constructs domain and tuple
spaces. Every relational domain consists of all finitely supported coherent
profiles on its recursively constructed argument space.

All carriers live in `Type`; no represented set-theoretic universe is used.
The auxiliary type-variable codes are interpreted by the same crisp base E,
as in `ChoiceFirstOrder.Full`. The original closed types need no such case.
This module proves support, nonemptiness, slicing, and profile equations. It
does not assume or claim a comprehension/model certificate, protected-table
coverage, Choice, or a separating verdict.
-/

namespace Classicism.Meta.ChoiceBoolean.TypedHierarchy

open ChoiceFirstOrder

variable {K B : Type} [CompleteBooleanAlgebra B]
variable (a : BooleanAction K B) (E : Type)

noncomputable section

/-- Domain spaces use the actual mutual type recursor. -/
abbrev DomSpace (σ : Ty) : ActionSpace a :=
  @Ty.rec (fun _ => ActionSpace a) (fun _ => ActionSpace a)
    (ActionSpace.crisp a E) (fun _ A => supportedPredicateSpace A)
    (fun _ => ActionSpace.crisp a E)
    (ActionSpace.crisp a PUnit) (fun _ _ X A => ActionSpace.product X A) σ

/-- The recursively constructed argument space of a relational type. -/
abbrev TupleSpace (ρ : RTy) : ActionSpace a :=
  @RTy.rec (fun _ => ActionSpace a) (fun _ => ActionSpace a)
    (ActionSpace.crisp a E) (fun _ A => supportedPredicateSpace A)
    (fun _ => ActionSpace.crisp a E)
    (ActionSpace.crisp a PUnit) (fun _ _ X A => ActionSpace.product X A) ρ

abbrev Dom (σ : Ty) : Type := (DomSpace a E σ).space.Carrier
abbrev Tuple (ρ : RTy) : Type := (TupleSpace a E ρ).space.Carrier

mutual
  theorem dom_finitelySupported : ∀ σ (x : Dom a E σ),
      (DomSpace a E σ).action.FinitelySupported x
    | .e, x => ActionSpace.crisp_finitelySupported a E x
    | .rel ρ, x => supportedPredicate_finitelySupported (TupleSpace a E ρ) x
    | .var _, x => ActionSpace.crisp_finitelySupported a E x

  theorem tuple_finitelySupported : ∀ ρ (x : Tuple a E ρ),
      (TupleSpace a E ρ).action.FinitelySupported x
    | .t, x => ActionSpace.crisp_finitelySupported a PUnit x
    | .arr σ ρ, x =>
        ActionSpace.product_finitelySupported (DomSpace a E σ) (TupleSpace a E ρ)
          (dom_finitelySupported σ x.1) (tuple_finitelySupported ρ x.2)
end

theorem dom_nonempty (hE : Nonempty E) : ∀ σ, Nonempty (Dom a E σ)
  | .e => hE
  | .rel ρ => ⟨supportedZero (TupleSpace a E ρ)⟩
  | .var _ => hE

theorem tuple_nonempty (hE : Nonempty E) : ∀ ρ, Nonempty (Tuple a E ρ)
  | .t => ⟨PUnit.unit⟩
  | .arr σ ρ => by
    obtain ⟨x⟩ := dom_nonempty a E hE σ
    obtain ⟨xs⟩ := tuple_nonempty hE ρ
    exact ⟨(x, xs)⟩

/-- Relate the project's existing finite argument tuple to the constructed carrier. -/
def toTuple : ∀ ρ, Args (Dom a E) ρ → Tuple a E ρ
  | .t, _ => PUnit.unit
  | .arr _ ρ, xs => (xs.1, toTuple ρ xs.2)

def fromTuple : ∀ ρ, Tuple a E ρ → Args (Dom a E) ρ
  | .t, _ => PUnit.unit
  | .arr _ ρ, xs => (xs.1, fromTuple ρ xs.2)

theorem to_from : ∀ ρ (xs : Tuple a E ρ),
    toTuple a E ρ (fromTuple a E ρ xs) = xs
  | .t, xs => by cases xs; rfl
  | .arr σ ρ, xs => by
    change Dom a E σ × Tuple a E ρ at xs
    rcases xs with ⟨x, xs⟩
    change (x, toTuple a E ρ (fromTuple a E ρ xs)) = (x, xs)
    rw [to_from ρ xs]

theorem from_to : ∀ ρ (xs : Args (Dom a E) ρ),
    fromTuple a E ρ (toTuple a E ρ xs) = xs
  | .t, xs => by cases xs; rfl
  | .arr _ ρ, xs => by
    change (xs.1, fromTuple a E ρ (toTuple a E ρ xs.2)) = xs
    rw [from_to ρ xs.2]

def tupleEquiv (ρ : RTy) : Args (Dom a E) ρ ≃ Tuple a E ρ where
  toFun := toTuple a E ρ
  invFun := fromTuple a E ρ
  left_inv := from_to a E ρ
  right_inv := to_from a E ρ

/-- The componentwise action on the existing argument representation. -/
def argsAction (π : Equiv.Perm K) (ρ : RTy) : Args (Dom a E) ρ → Args (Dom a E) ρ :=
  mapArgs (fun σ x => (DomSpace a E σ).action.act π x) ρ

theorem toTuple_action (π : Equiv.Perm K) : ∀ ρ (xs : Args (Dom a E) ρ),
    toTuple a E ρ (argsAction a E π ρ xs) =
      (TupleSpace a E ρ).action.act π (toTuple a E ρ xs)
  | .t, _ => rfl
  | .arr σ ρ, xs => by
    change ((DomSpace a E σ).action.act π xs.1,
      toTuple a E ρ (argsAction a E π ρ xs.2)) =
      ((DomSpace a E σ).action.act π xs.1,
        (TupleSpace a E ρ).action.act π (toTuple a E ρ xs.2))
    rw [toTuple_action π ρ xs.2]

def argsEq (ρ : RTy) (xs ys : Args (Dom a E) ρ) : B :=
  (TupleSpace a E ρ).space.eqv (toTuple a E ρ xs) (toTuple a E ρ ys)

/-- Actual Boolean profile evaluation, using the existing typed argument representation. -/
def profile (ρ : RTy) (F : Dom a E (.rel ρ)) (xs : Args (Dom a E) ρ) : B :=
  Predicate.toFun (X := (TupleSpace a E ρ).space) F.val (toTuple a E ρ xs)

theorem profile_congr (ρ : RTy) (F G : Dom a E (.rel ρ))
    (xs ys : Args (Dom a E) ρ) :
    (DomSpace a E (.rel ρ)).space.eqv F G ⊓ argsEq a E ρ xs ys ≤
      iffValue (profile a E ρ F xs) (profile a E ρ G ys) := by
  change (predicateSpace (TupleSpace a E ρ).space).eqv F.val G.val ⊓
    (TupleSpace a E ρ).space.eqv (toTuple a E ρ xs) (toTuple a E ρ ys) ≤
      iffValue (Predicate.toFun (X := (TupleSpace a E ρ).space) F.val (toTuple a E ρ xs))
        (Predicate.toFun (X := (TupleSpace a E ρ).space) G.val (toTuple a E ρ ys))
  exact eval_congr (X := (TupleSpace a E ρ).space) F.val G.val
    (toTuple a E ρ xs) (toTuple a E ρ ys)

theorem profile_eqv (ρ : RTy) (F G : Dom a E (.rel ρ)) :
    (DomSpace a E (.rel ρ)).space.eqv F G =
      ⨅ xs : Args (Dom a E) ρ, iffValue (profile a E ρ F xs) (profile a E ρ G xs) := by
  change (⨅ xs : Tuple a E ρ,
    iffValue (Predicate.toFun (X := (TupleSpace a E ρ).space) F.val xs)
      (Predicate.toFun (X := (TupleSpace a E ρ).space) G.val xs)) =
    ⨅ xs : Args (Dom a E) ρ,
      iffValue (Predicate.toFun (X := (TupleSpace a E ρ).space) F.val (toTuple a E ρ xs))
        (Predicate.toFun (X := (TupleSpace a E ρ).space) G.val (toTuple a E ρ xs))
  exact ((tupleEquiv a E ρ).iInf_comp
    (g := fun xs : Tuple a E ρ =>
      iffValue (Predicate.toFun (X := (TupleSpace a E ρ).space) F.val xs)
        (Predicate.toFun (X := (TupleSpace a E ρ).space) G.val xs))).symm

theorem profile_semilinear (π : Equiv.Perm K) (ρ : RTy)
    (F : Dom a E (.rel ρ)) (xs : Args (Dom a E) ρ) :
    profile a E ρ ((DomSpace a E (.rel ρ)).action.act π F) (argsAction a E π ρ xs) =
      a.map π (profile a E ρ F xs) := by
  change Predicate.toFun (X := (TupleSpace a E ρ).space)
      (actPredicate (TupleSpace a E ρ) π F.val)
      (toTuple a E ρ (argsAction a E π ρ xs)) =
    a.map π (Predicate.toFun (X := (TupleSpace a E ρ).space) F.val (toTuple a E ρ xs))
  exact (congrArg
    (Predicate.toFun (X := (TupleSpace a E ρ).space) (actPredicate (TupleSpace a E ρ) π F.val))
    (toTuple_action a E π ρ xs)).trans
      (actPredicate_eval (TupleSpace a E ρ) π F.val (toTuple a E ρ xs))

theorem profile_finitelySupported (ρ : RTy) (F : Dom a E (.rel ρ))
    (xs : Args (Dom a E) ρ) : a.toAction.FinitelySupported (profile a E ρ F xs) :=
  evaluation_finitelySupported (TupleSpace a E ρ) F
    (tuple_finitelySupported a E ρ (toTuple a E ρ xs))

/-- Application is an admitted slice, with finite support already proved. -/
def app (σ : Ty) (ρ : RTy) (F : Dom a E (.rel (σ ⇒ ρ)))
    (x : Dom a E σ) : Dom a E (.rel ρ) :=
  supportedSectionLeft (DomSpace a E σ) (TupleSpace a E ρ) F x
    (dom_finitelySupported a E σ x)

theorem app_profile (σ : Ty) (ρ : RTy) (F : Dom a E (.rel (σ ⇒ ρ)))
    (x : Dom a E σ) (xs : Args (Dom a E) ρ) :
    profile a E ρ (app a E σ ρ F x) xs = profile a E (σ ⇒ ρ) F (x, xs) := rfl

theorem app_congr (σ : Ty) (ρ : RTy) (F G : Dom a E (.rel (σ ⇒ ρ)))
    (x y : Dom a E σ) :
    (DomSpace a E (.rel (σ ⇒ ρ))).space.eqv F G ⊓ (DomSpace a E σ).space.eqv x y ≤
      (DomSpace a E (.rel ρ)).space.eqv (app a E σ ρ F x) (app a E σ ρ G y) :=
  supportedSectionLeft_congr (DomSpace a E σ) (TupleSpace a E ρ) F G x y
    (dom_finitelySupported a E σ x) (dom_finitelySupported a E σ y)

/-- Exact extensionality of slicing, as an equality of Boolean values. -/
theorem app_eqv (σ : Ty) (ρ : RTy) (F G : Dom a E (.rel (σ ⇒ ρ))) :
    (DomSpace a E (.rel (σ ⇒ ρ))).space.eqv F G =
      ⨅ x : Dom a E σ,
        (DomSpace a E (.rel ρ)).space.eqv (app a E σ ρ F x) (app a E σ ρ G x) := by
  change (⨅ p : Dom a E σ × Tuple a E ρ,
    iffValue (Predicate.toFun (X := (TupleSpace a E (σ ⇒ ρ)).space) F.val p)
      (Predicate.toFun (X := (TupleSpace a E (σ ⇒ ρ)).space) G.val p)) =
    ⨅ x : Dom a E σ, ⨅ xs : Tuple a E ρ,
      iffValue (Predicate.toFun (X := (TupleSpace a E (σ ⇒ ρ)).space) F.val (x, xs))
        (Predicate.toFun (X := (TupleSpace a E (σ ⇒ ρ)).space) G.val (x, xs))
  apply le_antisymm
  · apply le_iInf
    intro x
    apply le_iInf
    intro xs
    exact iInf_le _ (x, xs)
  · apply le_iInf
    intro p
    exact (iInf_le _ p.1).trans (iInf_le _ p.2)

theorem app_semilinear (π : Equiv.Perm K) (σ : Ty) (ρ : RTy)
    (F : Dom a E (.rel (σ ⇒ ρ))) (x : Dom a E σ) :
    (DomSpace a E (.rel ρ)).action.act π (app a E σ ρ F x) =
      app a E σ ρ ((DomSpace a E (.rel (σ ⇒ ρ))).action.act π F)
        ((DomSpace a E σ).action.act π x) := by
  apply Subtype.ext
  change actPredicate (TupleSpace a E ρ) π (Predicate.sectionLeft F.val x) =
    Predicate.sectionLeft
      (actPredicate (ActionSpace.product (DomSpace a E σ) (TupleSpace a E ρ)) π F.val)
      ((DomSpace a E σ).action.act π x)
  exact actPredicate_sectionLeft (DomSpace a E σ) (TupleSpace a E ρ) π F.val x

/-- At t, equality is exactly equivalence of the single profile values. -/
theorem truth_eqv (p q : Dom a E .t) :
    (DomSpace a E .t).space.eqv p q =
      iffValue (profile a E .t p PUnit.unit) (profile a E .t q PUnit.unit) := by
  change (⨅ x : PUnit,
    iffValue (Predicate.toFun (X := (TupleSpace a E .t).space) p.val x)
      (Predicate.toFun (X := (TupleSpace a E .t).space) q.val x)) =
    iffValue (Predicate.toFun (X := (TupleSpace a E .t).space) p.val PUnit.unit)
      (Predicate.toFun (X := (TupleSpace a E .t).space) q.val PUnit.unit)
  apply le_antisymm (iInf_le _ PUnit.unit)
  apply le_iInf
  intro x
  cases x
  exact le_rfl

end

end Classicism.Meta.ChoiceBoolean.TypedHierarchy
