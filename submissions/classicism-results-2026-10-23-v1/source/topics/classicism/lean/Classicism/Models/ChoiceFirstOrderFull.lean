import Classicism.Models.ChoiceFirstOrderTerms

/-!
# A concrete full hierarchy instantiating the first-order interpretation

Original formalization (misc), 23 October 2026, of the ground hierarchy in
`research/2026-10-22/followup/finite-functional-choice.md` section 1 and the
E₂ interpretation in `research/2026-10-23/finite-choice-forcing-extraction-review.md`
section 2 (both unpaginated).

This is a full hierarchy in the external Lean metatheory. It is an actual
instance of definable comprehension, not an assumed countermodel or a
represented symmetric ZF universe. In particular its external fullness is
compatible with full Choice; the construction supplies no Choice failure.
-/

namespace Classicism.Meta.ChoiceFirstOrder.Full

variable (E : Type)

abbrev Dom (σ : Ty) : Type :=
  @Ty.rec (fun _ => Type) (fun _ => Type)
    E (fun _ A => Set A) (fun _ => E)
    PUnit (fun _ _ X A => X × A) σ

abbrev Tuple (ρ : RTy) : Type :=
  @RTy.rec (fun _ => Type) (fun _ => Type)
    E (fun _ A => Set A) (fun _ => E)
    PUnit (fun _ _ X A => X × A) ρ

def toTuple : ∀ ρ, Args (Dom E) ρ → Tuple E ρ
  | .t, _ => PUnit.unit
  | .arr _ ρ, a => (a.1, toTuple ρ a.2)

def fromTuple : ∀ ρ, Tuple E ρ → Args (Dom E) ρ
  | .t, _ => PUnit.unit
  | .arr _ ρ, a => (a.1, fromTuple ρ a.2)

theorem to_from : ∀ ρ (a : Tuple E ρ), toTuple E ρ (fromTuple E ρ a) = a
  | .t, a => by cases a; rfl
  | .arr _ ρ, a => by
    change (a.1, toTuple E ρ (fromTuple E ρ a.2)) = a
    rw [to_from ρ a.2]

theorem from_to : ∀ ρ (a : Args (Dom E) ρ), fromTuple E ρ (toTuple E ρ a) = a
  | .t, a => by cases a; rfl
  | .arr _ ρ, a => by
    change (a.1, fromTuple E ρ (toTuple E ρ a.2)) = a
    rw [from_to ρ a.2]

def fullStructure (hne : Nonempty E) : Structure where
  D := Dom E
  rel ρ X a := toTuple E ρ a ∈ X
  rel_injective ρ := by
    intro X Y h
    ext a
    have ha := congrFun h (fromTuple E ρ a)
    change (toTuple E ρ (fromTuple E ρ a) ∈ X) =
      (toTuple E ρ (fromTuple E ρ a) ∈ Y) at ha
    rw [to_from] at ha
    exact Iff.of_eq ha
  nonempty_e := hne

/-- Every explicit first-order comprehension instance is realized by an
actual subset, with its original parameter assignment. -/
theorem comprehension (hne : Nonempty E) : Comprehension (fullStructure E hne) := by
  intro V ρ φ η
  refine ⟨{a | φ.Realize (fullStructure E hne) (extendEnv η ρ (fromTuple E ρ a))}, ?_⟩
  intro a
  change Args (Dom E) ρ at a
  change (∀ σ, V σ → Dom E σ) at η
  exact Iff.of_eq (congrArg
    (fun xs : Args (Dom E) ρ =>
      φ.Realize (fullStructure E hne) (extendEnv η ρ xs))
    (from_to E ρ a))

/-- A concrete `IsModel` certificate through the first-order interpretation,
with no term-closure or model-existence hypothesis. -/
theorem isModel (hne : Nonempty E) : (fullStructure E hne).model.IsModel :=
  ChoiceFirstOrder.isModel (fullStructure E hne) (comprehension E hne)

/-- Arbitrary external functions with relational output have their actual
curried graph in this full hierarchy. This is the positive full-model case. -/
def operation (σ : Ty) (ρ : RTy) (f : Dom E σ → Dom E (.rel ρ)) : Dom E (σ ⇒ ρ) :=
  fun a => a.2 ∈ f a.1

theorem operation_apply (σ : Ty) (ρ : RTy) (f : Dom E σ → Dom E (.rel ρ))
    (x : Dom E σ) (a : Tuple E ρ) : (x, a) ∈ operation E σ ρ f ↔ a ∈ f x :=
  Iff.rfl

/-- Serial rows in the external full hierarchy have an admitted selecting
operation. This invokes ordinary external Choice, as expected for this
positive witness; it is not a shallow C derivation or a negative example. -/
theorem serial_has_operation (σ : Ty) (ρ : RTy)
    (R : Dom E σ → Dom E (.rel ρ) → Prop)
    (hR : ∀ x, ∃ y, R x y) :
    ∃ F : Dom E (σ ⇒ ρ), ∀ x, ∃ y, R x y ∧
      ∀ a : Tuple E ρ, (x, a) ∈ F ↔ a ∈ y := by
  classical
  let f : Dom E σ → Dom E (.rel ρ) := fun x => Classical.choose (hR x)
  exact ⟨operation E σ ρ f, fun x =>
    ⟨f x, Classical.choose_spec (hR x), fun _ => Iff.rfl⟩⟩

end Classicism.Meta.ChoiceFirstOrder.Full
