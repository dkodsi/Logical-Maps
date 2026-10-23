import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.WellFounded

/-!
# Least proper Boolean parts in a supplied well-order

Direct source: `research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md`,
sections 5–6 (misc, 22 October 2026, unpaginated). This module formalizes the ordinary
external algebraic step, not a derivation in the object logic C.

The inputs are a Boolean algebra, atomlessness, and a well-founded relation. Explicit
trichotomy makes its minimal proper parts unique. No selector, selected value, or
splitting conclusion is assumed: the function below is constructed using
`WellFounded.min`, and its properties are proved.

This does not construct a rigid complete atomless Boolean algebra, a code for a set
universe, or a pure object-language definition of the supplied order. In particular,
external classical choice here does not establish an object-language Choice principle.
Completeness of the Boolean algebra is not needed for these lemmas.

Source preparation is not a successful Lean check. The designated serial checker owns
compilation and the final axiom reports.
-/

namespace Classicism.Meta.Research.MaxAtomicityWellOrder

universe u

variable {B : Type u} [BooleanAlgebra B]

/-- A nonzero proper Boolean part, written without introducing another order. -/
def ProperPart (p q : B) : Prop :=
  q ≠ ⊥ ∧ q ≤ p ∧ q ≠ p

/-- The explicit atomlessness property used in the proof. -/
def AtomlessParts (B : Type u) [BooleanAlgebra B] : Prop :=
  ∀ p : B, p ≠ ⊥ → ∃ q : B, ProperPart p q

/-- A proper part with no strictly earlier proper part in the auxiliary relation. -/
def LeastPart (r : B → B → Prop) (p q : B) : Prop :=
  ProperPart p q ∧ ∀ z : B, ProperPart p z → ¬ r z q

/-- Every nonzero element has an auxiliary-order-minimal proper part. -/
theorem exists_leastPart {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) {p : B} (hp : p ≠ ⊥) :
    ∃ q : B, LeastPart r p q := by
  obtain ⟨q, hq, hmin⟩ := wf.has_min {q : B | ProperPart p q} (atomless p hp)
  exact ⟨q, hq, hmin⟩

/-- Trichotomy rules out two different minimal proper parts. -/
theorem leastPart_unique {r : B → B → Prop}
    (total : ∀ x y : B, r x y ∨ x = y ∨ r y x)
    {p q z : B} (hq : LeastPart r p q) (hz : LeastPart r p z) : q = z := by
  rcases total q z with hqz | heq | hzq
  · exact (hz.2 q hq.1 hqz).elim
  · exact heq
  · exact (hq.2 z hz.1 hzq).elim

/-- Existence and uniqueness follow from the supplied well-order and atomlessness. -/
theorem exists_unique_leastPart {r : B → B → Prop} (wf : WellFounded r)
    (total : ∀ x y : B, r x y ∨ x = y ∨ r y x)
    (atomless : AtomlessParts B) {p : B} (hp : p ≠ ⊥) :
    ∃! q : B, LeastPart r p q := by
  obtain ⟨q, hq⟩ := exists_leastPart wf atomless hp
  refine ⟨q, hq, ?_⟩
  intro z hz
  exact leastPart_unique total hz hq

/-- Either Boolean piece determined by a proper nonzero part is nonzero. -/
theorem properPart_splits {p q : B} (hq : ProperPart p q) :
    p ⊓ q ≠ ⊥ ∧ p ⊓ qᶜ ≠ ⊥ := by
  constructor
  · rw [inf_eq_right.mpr hq.2.1]
    exact hq.1
  · intro hz
    have hpq : p = q := by
      calc
        p = (p ⊓ q) ⊔ (p ⊓ qᶜ) := (sup_inf_inf_compl (x := p) (y := q)).symm
        _ = q := by rw [inf_eq_right.mpr hq.2.1, hz, sup_bot_eq]
    exact hq.2.2 hpq.symm

/-- The least proper part is defined from the well-founded relation, not postulated. -/
noncomputable def leastPart {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) (p : B) (hp : p ≠ ⊥) : B :=
  wf.min {q : B | ProperPart p q} (atomless p hp)

/-- The constructed value has exactly the predicate used by the finite selector. -/
theorem leastPart_spec {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) (p : B) (hp : p ≠ ⊥) :
    LeastPart r p (leastPart wf atomless p hp) := by
  constructor
  · exact wf.min_mem {q : B | ProperPart p q} (atomless p hp)
  · intro z hz
    exact wf.not_lt_min {q : B | ProperPart p q} hz

/-- Any value satisfying the least-part predicate is the constructed value. -/
theorem eq_leastPart_of_spec {r : B → B → Prop} (wf : WellFounded r)
    (total : ∀ x y : B, r x y ∨ x = y ∨ r y x)
    (atomless : AtomlessParts B) {p q : B} (hp : p ≠ ⊥)
    (hq : LeastPart r p q) : q = leastPart wf atomless p hp :=
  leastPart_unique total hq (leastPart_spec wf atomless p hp)

/-- Extend the constructed selection to bottom by assigning bottom there. -/
noncomputable def selector {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) (p : B) : B := by
  classical
  exact if hp : p = ⊥ then ⊥ else leastPart wf atomless p hp

theorem selector_bot {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) : selector wf atomless ⊥ = ⊥ := by
  classical
  simp [selector]

theorem selector_eq_leastPart {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) {p : B} (hp : p ≠ ⊥) :
    selector wf atomless p = leastPart wf atomless p hp := by
  classical
  simp only [selector, dif_neg hp]

theorem selector_spec {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) {p : B} (hp : p ≠ ⊥) :
    LeastPart r p (selector wf atomless p) := by
  rw [selector_eq_leastPart wf atomless hp]
  exact leastPart_spec wf atomless p hp

/-- The function actually constructed above splits every nonzero input. -/
theorem selector_splits {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) {p : B} (hp : p ≠ ⊥) :
    p ⊓ selector wf atomless p ≠ ⊥ ∧ p ⊓ (selector wf atomless p)ᶜ ≠ ⊥ :=
  properPart_splits (selector_spec wf atomless hp).1

/-- The bottom-normalized least-part function exists and is unique. -/
theorem exists_unique_selector {r : B → B → Prop} (wf : WellFounded r)
    (total : ∀ x y : B, r x y ∨ x = y ∨ r y x)
    (atomless : AtomlessParts B) :
    ∃! F : B → B, F ⊥ = ⊥ ∧ ∀ p : B, p ≠ ⊥ → LeastPart r p (F p) := by
  refine ⟨selector wf atomless, ?_, ?_⟩
  · exact ⟨selector_bot wf atomless, fun _ hp => selector_spec wf atomless hp⟩
  · intro F hF
    funext p
    classical
    by_cases hp : p = ⊥
    · subst p
      exact hF.1.trans (selector_bot wf atomless).symm
    · exact leastPart_unique total (hF.2 p hp) (selector_spec wf atomless hp)

/-- A splitting function is a conclusion, not an input to the construction. -/
theorem exists_splitter {r : B → B → Prop} (wf : WellFounded r)
    (atomless : AtomlessParts B) :
    ∃ F : B → B, F ⊥ = ⊥ ∧
      ∀ p : B, p ≠ ⊥ → p ⊓ F p ≠ ⊥ ∧ p ⊓ (F p)ᶜ ≠ ⊥ :=
  ⟨selector wf atomless, selector_bot wf atomless, fun _ hp => selector_splits wf atomless hp⟩

end Classicism.Meta.Research.MaxAtomicityWellOrder

#print axioms Classicism.Meta.Research.MaxAtomicityWellOrder.exists_unique_leastPart
#print axioms Classicism.Meta.Research.MaxAtomicityWellOrder.properPart_splits
#print axioms Classicism.Meta.Research.MaxAtomicityWellOrder.leastPart_spec
#print axioms Classicism.Meta.Research.MaxAtomicityWellOrder.selector_splits
#print axioms Classicism.Meta.Research.MaxAtomicityWellOrder.exists_unique_selector
#print axioms Classicism.Meta.Research.MaxAtomicityWellOrder.exists_splitter
