import Classicism.Principles.Coarse
import Classicism.Principles.Lattice

/-!
# Full composite logical observers

Direct source: `research/2026-10-23/operator-characterizations/positive-operator-representation.txt`,
sections 1--3 (misc, 23 October 2026, unpaginated).
The equalities below are identities of the entire composite operations.
Type parameters are metalinguistic; no object quantifier ranges over types.
-/

namespace Classicism.Research.FullLogicalObservers
open Classicism.P Classicism.Paper

def BoolFull (O : Prop → Prop) : Prop :=
  O True = True ∧ O False = False ∧
  (fun p : Prop => O (¬ p)) = (fun p : Prop => ¬ O p) ∧
  (fun p q : Prop => O (p ∧ q)) = (fun p q : Prop => O p ∧ O q) ∧
  (fun p q : Prop => O (p ∨ q)) = (fun p q : Prop => O p ∨ O q)

def QuantifierFull (σ : Type) [Ty σ] (O : Prop → Prop) : Prop :=
  (fun F : σ → Prop => O (∀ x, F x)) =
    (fun F : σ → Prop => ∀ x, O (F x)) ∧
  (fun F : σ → Prop => O (∃ x, F x)) =
    (fun F : σ → Prop => ∃ x, O (F x))

def QualifiedFull (σ : Type) [Ty σ] (O : Prop → Prop) : Prop :=
  BoolFull O ∧ QuantifierFull σ O

def SeparationBy (X : (Prop → Prop) → Prop) : Prop :=
  ∀ p q : Prop, p = q ↔ ∀ O : Prop → Prop, (BoolFull O ∧ X O) → O (p ↔ q)

def SeparationFull (σ : Type) [Ty σ] : Prop :=
  ∀ p q : Prop, p = q ↔ ∀ O : Prop → Prop, QualifiedFull σ O → O (p ↔ q)

theorem boolFull_top {O : Prop → Prop} (h : BoolFull O) : O True = True := h.1
theorem boolFull_bot {O : Prop → Prop} (h : BoolFull O) : O False = False := h.2.1
theorem boolFull_not {O : Prop → Prop} (h : BoolFull O) (p : Prop) :
    O (¬ p) = ¬ O p := congrFun h.2.2.1 p
theorem boolFull_and {O : Prop → Prop} (h : BoolFull O) (p q : Prop) :
    O (p ∧ q) = (O p ∧ O q) := congrFun (congrFun h.2.2.2.1 p) q
theorem boolFull_or {O : Prop → Prop} (h : BoolFull O) (p q : Prop) :
    O (p ∨ q) = (O p ∨ O q) := congrFun (congrFun h.2.2.2.2 p) q
theorem quantifierFull_forall {σ : Type} [Ty σ] {O : Prop → Prop}
    (h : QuantifierFull σ O) (F : σ → Prop) :
    O (∀ x, F x) = (∀ x, O (F x)) := congrFun h.1 F
theorem quantifierFull_exists {σ : Type} [Ty σ] {O : Prop → Prop}
    (h : QuantifierFull σ O) (F : σ → Prop) :
    O (∃ x, F x) = (∃ x, O (F x)) := congrFun h.2 F

theorem iff_boolean_eq (p q : Prop) :
    (p ↔ q) = ((p ∧ q) ∨ (¬ p ∧ ¬ q)) :=
  propext ⟨fun h => (em p).elim (fun hp => Or.inl ⟨hp, h.1 hp⟩)
    (fun hn => Or.inr ⟨hn, fun hq => hn (h.2 hq)⟩),
    fun h => h.elim (fun h => ⟨fun _ => h.2, fun _ => h.1⟩)
      (fun h => ⟨fun hp => (h.1 hp).elim, fun hq => (h.2 hq).elim⟩)⟩

theorem boolFull_iff {O : Prop → Prop} (h : BoolFull O) (p q : Prop) :
    O (p ↔ q) = (O p ↔ O q) := by
  rw [iff_boolean_eq p q, boolFull_or h, boolFull_and h,
    boolFull_and h, boolFull_not h, boolFull_not h, ← iff_boolean_eq]

end Classicism.Research.FullLogicalObservers
