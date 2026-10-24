import Classicism.Results.Research.AtomicProbabilityEnvelope

/-!
# Normalizing an atomic envelope by an additive order isomorphism

Conditional ordinary Lean. The isomorphism is supplied explicitly: for positive
real total mass t, its intended realization is x ↦ x/t. No real field, division
by a real, C interpretation, or internal-code instance is asserted here.
This separates the normalization step from the unnormalized canonical atomic
part and prevents an incorrect claim that normalization preserves raw masses.

Source: canonical-atomic-probability.md, sections 2-3, and
canonical-finite-class-symmetrization.md, sections 1-2, unpaginated local research.
-/

namespace Classicism.Research.Probability

universe u v w

variable {R : Type u} {s : MassScalar R}

/-- A positive scaling abstracted as an additive order isomorphism. -/
structure PositiveScale (s : MassScalar R) where
  forward : R → R
  inverse : R → R
  inverse_forward : ∀ x, inverse (forward x) = x
  forward_inverse : ∀ x, forward (inverse x) = x
  map_zero : forward s.zero = s.zero
  map_add : ∀ x y, forward (s.add x y) = s.add (forward x) (forward y)
  le_map_iff : ∀ x y, s.le (forward x) (forward y) ↔ s.le x y

namespace PositiveScale

variable (T : PositiveScale s)

theorem monotone {x y : R} (h : s.le x y) : s.le (T.forward x) (T.forward y) :=
  (T.le_map_iff x y).mpr h

theorem injective {x y : R} (h : T.forward x = T.forward y) : x = y := by
  have h' := congrArg T.inverse h
  rw [T.inverse_forward, T.inverse_forward] at h'
  exact h'

theorem positive {x : R} (hx : s.Positive x) : s.Positive (T.forward x) := by
  refine ⟨?_, ?_⟩
  · have h := T.monotone hx.1
    rw [T.map_zero] at h
    exact h
  · intro h
    apply hx.2
    apply T.injective
    exact h.trans T.map_zero.symm

/-- Positive scaling preserves arbitrary represented suprema, not just finite sums. -/
theorem map_sup {P : R → Prop} {x : R} (hx : IsMassSup s P x) :
    IsMassSup s (fun z => ∃ y, P y ∧ z = T.forward y) (T.forward x) := by
  constructor
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact T.monotone (hx.1 y hy)
  · intro b hb
    have hxb : s.le x (T.inverse b) := by
      apply hx.2 (T.inverse b)
      intro y hy
      apply (T.le_map_iff y (T.inverse b)).mp
      rw [T.forward_inverse]
      exact hb (T.forward y) ⟨y, hy, rfl⟩
    have h := T.monotone hxb
    rw [T.forward_inverse] at h
    exact h

end PositiveScale

namespace FiniteSupportSystem

variable {E : Type v} {K : Type w}
variable (F : FiniteSupportSystem s E K) (T : PositiveScale s)

def scaled : FiniteSupportSystem s E K where
  bottom := F.bottom
  join := F.join
  disjoint := F.disjoint
  below := F.below
  mass := fun k => T.forward (F.mass k)
  empty := F.empty
  empty_below := F.empty_below
  empty_mass := by rw [F.empty_mass, T.map_zero]
  bottom_mass := by
    intro k hk
    rw [F.bottom_mass k hk, T.map_zero]
  split := by
    intro p q hd k hk
    obtain ⟨i, j, hi, hj, he⟩ := F.split p q hd k hk
    refine ⟨i, j, hi, hj, ?_⟩
    rw [he, T.map_add]
  merge := by
    intro p q hd i j hi hj
    obtain ⟨k, hk, he⟩ := F.merge p q hd i j hi hj
    refine ⟨k, hk, ?_⟩
    rw [he, T.map_add]

theorem scaled_value {p : E} {x : R} (hx : F.Value p x) :
    (F.scaled T).Value p (T.forward x) := by
  constructor
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact T.monotone (F.upper hx hk)
  · intro b hb
    have hxb : s.le x (T.inverse b) := by
      apply F.least hx (T.inverse b)
      intro k hk
      apply (T.le_map_iff (F.mass k) (T.inverse b)).mp
      rw [T.forward_inverse]
      exact hb (T.forward (F.mass k)) ⟨k, hk, rfl⟩
    have h := T.monotone hxb
    rw [T.forward_inverse] at h
    exact h

/-- A supplied positive scaling normalizes the value at the chosen top event,
preserving finite additivity and faithfulness on the stated nonzero events.

`hfaithful` and the scalar scaling are explicit inputs; this theorem does not
claim that dividing by the total preserves the old, unnormalized atom masses.
-/
theorem normalize_atomic_state (v : E → R) (hv : ∀ p, F.Value p (v p))
    (top : E) (one : R) (hnorm : T.forward (v top) = one)
    (nonzero : E → Prop) (hfaithful : ∀ p, nonzero p → s.Positive (v p)) :
    T.forward (v top) = one ∧
    (∀ p, (F.scaled T).Value p (T.forward (v p))) ∧
    (∀ p q, F.disjoint p q → T.forward (v (F.join p q)) =
      s.add (T.forward (v p)) (T.forward (v q))) ∧
    (∀ p, nonzero p → s.Positive (T.forward (v p))) := by
  refine ⟨hnorm, fun p => F.scaled_value T (hv p), ?_, ?_⟩
  · intro p q hd
    have he := F.value_unique (hv (F.join p q)) (F.value_add hd (hv p) (hv q))
    rw [he, T.map_add]
  · intro p hp
    exact T.positive (hfaithful p hp)

end FiniteSupportSystem

end Classicism.Research.Probability

#print axioms Classicism.Research.Probability.PositiveScale.map_sup
#print axioms Classicism.Research.Probability.FiniteSupportSystem.normalize_atomic_state
