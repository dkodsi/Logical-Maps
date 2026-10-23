import Classicism.Results.Research.AtomicProbabilityScalar

/-!
# Canonical finite-support envelopes as functional graphs

Conditional ordinary Lean mathematics, NOT an object-language C certificate.
The finite-support representation and the scalar supremum resource are explicit
parameters. There is no global choice of a supremum function: `Value` is a graph.
In particular these theorems do not establish either of the proposed C-to-real
interpretations in the research notes.

Source: research/2026-10-22/proof-refinements/canonical-atomic-probability.md,
sections 1-3 (unpaginated), and canonical-finite-class-symmetrization.md,
sections 1-2. Direct research source: OpenAI Codex, 22 October 2026.
-/

namespace Classicism.Research.Probability

universe u v w

variable {R : Type u}

/-- Least upper bound, with no choice of a value included in the definition. -/
def IsMassSup (s : MassScalar R) (P : R → Prop) (x : R) : Prop :=
  (∀ y, P y → s.le y x) ∧
  (∀ z, (∀ y, P y → s.le y z) → s.le x z)

theorem massSup_unique (s : MassScalar R) {P : R → Prop} {x y : R}
    (hx : IsMassSup s P x) (hy : IsMassSup s P y) : x = y :=
  s.le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

/-- Conditional scalar completeness; not asserted of any constructed C code. -/
def HasBoundedMassSuprema (s : MassScalar R) : Prop :=
  ∀ P : R → Prop, (∃ x, P x) →
    (∃ b, ∀ x, P x → s.le x b) → ∃ x, IsMassSup s P x

/-- The exact finite-support operations needed for disjoint additivity.

For the intended interpretation, K is the field of finite atom subsets, `below`
means containment below an event, and `mass` is the finite sum of atom weights.
That interpretation, including `split` and `merge`, has NOT been constructed here.
-/
structure FiniteSupportSystem (s : MassScalar R) (E : Type v) (K : Type w) where
  bottom : E
  join : E → E → E
  disjoint : E → E → Prop
  below : K → E → Prop
  mass : K → R
  empty : K
  empty_below : ∀ p, below empty p
  empty_mass : mass empty = s.zero
  bottom_mass : ∀ k, below k bottom → mass k = s.zero
  split : ∀ p q, disjoint p q → ∀ k, below k (join p q) →
    ∃ i j, below i p ∧ below j q ∧ mass k = s.add (mass i) (mass j)
  merge : ∀ p q, disjoint p q → ∀ i j, below i p → below j q →
    ∃ k, below k (join p q) ∧ mass k = s.add (mass i) (mass j)

namespace FiniteSupportSystem

variable {s : MassScalar R} {E : Type v} {K : Type w}
variable (F : FiniteSupportSystem s E K)

def Values (p : E) (x : R) : Prop := ∃ k, F.below k p ∧ x = F.mass k

/-- The canonical atomic value graph. -/
def Value (p : E) (x : R) : Prop := IsMassSup s (F.Values p) x

theorem upper {p : E} {x : R} (hx : F.Value p x) {k : K}
    (hk : F.below k p) : s.le (F.mass k) x :=
  hx.1 (F.mass k) ⟨k, hk, rfl⟩

theorem least {p : E} {x : R} (hx : F.Value p x) (b : R)
    (hb : ∀ k, F.below k p → s.le (F.mass k) b) : s.le x b := by
  apply hx.2 b
  intro y hy
  obtain ⟨k, hk, rfl⟩ := hy
  exact hb k hk

theorem value_unique {p : E} {x y : R} (hx : F.Value p x)
    (hy : F.Value p y) : x = y := massSup_unique s hx hy

theorem value_exists (hc : HasBoundedMassSuprema s) (p : E) (b : R)
    (hb : ∀ k, F.below k p → s.le (F.mass k) b) :
    ∃ x, F.Value p x := by
  apply hc (F.Values p)
  · exact ⟨F.mass F.empty, F.empty, F.empty_below p, rfl⟩
  · refine ⟨b, ?_⟩
    intro y hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact hb k hk

/-- Totality and single-valuedness of the graph; no operation is selected. -/
theorem graph_total_functional (hc : HasBoundedMassSuprema s) (b : R)
    (hb : ∀ k, s.le (F.mass k) b) :
    ∀ p, ∃ x, F.Value p x ∧ ∀ y, F.Value p y → x = y := by
  intro p
  obtain ⟨x, hx⟩ := F.value_exists hc p b (fun k _ => hb k)
  exact ⟨x, hx, fun y hy => F.value_unique hx hy⟩

theorem value_bottom : F.Value F.bottom s.zero := by
  constructor
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [F.bottom_mass k hk]
    exact s.le_refl _
  · intro b hb
    have h := hb (F.mass F.empty) ⟨F.empty, F.empty_below F.bottom, rfl⟩
    rw [F.empty_mass] at h
    exact h

theorem value_nonnegative {p : E} {x : R} (hx : F.Value p x) :
    s.Nonnegative x := by
  have h := F.upper hx (F.empty_below p)
  rw [F.empty_mass] at h
  exact h

theorem value_le_bound {p : E} {x : R} (hx : F.Value p x) (b : R)
    (hb : ∀ k, F.below k p → s.le (F.mass k) b) : s.le x b :=
  F.least hx b hb

theorem value_mono {p q : E} {x y : R}
    (hx : F.Value p x) (hy : F.Value q y)
    (hpq : ∀ k, F.below k p → F.below k q) : s.le x y := by
  apply F.least hx y
  intro k hk
  exact F.upper hy (hpq k hk)

/-- Splitting and merging finite supports prove finite additivity of the LUB graph. -/
theorem value_add {p q : E} {x y : R} (hd : F.disjoint p q)
    (hx : F.Value p x) (hy : F.Value q y) :
    F.Value (F.join p q) (s.add x y) := by
  constructor
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := hz
    obtain ⟨i, j, hi, hj, hsum⟩ := F.split p q hd k hk
    rw [hsum]
    exact s.add_mono (F.upper hx hi) (F.upper hy hj)
  · intro b hb
    have hpair : ∀ i j, F.below i p → F.below j q →
        s.le (s.add (F.mass i) (F.mass j)) b := by
      intro i j hi hj
      obtain ⟨k, hk, hsum⟩ := F.merge p q hd i j hi hj
      have h := hb (F.mass k) ⟨k, hk, rfl⟩
      rw [hsum] at h
      exact h
    have hleft : ∀ j, F.below j q → s.le (s.add x (F.mass j)) b := by
      intro j hj
      apply (s.add_le_iff_le_sub x (F.mass j) b).mpr
      apply F.least hx (s.sub b (F.mass j))
      intro i hi
      exact (s.add_le_iff_le_sub _ _ _).mp (hpair i j hi hj)
    have hright : s.le y (s.sub b x) := by
      apply F.least hy (s.sub b x)
      intro j hj
      apply (s.add_le_iff_le_sub (F.mass j) x b).mp
      rw [s.add_comm]
      exact hleft j hj
    have h := (s.add_le_iff_le_sub y x b).mpr hright
    rw [s.add_comm] at h
    exact h

theorem value_at_atom (p : E) (a : K) (ha : F.below a p)
    (hmax : ∀ k, F.below k p → s.le (F.mass k) (F.mass a)) :
    F.Value p (F.mass a) := by
  constructor
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact hmax k hk
  · intro b hb
    exact hb (F.mass a) ⟨a, ha, rfl⟩

theorem value_positive {p : E} {x : R} (hx : F.Value p x)
    (hp : ∃ k, F.below k p ∧ s.Positive (F.mass k)) : s.Positive x := by
  obtain ⟨k, hk, hm⟩ := hp
  exact s.positive_of_positive_le hm (F.upper hx hk)

theorem residual_nonnegative {p : E} {x : R} (hx : F.Value p x)
    (mu : E → R) (hm : ∀ k, F.below k p → s.le (F.mass k) (mu p)) :
    s.Nonnegative (s.sub (mu p) x) :=
  s.sub_nonnegative (F.least hx (mu p) hm)

theorem residual_add {p q : E} {x y z : R} (hd : F.disjoint p q)
    (hx : F.Value p x) (hy : F.Value q y) (hz : F.Value (F.join p q) z)
    (mu : E → R) (hm : mu (F.join p q) = s.add (mu p) (mu q)) :
    s.sub (mu (F.join p q)) z = s.add (s.sub (mu p) x) (s.sub (mu q) y) := by
  have hv := F.value_unique hz (F.value_add hd hx hy)
  rw [hm, hv, s.sub_add_sub]

theorem residual_atom_zero {p : E} {x : R} (hx : F.Value p x)
    (a : K) (ha : F.below a p)
    (hmax : ∀ k, F.below k p → s.le (F.mass k) (F.mass a))
    (mu : E → R) (hm : mu p = F.mass a) : s.sub (mu p) x = s.zero := by
  have hv := F.value_unique hx (F.value_at_atom p a ha hmax)
  rw [hm, hv, s.sub_self]

end FiniteSupportSystem

/-- Cofinal domination of finite subsums suffices for comparison of atomic envelopes. -/
theorem massSup_le_of_cofinal (s : MassScalar R) {P Q : R → Prop} {x y : R}
    (hx : IsMassSup s P x) (hy : IsMassSup s Q y)
    (h : ∀ a, P a → ∃ b, Q b ∧ s.le a b) : s.le x y := by
  apply hx.2 y
  intro a ha
  obtain ⟨b, hb, hab⟩ := h a ha
  exact s.le_trans hab (hy.1 b hb)

theorem massSup_eq_of_mutually_cofinal (s : MassScalar R)
    {P Q : R → Prop} {x y : R} (hx : IsMassSup s P x) (hy : IsMassSup s Q y)
    (hpq : ∀ a, P a → ∃ b, Q b ∧ s.le a b)
    (hqp : ∀ b, Q b → ∃ a, P a ∧ s.le b a) : x = y :=
  s.le_antisymm (massSup_le_of_cofinal s hx hy hpq)
    (massSup_le_of_cofinal s hy hx hqp)

end Classicism.Research.Probability
