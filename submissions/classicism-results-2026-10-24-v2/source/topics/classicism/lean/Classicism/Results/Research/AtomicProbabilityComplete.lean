import Classicism.Results.Research.AtomicProbabilityEnvelope

/-!
# Complete additivity of a canonical finite-support envelope

Ordinary conditional algebra, not an object-C theorem. This isolates the full
supremum-of-finite-subsums argument. The exact finite atom-cover property needed
at a represented join is a visible premise, not inferred from an external
powerset or silently assumed of an internal Boolean algebra.

Source: canonical-atomic-probability.md, section 2, unpaginated local research,
OpenAI Codex, 22 October 2026.
-/

namespace Classicism.Research.Probability

universe u v w z

namespace FiniteSupportSystem

variable {R : Type u} {s : MassScalar R} {E : Type v} {K : Type w} {I : Type z}
variable (F : FiniteSupportSystem s E K)

def joinList (f : I → E) : List I → E
  | [] => F.bottom
  | i :: is => F.join (f i) (joinList f is)

/-- A list in which each event is disjoint from the join of its successors. -/
def JoinCompatible (f : I → E) : List I → Prop
  | [] => True
  | i :: is => F.disjoint (f i) (F.joinList f is) ∧ JoinCompatible f is

theorem value_joinList (f : I → E) (v : I → R)
    (hv : ∀ i, F.Value (f i) (v i)) (is : List I)
    (hc : F.JoinCompatible f is) : F.Value (F.joinList f is) (s.sum v is) := by
  revert hc
  induction is with
  | nil => intro hc; exact F.value_bottom
  | cons i is ih =>
    intro hc
    exact F.value_add hc.1 (hv i) (ih hc.2)

/-- The finite-partition argument proves complete additivity in the exact
supremum-of-finite-subsums sense.

For an atomic Boolean interpretation, `hcover` is supplied by: every atom below
the represented join lies below a member, and a finite set of those atoms has
a finite set of member indices. That representation proof is NOT part of this
conditional theorem. `hupper` says that finite subjoins are below the given join.
-/
theorem completely_additive_graph (f : I → E) (v : I → R)
    (hv : ∀ i, F.Value (f i) (v i)) (p : E) (x : R) (hx : F.Value p x)
    (hdisjoint : ∀ is : List I, is.Nodup → F.JoinCompatible f is)
    (hupper : ∀ is : List I, is.Nodup → ∀ k,
      F.below k (F.joinList f is) → F.below k p)
    (hcover : ∀ k, F.below k p → ∃ is : List I,
      is.Nodup ∧ F.below k (F.joinList f is)) :
    IsMassSup s (fun r => ∃ is : List I, is.Nodup ∧ r = s.sum v is) x := by
  constructor
  · intro r hr
    obtain ⟨is, hn, rfl⟩ := hr
    exact F.value_mono (F.value_joinList f v hv is (hdisjoint is hn)) hx
      (hupper is hn)
  · intro b hb
    apply F.least hx b
    intro k hk
    obtain ⟨is, hn, hki⟩ := hcover k hk
    have hvalue := F.value_joinList f v hv is (hdisjoint is hn)
    exact s.le_trans (F.upper hvalue hki) (hb (s.sum v is) ⟨is, hn, rfl⟩)

end FiniteSupportSystem

/-- Supremum-defined atomic charges are monotone in their atom weights. -/
theorem atomSum_mono (s : MassScalar R) {A : Type v}
    (admissible : List A → Prop) (c d : A → R)
    (hcd : ∀ a, s.le (c a) (d a)) {x y : R}
    (hx : IsMassSup s (fun r => ∃ xs, admissible xs ∧ r = s.sum c xs) x)
    (hy : IsMassSup s (fun r => ∃ xs, admissible xs ∧ r = s.sum d xs) y) :
    s.le x y := by
  apply massSup_le_of_cofinal s hx hy
  intro r hr
  obtain ⟨xs, hxs, rfl⟩ := hr
  exact ⟨s.sum d xs, ⟨xs, hxs, rfl⟩, s.sum_mono c d xs (fun a _ => hcd a)⟩

/-- Once an atomic expansion is proved, the weights determine the charge. -/
theorem atomSum_unique (s : MassScalar R) {A : Type v}
    (admissible : List A → Prop) (c : A → R) {x y : R}
    (hx : IsMassSup s (fun r => ∃ xs, admissible xs ∧ r = s.sum c xs) x)
    (hy : IsMassSup s (fun r => ∃ xs, admissible xs ∧ r = s.sum c xs) y) :
    x = y := massSup_unique s hx hy

end Classicism.Research.Probability

#print axioms Classicism.Research.Probability.FiniteSupportSystem.completely_additive_graph
#print axioms Classicism.Research.Probability.atomSum_mono
