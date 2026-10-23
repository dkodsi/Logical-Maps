import Classicism.Results.Research.AtomicProbabilityEnvelope

/-!
# Finite-class averaging without a family of chosen enumerations

Ordinary conditional Lean, not object-language C. Each class is given by the
existence of a duplicate-free finite enumeration. Enumeration witnesses are
eliminated only inside proofs in Prop; no simultaneous enumeration or selector
is constructed. Decidable equality of the external atom type is explicit.

Source: research/2026-10-22/proof-refinements/
canonical-finite-class-symmetrization.md, sections 1-2, unpaginated.
The internal graph/real bridge and arbitrary represented permutation action
on C events remain separate obligations.
-/

namespace Classicism.Research.Probability

universe u v

variable {R : Type u} {A : Type v} {s : MassScalar R}

def ClassEnumeration (r : A → A → Prop) (a : A) (xs : List A) : Prop :=
  xs.Nodup ∧ ∀ b, b ∈ xs ↔ r a b

def FiniteClasses (r : A → A → Prop) : Prop :=
  ∀ a, ∃ xs, ClassEnumeration r a xs

/-- A value relation, rather than a chosen operation on classes. -/
def ClassAverageGraph (d : FiniteDivision s) (r : A → A → Prop)
    (c : A → R) (a : A) (x : R) : Prop :=
  ∃ xs, ClassEnumeration r a xs ∧ x = d.divide (s.sum c xs) xs.length

theorem classEnumeration_perm [DecidableEq A] {r : A → A → Prop}
    {a : A} {xs ys : List A} (hx : ClassEnumeration r a xs)
    (hy : ClassEnumeration r a ys) : xs.Perm ys :=
  enumeration_perm hx.1 hy.1 (fun b => (hx.2 b).trans (hy.2 b).symm)

theorem classAverage_unique [DecidableEq A] (d : FiniteDivision s)
    {r : A → A → Prop} {c : A → R} {a : A} {x y : R}
    (hx : ClassAverageGraph d r c a x) (hy : ClassAverageGraph d r c a y) :
    x = y := by
  obtain ⟨xs, hxs, rfl⟩ := hx
  obtain ⟨ys, hys, rfl⟩ := hy
  have hp := classEnumeration_perm hxs hys
  rw [s.sum_perm c hp, ProbabilityFinite.perm_length hp]

theorem classAverage_total (d : FiniteDivision s) {r : A → A → Prop}
    (hf : FiniteClasses r) (c : A → R) :
    ∀ a, ∃ x, ClassAverageGraph d r c a x := by
  intro a
  obtain ⟨xs, hxs⟩ := hf a
  exact ⟨d.divide (s.sum c xs) xs.length, xs, hxs, rfl⟩

theorem classAverage_total_functional [DecidableEq A] (d : FiniteDivision s)
    {r : A → A → Prop} (hf : FiniteClasses r) (c : A → R) :
    ∀ a, ∃ x, ClassAverageGraph d r c a x ∧
      ∀ y, ClassAverageGraph d r c a y → x = y := by
  intro a
  obtain ⟨x, hx⟩ := classAverage_total d hf c a
  exact ⟨x, hx, fun y hy => classAverage_unique d hx hy⟩

theorem class_rel_iff {r : A → A → Prop} (hr : Equivalence r)
    {a b : A} (hab : r a b) : ∀ z, r a z ↔ r b z := by
  intro z
  exact ⟨fun haz => hr.trans (hr.symm hab) haz, fun hbz => hr.trans hab hbz⟩

theorem classEnumeration_transfer {r : A → A → Prop} (hr : Equivalence r)
    {a b : A} {xs : List A} (hab : r a b) (hx : ClassEnumeration r a xs) :
    ClassEnumeration r b xs :=
  ⟨hx.1, fun z => (hx.2 z).trans (class_rel_iff hr hab z)⟩

theorem classAverage_transfer (d : FiniteDivision s)
    {r : A → A → Prop} (hr : Equivalence r) {c : A → R}
    {a b : A} {x : R} (hab : r a b) (hx : ClassAverageGraph d r c a x) :
    ClassAverageGraph d r c b x := by
  obtain ⟨xs, hxs, hval⟩ := hx
  exact ⟨xs, classEnumeration_transfer hr hab hxs, hval⟩

theorem classAverage_constant [DecidableEq A] (d : FiniteDivision s)
    {r : A → A → Prop} (hr : Equivalence r) {c v : A → R}
    (hv : ∀ a, ClassAverageGraph d r c a (v a)) {a b : A} (hab : r a b) :
    v a = v b :=
  classAverage_unique d (classAverage_transfer d hr hab (hv a)) (hv b)

/-- Any class-preserving map preserves the averaged weights; bijectivity is unnecessary here. -/
theorem classAverage_map_invariant [DecidableEq A] (d : FiniteDivision s)
    {r : A → A → Prop} (hr : Equivalence r) {c v : A → R}
    (hv : ∀ a, ClassAverageGraph d r c a (v a)) (f : A → A)
    (hf : ∀ a, r a (f a)) : ∀ a, v (f a) = v a := by
  intro a
  exact (classAverage_constant d hr hv (hf a)).symm

theorem classAverage_positive (d : FiniteDivision s) {r : A → A → Prop}
    (hr : Equivalence r) {c : A → R} (hc : ∀ a, s.Positive (c a))
    {a : A} {x : R} (hx : ClassAverageGraph d r c a x) : s.Positive x := by
  obtain ⟨xs, hxs, rfl⟩ := hx
  have ha : a ∈ xs := (hxs.2 a).mpr (hr.refl a)
  have hn : xs.length ≠ 0 := Nat.ne_of_gt (List.length_pos_of_mem ha)
  apply d.divide_positive xs.length hn
  exact s.sum_positive_of_member c xs (fun b _ => (hc b).1) ha (hc a)

/-- The finite sum on one complete class is preserved exactly. -/
theorem classAverage_preserves_class_sum [DecidableEq A] (d : FiniteDivision s)
    {r : A → A → Prop} (hr : Equivalence r) {c v : A → R}
    (hv : ∀ a, ClassAverageGraph d r c a (v a))
    {a : A} {xs : List A} (hxs : ClassEnumeration r a xs) :
    s.sum v xs = s.sum c xs := by
  have ha : a ∈ xs := (hxs.2 a).mpr (hr.refl a)
  have hn : xs.length ≠ 0 := Nat.ne_of_gt (List.length_pos_of_mem ha)
  have hvx : ∀ b, b ∈ xs → v b = d.divide (s.sum c xs) xs.length := by
    intro b hb
    apply classAverage_unique d (hv b)
    exact ⟨xs, classEnumeration_transfer hr ((hxs.2 b).mp hb) hxs, rfl⟩
  rw [s.sum_congr xs hvx, s.sum_const, d.nsmul_divide _ _ hn]

theorem classAverage_of_constant (d : FiniteDivision s) {r : A → A → Prop}
    (hr : Equivalence r) {c : A → R} {a : A} {xs : List A}
    (hxs : ClassEnumeration r a xs) (hc : ∀ b, r a b → c b = c a) :
    ClassAverageGraph d r c a (c a) := by
  have ha : a ∈ xs := (hxs.2 a).mpr (hr.refl a)
  have hn : xs.length ≠ 0 := Nat.ne_of_gt (List.length_pos_of_mem ha)
  refine ⟨xs, hxs, ?_⟩
  have hsum := s.sum_congr xs (fun b hb => hc b ((hxs.2 b).mp hb))
  rw [hsum, s.sum_const, d.divide_nsmul _ _ hn]

/-- Idempotence of the weight graph, before any normalization of a probability. -/
theorem classAverage_idempotent [DecidableEq A] (d : FiniteDivision s)
    {r : A → A → Prop} (hr : Equivalence r) {c v w : A → R}
    (hv : ∀ a, ClassAverageGraph d r c a (v a))
    (hw : ∀ a, ClassAverageGraph d r v a (w a)) : ∀ a, w a = v a := by
  intro a
  obtain ⟨xs, hxs, _⟩ := hv a
  have hfixed : ClassAverageGraph d r v a (v a) :=
    classAverage_of_constant d hr hxs
      (fun b hab => (classAverage_constant d hr hv hab).symm)
  exact classAverage_unique d (hw a) hfixed

/-- Class-constant weights with the prescribed class sums are the canonical averages. -/
theorem classAverage_unique_from_class_mass [DecidableEq A] (d : FiniteDivision s)
    {r : A → A → Prop} (hr : Equivalence r) {c v : A → R}
    {a : A} {xs : List A} (hxs : ClassEnumeration r a xs)
    (hv : ∀ b, r a b → v b = v a) (hm : s.sum v xs = s.sum c xs) :
    ClassAverageGraph d r c a (v a) := by
  have ha : a ∈ xs := (hxs.2 a).mpr (hr.refl a)
  have hn : xs.length ≠ 0 := Nat.ne_of_gt (List.length_pos_of_mem ha)
  have heq := s.sum_congr xs (fun b hb => hv b ((hxs.2 b).mp hb))
  rw [s.sum_const] at heq
  refine ⟨xs, hxs, ?_⟩
  rw [← hm, heq, d.divide_nsmul _ _ hn]

def FiniteMassValues (s : MassScalar R) (c : A → R) (admissible : List A → Prop) (x : R) : Prop :=
  ∃ xs, admissible xs ∧ x = s.sum c xs

/-- The cofinality step used for total and saturated-event mass preservation.

`hsaturate` is a FINITE saturation obligation. It supplies no global choice
function and is not silently discharged by the finite-class graph above.
-/
theorem saturated_envelopes_equal (c v : A → R)
    (admissible saturated : List A → Prop)
    (hsaturate : ∀ xs, admissible xs → ∃ ys,
      admissible ys ∧ saturated ys ∧
      s.le (s.sum c xs) (s.sum c ys) ∧ s.le (s.sum v xs) (s.sum v ys))
    (hmass : ∀ xs, admissible xs → saturated xs → s.sum c xs = s.sum v xs)
    {x y : R} (hx : IsMassSup s (FiniteMassValues s c admissible) x)
    (hy : IsMassSup s (FiniteMassValues s v admissible) y) : x = y := by
  apply massSup_eq_of_mutually_cofinal s hx hy
  · intro a ha
    obtain ⟨xs, hxs, rfl⟩ := ha
    obtain ⟨ys, hys, hsat, hc, hv⟩ := hsaturate xs hxs
    refine ⟨s.sum v ys, ⟨ys, hys, rfl⟩, ?_⟩
    rw [← hmass ys hys hsat]
    exact hc
  · intro b hb
    obtain ⟨xs, hxs, rfl⟩ := hb
    obtain ⟨ys, hys, hsat, hc, hv⟩ := hsaturate xs hxs
    refine ⟨s.sum c ys, ⟨ys, hys, rfl⟩, ?_⟩
    rw [hmass ys hys hsat]
    exact hv

end Classicism.Research.Probability
