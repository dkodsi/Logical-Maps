import Classicism.Results.Research.AtomicProbabilityEnvelope

/-!
# The finite-fibre weight construction

Conditional ordinary Lean over an external atom type and Lean Nat. No theorem
of C, no internal-number identification, no countable-choice principle.
Finite fibres are existential finite-list witnesses, not a chosen enumeration
function. The budget sequence, scalar division and scalar order laws are inputs.
The geometric sequence and the graph-coded internal real construction are NOT
asserted here. A supplied function realizing the unique weight graph is an
explicit parameter of the finite-budget theorem.

Source: research/2026-10-22/proof-refinements/choice-free-faithful-probability.md,
sections 1-3, unpaginated. New argument: OpenAI Codex, 22 October 2026.
-/

namespace Classicism.Research.Probability

universe u v w

variable {R : Type u} {A : Type v} {B : Type w}

namespace MassScalar

variable (s : MassScalar R)

theorem sum_zero (xs : List A) : s.sum (fun _ : A => s.zero) xs = s.zero := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change s.add s.zero (s.sum (fun _ : A => s.zero) xs) = s.zero
    rw [ih, s.zero_add]

theorem sum_add_pointwise (f g : A → R) (xs : List A) :
    s.sum (fun a => s.add (f a) (g a)) xs = s.add (s.sum f xs) (s.sum g xs) := by
  induction xs with
  | nil => exact (s.zero_add s.zero).symm
  | cons a xs ih =>
    change s.add (s.add (f a) (g a)) (s.sum (fun b => s.add (f b) (g b)) xs) =
      s.add (s.add (f a) (s.sum f xs)) (s.add (g a) (s.sum g xs))
    rw [ih, s.add_assoc, s.add_left_comm (g a) (s.sum f xs),
      ← s.add_assoc]

theorem sum_swap (f : A → B → R) (xs : List A) (ys : List B) :
    s.sum (fun a => s.sum (f a) ys) xs =
      s.sum (fun b => s.sum (fun a => f a b) xs) ys := by
  induction xs with
  | nil => exact (s.sum_zero ys).symm
  | cons a xs ih =>
    change s.add (s.sum (f a) ys) (s.sum (fun a => s.sum (f a) ys) xs) =
      s.sum (fun b => s.add (f a b) (s.sum (fun a => f a b) xs)) ys
    rw [ih, s.sum_add_pointwise]

theorem sum_single_label (labels : List Nat) (hn : labels.Nodup)
    (n : Nat) (hm : n ∈ labels) (x : R) :
    s.sum (fun k => if n = k then x else s.zero) labels = x := by
  revert hn hm
  induction labels with
  | nil => intro hn hm; cases hm
  | cons k labels ih =>
    intro hn hm
    have hpair := List.nodup_cons.mp hn
    by_cases hnk : n = k
    · subst k
      have hz : s.sum (fun j => if n = j then x else s.zero) labels = s.zero := by
        have heq : s.sum (fun j => if n = j then x else s.zero) labels =
            s.sum (fun _ => s.zero) labels := s.sum_congr labels (fun j hj =>
          if_neg (show n ≠ j from fun h => hpair.1 (h.symm ▸ hj)))
        exact heq.trans (s.sum_zero labels)
      change s.add (if n = n then x else s.zero)
        (s.sum (fun j => if n = j then x else s.zero) labels) = x
      rw [if_pos rfl, hz, s.add_zero]
    · have htail : n ∈ labels := by
        cases List.mem_cons.mp hm with
        | inl h => exact False.elim (hnk h)
        | inr h => exact h
      change s.add (if n = k then x else s.zero)
        (s.sum (fun j => if n = j then x else s.zero) labels) = x
      rw [if_neg hnk, s.zero_add]
      exact ih hpair.2 htail

theorem sum_partition_by_labels (label : A → Nat) (c : A → R)
    (xs : List A) (labels : List Nat) (hn : labels.Nodup)
    (hc : ∀ a, a ∈ xs → label a ∈ labels) :
    s.sum c xs = s.sum
      (fun n => s.sum (fun a => if label a = n then c a else s.zero) xs) labels := by
  have hswap := s.sum_swap (fun a n => if label a = n then c a else s.zero) xs labels
  have heq : s.sum
      (fun a => s.sum (fun n => if label a = n then c a else s.zero) labels) xs =
      s.sum c xs := by
    apply s.sum_congr xs
    intro a ha
    exact s.sum_single_label labels hn (label a) (hc a ha) (c a)
  exact heq.symm.trans hswap

end MassScalar

/-- Only finitely many labels must be collected at this step. -/
theorem finite_labels_exist (label : A → Nat) (xs : List A) :
    ∃ labels : List Nat, labels.Nodup ∧ ∀ a, a ∈ xs → label a ∈ labels := by
  induction xs with
  | nil => exact ⟨[], List.Pairwise.nil, fun a ha => False.elim (List.not_mem_nil ha)⟩
  | cons a xs ih =>
    obtain ⟨labels, hn, hc⟩ := ih
    by_cases h : label a ∈ labels
    · refine ⟨labels, hn, ?_⟩
      intro b hb
      cases List.mem_cons.mp hb with
      | inl hba => exact hba.symm ▸ h
      | inr hbx => exact hc b hbx
    · refine ⟨label a :: labels, List.nodup_cons.mpr ⟨h, hn⟩, ?_⟩
      intro b hb
      cases List.mem_cons.mp hb with
      | inl hba => exact List.mem_cons.mpr (Or.inl (congrArg label hba))
      | inr hbx => exact List.mem_cons_of_mem _ (hc b hbx)

/-- The usual finite cardinal inequality, with decidable equality supplied as data. -/
theorem enumeration_subset_length [DecidableEq A] {xs ys : List A}
    (hn : xs.Nodup) (hsub : ∀ a, a ∈ xs → a ∈ ys) : xs.length ≤ ys.length :=
  ProbabilityFinite.enumeration_subset_length hn hsub

def FibreEnumeration (label : A → Nat) (n : Nat) (xs : List A) : Prop :=
  xs.Nodup ∧ ∀ a, a ∈ xs ↔ label a = n

def FiniteFibres (label : A → Nat) : Prop := ∀ n, ∃ xs, FibreEnumeration label n xs

variable {s : MassScalar R}

/-- Unique formula for a weight, with no sequence of chosen fibre enumerations. -/
def FibreWeightGraph (d : FiniteDivision s) (label : A → Nat) (budget : Nat → R)
    (a : A) (x : R) : Prop :=
  ∃ xs, FibreEnumeration label (label a) xs ∧
    x = d.divide (budget (label a)) xs.length

theorem fibreWeight_unique [DecidableEq A] (d : FiniteDivision s)
    {label : A → Nat} {budget : Nat → R} {a : A} {x y : R}
    (hx : FibreWeightGraph d label budget a x)
    (hy : FibreWeightGraph d label budget a y) : x = y := by
  obtain ⟨xs, hxs, rfl⟩ := hx
  obtain ⟨ys, hys, rfl⟩ := hy
  have hp := enumeration_perm hxs.1 hys.1
    (fun b => (hxs.2 b).trans (hys.2 b).symm)
  rw [ProbabilityFinite.perm_length hp]

theorem fibreWeight_total_functional [DecidableEq A] (d : FiniteDivision s)
    {label : A → Nat} (hf : FiniteFibres label) (budget : Nat → R) :
    ∀ a, ∃ x, FibreWeightGraph d label budget a x ∧
      ∀ y, FibreWeightGraph d label budget a y → x = y := by
  intro a
  obtain ⟨xs, hxs⟩ := hf (label a)
  have hv : FibreWeightGraph d label budget a
      (d.divide (budget (label a)) xs.length) := ⟨xs, hxs, rfl⟩
  exact ⟨_, hv, fun y hy => fibreWeight_unique d hv hy⟩

theorem fibreWeight_positive (d : FiniteDivision s)
    {label : A → Nat} {budget : Nat → R} (hb : ∀ n, s.Positive (budget n))
    {a : A} {x : R} (hx : FibreWeightGraph d label budget a x) : s.Positive x := by
  obtain ⟨xs, hxs, rfl⟩ := hx
  have ha : a ∈ xs := (hxs.2 a).mpr rfl
  exact d.divide_positive xs.length (Nat.ne_of_gt (List.length_pos_of_mem ha))
    (hb (label a))

/-- A partial fibre consumes at most its whole-fibre budget. -/
theorem partialFibre_budget [DecidableEq A] (d : FiniteDivision s)
    {label : A → Nat} (hf : FiniteFibres label) {budget : Nat → R}
    (hb : ∀ n, s.Nonnegative (budget n)) (c : A → R)
    (hc : ∀ a, FibreWeightGraph d label budget a (c a))
    (n : Nat) (xs : List A) (hn : xs.Nodup)
    (hsame : ∀ a, a ∈ xs → label a = n) : s.le (s.sum c xs) (budget n) := by
  obtain ⟨ys, hys⟩ := hf n
  have hlen : xs.length ≤ ys.length := enumeration_subset_length hn
    (fun a ha => (hys.2 a).mpr (hsame a ha))
  by_cases hzero : ys.length = 0
  · have hxzero : xs.length = 0 := Nat.eq_zero_of_le_zero (hzero ▸ hlen)
    have hxnil := List.eq_nil_of_length_eq_zero hxzero
    rw [hxnil, s.sum_nil]
    exact hb n
  · have heq : ∀ a, a ∈ xs → c a = d.divide (budget n) ys.length := by
      intro a ha
      apply fibreWeight_unique d (hc a)
      unfold FibreWeightGraph
      rw [hsame a ha]
      exact ⟨ys, hys, rfl⟩
    rw [s.sum_congr xs heq, s.sum_const]
    have h := s.nsmul_mono_index (d.divide_nonnegative ys.length (hb n)) hlen
    rw [d.nsmul_divide _ _ hzero] at h
    exact h

def fibreSlice (label : A → Nat) (n : Nat) (xs : List A) : List A :=
  xs.filter (fun a => decide (label a = n))

theorem sum_fibreSlice (s : MassScalar R) (label : A → Nat) (c : A → R)
    (n : Nat) (xs : List A) :
    s.sum c (fibreSlice label n xs) =
      s.sum (fun a => if label a = n then c a else s.zero) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : label a = n
    · simpa [fibreSlice, MassScalar.sum, h] using congrArg (s.add (c a)) ih
    · simpa [fibreSlice, MassScalar.sum, h, s.zero_add] using ih

/-- The entire finite-budget estimate, conditional on a scalar budget sequence.

This supplies the combinatorial half of the construction. It does not construct
internal reals, identify internal naturals with Lean Nat, or select an ambient
function from the unique value graph in C.
-/
theorem finiteFibre_finite_budget [DecidableEq A] (d : FiniteDivision s)
    {label : A → Nat} (hf : FiniteFibres label) {budget : Nat → R}
    (hb : ∀ n, s.Nonnegative (budget n)) (bound : R)
    (hbudget : ∀ ns : List Nat, ns.Nodup → s.le (s.sum budget ns) bound)
    (c : A → R) (hc : ∀ a, FibreWeightGraph d label budget a (c a))
    (xs : List A) (hn : xs.Nodup) : s.le (s.sum c xs) bound := by
  obtain ⟨ns, hns, hcover⟩ := finite_labels_exist label xs
  rw [s.sum_partition_by_labels label c xs ns hns hcover]
  apply s.le_trans (s.sum_mono _ budget ns ?_) (hbudget ns hns)
  intro n _
  rw [← sum_fibreSlice s label c n xs]
  apply partialFibre_budget d hf hb c hc n (fibreSlice label n xs)
  · exact List.Pairwise.filter (fun a => decide (label a = n)) hn
  · intro a ha
    have h := (List.mem_filter.mp ha).2
    exact of_decide_eq_true h

end Classicism.Research.Probability
