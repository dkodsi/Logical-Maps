import Classicism.Results.Research.MaxAtomicityRegularCompletion
import Mathlib.SetTheory.Descriptive.Tree
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The elementary Jech--Shelah tree forcing and its atomless completion

The concrete growth recurrence is P₀=N₀=1, Pₖ₊₁=PₖNₖ, Nₖ₊₁=2^Pₖ₊₁.
The index of the i-th child of node k is 1 + sum_{j<k} Nⱼ + i. Starting
with the empty sequence at index zero, this implements the paper's breadth-first,
lexicographic master tree; the initial branching values are 1, 2, 4, 256.
The admissible finite sequences and the forcing conditions are actual definitions.
Condition (4) of the source is expressed by an injective list of sufficiently
many immediate successors, so no cardinality convention is hidden.

This module proves that the full master tree is a condition, stem restrictions
remain conditions, all conditions have incompatible refinements, the forcing
order is separative, and the constructed regular-lower-set completion is atomless.
No splitting hypothesis is assumed about the concrete forcing.

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 749--750,
definitions (2)--(4) and restriction (8). The explicit index recursion and the
Lean proofs are original transcription/proof work (misc, 22 October 2026).
The full enumeration theorem for this index, fusion, rigidity, cylinder
generation, coding in C, and the final inconsistency are not proved here.

Source preparation is not a successful Lean check. The designated serial checker
owns compilation and the final axiom reports.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahTrees

open scoped BigOperators
open MaxAtomicityRegularCompletion

/-- The source's pair of fast-growing integer sequences, including its special
initial value N₀=1. -/
def growth : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 => let p := (growth k).1 * (growth k).2; (p, 2 ^ p)

def growthP (k : ℕ) : ℕ := (growth k).1
def growthN (k : ℕ) : ℕ := (growth k).2

@[simp] theorem growthP_zero : growthP 0 = 1 := rfl
@[simp] theorem growthN_zero : growthN 0 = 1 := rfl
@[simp] theorem growthP_succ (k : ℕ) : growthP (k + 1) = growthP k * growthN k := rfl
@[simp] theorem growthN_succ (k : ℕ) : growthN (k + 1) = 2 ^ growthP (k + 1) := rfl

theorem growth_pos (k : ℕ) : 0 < growthP k ∧ 0 < growthN k := by
  induction k with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    constructor
    · exact Nat.mul_pos ih.1 ih.2
    · exact Nat.pow_pos (by decide : 0 < (2 : ℕ))

theorem two_le_growthN_succ (k : ℕ) : 2 ≤ growthN (k + 1) := by
  rw [growthN_succ]
  have hp : 1 ≤ growthP (k + 1) := (growth_pos (k + 1)).1
  simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hp

theorem index_le_growthP (k : ℕ) : k ≤ growthP k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases k with
    | zero => exact le_rfl
    | succ k =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * growthP (k + 1) := Nat.mul_le_mul_left 2 ih
        _ = growthP (k + 1) * 2 := Nat.mul_comm _ _
        _ ≤ growthP (k + 1) * growthN (k + 1) :=
          Nat.mul_le_mul_left _ (two_le_growthN_succ k)
        _ = growthP (k + 1 + 1) := rfl

/-- An elementary eventual-power bound, with an explicit index. -/
theorem power_growth_bound (m k : ℕ) (hk : m + 2 ≤ k) :
    growthP k ^ m ≤ growthN k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
  have hj : m ≤ growthP (j + 1) :=
    (show m ≤ j + 1 by omega).trans (index_le_growthP (j + 1))
  have hN : growthN (j + 1) = 2 ^ growthP (j + 1) := growthN_succ j
  have hP : growthP (j + 1) ≤ 2 ^ growthP (j + 1) :=
    (Nat.lt_two_pow_self (n := growthP (j + 1))).le
  have hexp : (growthP (j + 1) + growthP (j + 1)) * m ≤
      growthP (j + 1) * 2 ^ growthP (j + 1) := by
    calc
      (growthP (j + 1) + growthP (j + 1)) * m =
          growthP (j + 1) * (2 * m) := by
            simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul]
      _ ≤ growthP (j + 1) * (2 * growthP (j + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hj)
      _ ≤ growthP (j + 1) * 2 ^ growthP (j + 1) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_pow (by decide : 2 ≠ 1) _)
  have hstep : growthP (j + 1 + 1) ^ m ≤ growthN (j + 1 + 1) := by
    change (growthP (j + 1) * growthN (j + 1)) ^ m ≤
      2 ^ (growthP (j + 1) * growthN (j + 1))
    simp only [hN]
    calc
      (growthP (j + 1) * 2 ^ growthP (j + 1)) ^ m ≤
          (2 ^ growthP (j + 1) * 2 ^ growthP (j + 1)) ^ m :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hP) _
      _ = 2 ^ ((growthP (j + 1) + growthP (j + 1)) * m) := by
        rw [← pow_add, ← pow_mul]
      _ ≤ 2 ^ (growthP (j + 1) * 2 ^ growthP (j + 1)) :=
        Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

/-- The first child index of the node with index k. -/
def offset (k : ℕ) : ℕ := 1 + ∑ j ∈ Finset.range k, growthN j

theorem offset_succ (k : ℕ) : offset (k + 1) = offset k + growthN k := by
  simp only [offset, Finset.sum_range_succ]
  omega

theorem index_lt_offset (k : ℕ) : k < offset k := by
  induction k with
  | zero => simp [offset]
  | succ k ih =>
    rw [offset_succ]
    have hn := (growth_pos k).2
    omega

/-- Follow a finite sequence from an indexed node. -/
def walk (k : ℕ) : List ℕ → ℕ
  | [] => k
  | i :: s => walk (offset k + i) s

def index (s : List ℕ) : ℕ := walk 0 s

theorem walk_append (k : ℕ) (s t : List ℕ) :
    walk k (s ++ t) = walk (walk k s) t := by
  induction s generalizing k with
  | nil => rfl
  | cons i s ih => exact ih (offset k + i)

theorem index_append (s : List ℕ) (i : ℕ) :
    index (s ++ [i]) = offset (index s) + i := by
  exact walk_append 0 s [i]

theorem length_add_le_walk (k : ℕ) (s : List ℕ) : k + s.length ≤ walk k s := by
  induction s generalizing k with
  | nil => exact le_rfl
  | cons i s ih =>
    have h := ih (offset k + i)
    have ho := index_lt_offset k
    change k + (s.length + 1) ≤ walk (offset k + i) s
    omega

theorem length_le_index (s : List ℕ) : s.length ≤ index s := by
  simpa only [index, Nat.zero_add] using length_add_le_walk 0 s

/-- Every edge label is less than the branching number at its parent. -/
def Admissible (k : ℕ) : List ℕ → Prop
  | [] => True
  | i :: s => i < growthN k ∧ Admissible (offset k + i) s

theorem admissible_append (k : ℕ) (s t : List ℕ) :
    Admissible k (s ++ t) ↔ Admissible k s ∧ Admissible (walk k s) t := by
  induction s generalizing k with
  | nil => simp only [List.nil_append, Admissible, walk, true_and]
  | cons i s ih =>
    simp only [List.cons_append, Admissible, walk, ih, and_assoc]

def MasterNode (s : List ℕ) : Prop := Admissible 0 s

theorem master_append_iff (s : List ℕ) (i : ℕ) :
    MasterNode (s ++ [i]) ↔ MasterNode s ∧ i < growthN (index s) := by
  simp only [MasterNode, admissible_append, Admissible, and_true, index]

theorem master_of_prefix {s t : List ℕ} (hst : s <+: t) (ht : MasterNode t) :
    MasterNode s := by
  obtain ⟨u, rfl⟩ := hst
  exact (admissible_append 0 s u).mp ht |>.1

/-- The concrete master tree. -/
def masterTree : Descriptive.tree ℕ :=
  ⟨{s | MasterNode s}, fun s i h => (master_append_iff s i).mp h |>.1⟩

def zeroExtend (s : List ℕ) : ℕ → List ℕ
  | 0 => s
  | n + 1 => zeroExtend s n ++ [0]

theorem zeroExtend_prefix (s : List ℕ) (n : ℕ) : s <+: zeroExtend s n := by
  induction n with
  | zero => exact List.prefix_refl _
  | succ n ih => exact ih.trans ((zeroExtend s n).prefix_append [0])

theorem zeroExtend_length (s : List ℕ) (n : ℕ) : (zeroExtend s n).length = s.length + n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeroExtend, List.length_append, List.length_singleton, ih]; omega

theorem zeroExtend_master {s : List ℕ} (hs : MasterNode s) (n : ℕ) :
    MasterNode (zeroExtend s n) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    exact (master_append_iff _ 0).mpr ⟨ih, (growth_pos _).2⟩

def StrictExtension (s t : List ℕ) : Prop := s <+: t ∧ s.length < t.length

/-- Exactly the paper's condition (4), including the nonempty tree convention. -/
structure Condition where
  tree : Descriptive.tree ℕ
  root_mem : [] ∈ tree
  submaster : tree ≤ masterTree
  bushy : ∀ s ∈ tree, ∀ m : ℕ, ∃ t : List ℕ, t ∈ tree ∧ StrictExtension s t ∧
    ∃ f : Fin (growthP (index t) ^ m) → ℕ,
      Function.Injective f ∧ ∀ i, t ++ [f i] ∈ tree

instance : PartialOrder Condition :=
  PartialOrder.lift Condition.tree (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

/-- The master tree meets the actual growth requirement, by an explicit bound. -/
def masterCondition : Condition where
  tree := masterTree
  root_mem := True.intro
  submaster := le_rfl
  bushy := by
    intro s hs m
    let t := zeroExtend s (m + 3)
    have ht : MasterNode t := zeroExtend_master hs (m + 3)
    have hlen : t.length = s.length + (m + 3) := zeroExtend_length s (m + 3)
    have hind : m + 2 ≤ index t := by
      have := length_le_index t
      omega
    have hbound := power_growth_bound m (index t) hind
    refine ⟨t, ht, ⟨zeroExtend_prefix s (m + 3), by omega⟩,
      (fun i => i.val), ?_, ?_⟩
    · exact Fin.val_injective
    · intro i
      exact (master_append_iff t i.val).mpr ⟨ht, i.isLt.trans_le hbound⟩

instance : Inhabited Condition := ⟨masterCondition⟩

namespace Condition

theorem exists_long_node (T : Condition) (n : ℕ) :
    ∃ s : List ℕ, s ∈ T.tree ∧ n ≤ s.length := by
  induction n with
  | zero => exact ⟨[], T.root_mem, le_rfl⟩
  | succ n ih =>
    obtain ⟨s, hs, hn⟩ := ih
    obtain ⟨t, ht, hst, f, hf, hchildren⟩ := T.bushy s hs 0
    exact ⟨t, ht, by have := hst.2; omega⟩

/-- Restrict a tree to nodes comparable with a fixed node a. -/
def restrictedTree (T : Condition) (a : List ℕ) : Descriptive.tree ℕ := by
  refine ⟨{s | s ∈ T.tree ∧ (s <+: a ∨ a <+: s)}, ?_⟩
  intro s i hs
  refine ⟨Descriptive.Tree.mem_of_append hs.1, ?_⟩
  rcases hs.2 with h | h
  · exact Or.inl ((s.prefix_append [i]).trans h)
  · exact List.prefix_or_prefix_of_prefix (s.prefix_append [i]) h

/-- Stem restriction preserves the concrete growth condition. -/
def restrict (T : Condition) (a : List ℕ) (ha : a ∈ T.tree) : Condition where
  tree := T.restrictedTree a
  root_mem := ⟨T.root_mem, Or.inl List.nil_prefix⟩
  submaster := fun _ hs => T.submaster hs.1
  bushy := by
    intro s hs m
    have hu : ∃ u : List ℕ, u ∈ T.tree ∧ s <+: u ∧ a <+: u := by
      rcases hs.2 with h | h
      · exact ⟨a, ha, h, List.prefix_refl _⟩
      · exact ⟨s, hs.1, List.prefix_refl _, h⟩
    obtain ⟨u, hu, hsu, hau⟩ := hu
    obtain ⟨t, ht, hut, f, hf, hchildren⟩ := T.bushy u hu m
    have hat : a <+: t := hau.trans hut.1
    refine ⟨t, ⟨ht, Or.inr hat⟩,
      ⟨hsu.trans hut.1, lt_of_le_of_lt hsu.length_le hut.2⟩, f, hf, ?_⟩
    intro i
    exact ⟨hchildren i, Or.inr (hat.trans (t.prefix_append [f i]))⟩

theorem restrict_le (T : Condition) (a : List ℕ) (ha : a ∈ T.tree) : T.restrict a ha ≤ T :=
  fun _ hs => hs.1

/-- Every further condition under a stem restriction still contains that stem. -/
theorem stem_mem_of_le_restrict {S T : Condition} {a : List ℕ} {ha : a ∈ T.tree}
    (h : S ≤ T.restrict a ha) : a ∈ S.tree := by
  obtain ⟨s, hs, hlen⟩ := S.exists_long_node a.length
  have hcomp := (h hs).2
  have has : a <+: s := by
    rcases hcomp with hsa | has
    · have heq : s = a := hsa.eq_of_length_le hlen
      simpa only [heq] using (List.prefix_refl a)
    · exact has
  exact Descriptive.Tree.mem_of_prefix has hs

theorem restrictions_incompatible (T : Condition) {a b : List ℕ}
    (ha : a ∈ T.tree) (hb : b ∈ T.tree) (hlen : a.length = b.length) (hne : a ≠ b) :
    ¬ ∃ S : Condition, S ≤ T.restrict a ha ∧ S ≤ T.restrict b hb := by
  rintro ⟨S, hSa, hSb⟩
  have has : a ∈ S.tree := stem_mem_of_le_restrict hSa
  rcases (hSb has).2 with hab | hba
  · exact hne (hab.eq_of_length hlen)
  · exact hne (hba.eq_of_length hlen.symm).symm

end Condition

/-- Splitting is proved for the actual tree forcing, not supplied as a premise. -/
theorem forcing_splitting : Splitting Condition := by
  intro T
  obtain ⟨v, hv, hlong⟩ := T.exists_long_node 2
  obtain ⟨t, ht, hvt, f, hf, hchildren⟩ := T.bushy v hv 1
  have htwo : 2 ≤ growthP (index t) ^ 1 := by
    rw [pow_one]
    have hlen := length_le_index t
    have hgrowth := index_le_growthP (index t)
    have hstrict := hvt.2
    omega
  let i : Fin (growthP (index t) ^ 1) := ⟨0, by omega⟩
  let j : Fin (growthP (index t) ^ 1) := ⟨1, by omega⟩
  have hne : t ++ [f i] ≠ t ++ [f j] := by
    intro h
    have hij : f i = f j := by simpa using h
    have hval := congrArg Fin.val (hf hij)
    change (0 : ℕ) = 1 at hval
    exact Nat.zero_ne_one hval
  refine ⟨T.restrict (t ++ [f i]) (hchildren i),
    T.restrict (t ++ [f j]) (hchildren j),
    T.restrict_le _ _, T.restrict_le _ _, ?_⟩
  exact T.restrictions_incompatible (hchildren i) (hchildren j) (by simp) hne

/-- Inclusion is the separative forcing order because a node outside a tree
can be made a permanent stem. -/
theorem forcing_separative : Separative Condition := by
  classical
  intro S T hnot
  have hex : ∃ a : List ℕ, a ∈ S.tree ∧ a ∉ T.tree := by
    by_contra hn
    apply hnot
    intro a ha
    by_contra hna
    exact hn ⟨a, ha, hna⟩
  obtain ⟨a, ha, hat⟩ := hex
  refine ⟨S.restrict a ha, S.restrict_le a ha, ?_⟩
  rintro ⟨R, hRS, hRT⟩
  exact hat (hRT (Condition.stem_mem_of_le_restrict hRS))

/-- The actual Jech--Shelah forcing has a nontrivial complete Boolean completion. -/
instance completionNontrivial : Nontrivial (Completion Condition) :=
  ⟨⟨condition Condition masterCondition, ⊥, condition_ne_bot masterCondition⟩⟩

/-- Atomlessness of the actual completion, with no remaining growth/splitting
hypothesis. Rigidity is a separate, unfinished fusion theorem. -/
theorem forcing_completion_atomless {b : Completion Condition} (hb : b ≠ ⊥) :
    ∃ c : Completion Condition, c ≠ ⊥ ∧ c ≤ b ∧ c ≠ b :=
  completion_atomless forcing_splitting hb

#print axioms power_growth_bound
#print axioms masterCondition
#print axioms Condition.restrict
#print axioms forcing_splitting
#print axioms forcing_separative
#print axioms forcing_completion_atomless

end Classicism.Meta.Research.MaxAtomicityJechShelahTrees
