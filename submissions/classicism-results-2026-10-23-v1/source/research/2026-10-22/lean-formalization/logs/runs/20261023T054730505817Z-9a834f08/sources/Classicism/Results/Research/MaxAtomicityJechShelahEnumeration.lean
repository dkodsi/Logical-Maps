import Classicism.Results.Research.MaxAtomicityJechShelahTrees
import Mathlib.Order.Monotone.Basic

/-!
# Enumeration of the concrete Jech--Shelah master tree

The child-index intervals partition the positive natural numbers. This proves
that the actual recursive index is a bijection from the master nodes to ℕ.
Indices also strictly increase between levels, and the earlier module already
proves length(s) ≤ index(s). These are the enumeration facts used by fusion and
the slalom counting argument. No enumerating function is assumed as a parameter.

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 749--750,
definition (3). The explicit child-offset recursion and its verification are
original formalization work (misc, 22 October 2026). The within-level lexicographic
characterization is not needed or claimed by these theorems.
Source preparation is not a successful Lean check.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahEnumeration

open MaxAtomicityJechShelahTrees

theorem offset_strictMono : StrictMono offset := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [offset_succ]
  have := (growth_pos k).2
  omega

/-- Earlier parents have all their children before every child of a later parent. -/
theorem child_index_lt {s t : List ℕ} {i j : ℕ}
    (hi : i < growthN (index s)) (h : index s < index t) :
    index (s ++ [i]) < index (t ++ [j]) := by
  rw [index_append, index_append]
  calc
    offset (index s) + i < offset (index s) + growthN (index s) :=
      Nat.add_lt_add_left hi _
    _ = offset (index s + 1) := (offset_succ _).symm
    _ ≤ offset (index t) := offset_strictMono.monotone (Nat.succ_le_of_lt h)
    _ ≤ offset (index t) + j := Nat.le_add_right _ _

private theorem nil_or_append (s : List ℕ) :
    s = [] ∨ ∃ t i, s = t ++ [i] := by
  simpa only [List.concat_eq_append] using List.eq_nil_or_concat s

/-- Nodes at a lower level have smaller indices. -/
theorem index_lt_of_length_lt (s t : List ℕ) :
    MasterNode s → MasterNode t → s.length < t.length → index s < index t := by
  induction s using List.reverseRecOn generalizing t with
  | nil =>
    intro hs ht hlen
    have hi := length_le_index t
    change 0 < index t
    simp only [List.length_nil] at hlen
    omega
  | append_singleton s i ih =>
    intro hs ht hlen
    rcases nil_or_append t with rfl | ⟨u, j, rfl⟩
    · simp only [List.length_nil] at hlen
      omega
    · have hsi := (master_append_iff s i).mp hs
      have huj := (master_append_iff u j).mp ht
      have hparent : s.length < u.length := by
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      exact child_index_lt hsi.2 (ih u hsi.1 huj.1 hparent)

/-- Uniqueness of the node with a given index. -/
theorem index_injective (s t : List ℕ) :
    MasterNode s → MasterNode t → index s = index t → s = t := by
  induction s using List.reverseRecOn generalizing t with
  | nil =>
    intro hs ht h
    have hi := length_le_index t
    have htlen : t.length = 0 := by
      change 0 = index t at h
      omega
    exact (List.eq_nil_of_length_eq_zero htlen).symm
  | append_singleton s i ih =>
    intro hs ht h
    rcases nil_or_append t with rfl | ⟨u, j, rfl⟩
    · have hi := length_le_index (s ++ [i])
      change index (s ++ [i]) = 0 at h
      simp only [List.length_append, List.length_singleton] at hi
      omega
    · have hsi := (master_append_iff s i).mp hs
      have huj := (master_append_iff u j).mp ht
      have hparents : index s = index u := by
        rcases lt_trichotomy (index s) (index u) with hlt | heq | hgt
        · have hc := child_index_lt (j := j) hsi.2 hlt
          omega
        · exact heq
        · have hc := child_index_lt (j := i) huj.2 hgt
          omega
      have hsu : s = u := ih u hsi.1 huj.1 hparents
      subst u
      have hij : i = j := by
        rw [index_append, index_append] at h
        omega
      subst j
      rfl

/-- Every positive index belongs to a unique parent block; only existence is
needed here because uniqueness follows from strict growth of offset. -/
theorem exists_child_block (n : ℕ) :
    ∃ k : ℕ, offset k ≤ n + 1 ∧ n + 1 < offset (k + 1) := by
  induction n with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨k, hlo, hhi⟩ := ih
    by_cases hnext : n + 1 + 1 < offset (k + 1)
    · exact ⟨k, by omega, hnext⟩
    · have heq : offset (k + 1) = n + 1 + 1 := by omega
      refine ⟨k + 1, heq.le, ?_⟩
      rw [← heq]
      exact offset_strictMono (Nat.lt_succ_self _)

/-- Each natural number is the actual index of a concrete finite master node. -/
theorem index_surjective (n : ℕ) : ∃ s : List ℕ, MasterNode s ∧ index s = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨[], True.intro, rfl⟩
    | succ n =>
      obtain ⟨k, hlo, hhi⟩ := exists_child_block n
      have hkn : k < n + 1 := (index_lt_offset k).trans_le hlo
      obtain ⟨s, hs, hindex⟩ := ih k hkn
      let i := n + 1 - offset k
      have hi : i < growthN k := by
        rw [offset_succ] at hhi
        omega
      refine ⟨s ++ [i], (master_append_iff s i).mpr ⟨hs, ?_⟩, ?_⟩
      · simpa only [hindex] using hi
      · rw [index_append, hindex]
        exact Nat.add_sub_of_le hlo

/-- The actual index, restricted to master nodes, is an equivalence with ℕ. -/
noncomputable def masterIndexEquiv : {s : List ℕ // MasterNode s} ≃ ℕ :=
  Equiv.ofBijective (fun s => index s.val) ⟨by
    intro s t h
    exact Subtype.ext (index_injective s.val t.val s.prop t.prop h), by
    intro n
    obtain ⟨s, hs, h⟩ := index_surjective n
    exact ⟨⟨s, hs⟩, h⟩⟩

#print axioms index_lt_of_length_lt
#print axioms index_injective
#print axioms index_surjective
#print axioms masterIndexEquiv

end Classicism.Meta.Research.MaxAtomicityJechShelahEnumeration
