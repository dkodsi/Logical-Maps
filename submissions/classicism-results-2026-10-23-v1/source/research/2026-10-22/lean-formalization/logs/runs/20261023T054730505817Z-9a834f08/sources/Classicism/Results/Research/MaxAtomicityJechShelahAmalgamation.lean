import Classicism.Results.Research.MaxAtomicityJechShelahEnumeration
import Classicism.Results.Research.MaxAtomicityJechShelahFusion
import Classicism.Results.Research.MaxAtomicityJechShelahCylinders
import Classicism.Results.Research.MaxAtomicitySlalomInvariance
import Mathlib.Data.Fintype.OfMap
import Mathlib.Logic.Function.Basic

/-!
# Finite levels, amalgamation, and finite decisions for the actual forcing

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 750--751,
the level-amalgamation lemma, and pp. 753--754, finite decisions in the local
slalom construction. This module constructs the unions of actual conditions,
proves level preservation and the Boolean join identity, and proves finite
prefix decisions for actual partition-valued names. The finite-level property
is derived from the concrete master-tree index, not supplied as a hypothesis.

The infinite slalom recursion and its pigeonhole/cardinality invariants remain
separate obligations. Source preparation is not a successful Lean check.
Original formal proof transcription: misc, 23 October 2026, unpaginated.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahAmalgamation

set_option backward.isDefEq.respectTransparency false

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahEnumeration MaxAtomicityJechShelahFusion
open MaxAtomicityJechShelahCylinders MaxAtomicitySlalomInvariance

noncomputable section

/-- Any nonempty union of actual conditions is again a condition. -/
def union {I : Type*} [Nonempty I] (F : I → Condition) : Condition where
  tree := ⟨{s | ∃ i, s ∈ (F i).tree}, by
    intro s j hs
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, Descriptive.Tree.mem_of_append hi⟩⟩
  root_mem := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact ⟨i, (F i).root_mem⟩
  submaster := by
    rintro s ⟨i, hi⟩
    exact (F i).submaster hi
  bushy := by
    rintro s ⟨i, hi⟩ m
    obtain ⟨t, ht, hst, f, hf, hchildren⟩ := (F i).bushy s hi m
    exact ⟨t, ⟨i, ht⟩, hst, f, hf, fun j => ⟨i, hchildren j⟩⟩

theorem member_le_union {I : Type*} [Nonempty I] (F : I → Condition) (i : I) :
    F i ≤ union F := fun _ hs => ⟨i, hs⟩

theorem union_le {I : Type*} [Nonempty I] (F : I → Condition) {T : Condition}
    (h : ∀ i, F i ≤ T) : union F ≤ T := by
  rintro s ⟨i, hi⟩
  exact h i hi

abbrev Front (T : Condition) (n : ℕ) := {s : List ℕ // s ∈ T.tree ∧ s.length = n}

instance frontNonempty (T : Condition) (n : ℕ) : Nonempty (Front T n) := by
  obtain ⟨s, hs, hlen⟩ := exists_node_at_level T n
  exact ⟨⟨s, hs, hlen⟩⟩

/-- Finiteness of every level is a theorem about the actual master tree. -/
instance frontFintype (T : Condition) (n : ℕ) : Fintype (Front T n) := by
  let t := zeroExtend [] (n + 1)
  have ht : MasterNode t := zeroExtend_master (s := []) True.intro (n + 1)
  have htlen : t.length = n + 1 := by
    simpa only [List.length_nil, Nat.zero_add] using zeroExtend_length [] (n + 1)
  let f : Front T n → Fin (index t) := fun s =>
    ⟨index s.val, index_lt_of_length_lt s.val t (T.submaster s.prop.1) ht (by
      rw [s.prop.2, htlen]
      exact Nat.lt_succ_self _)⟩
  exact Fintype.ofInjective f (by
    intro s u h
    apply Subtype.ext
    exact index_injective s.val u.val (T.submaster s.prop.1) (T.submaster u.prop.1)
      (congrArg Fin.val h))

variable {T : Condition} {n : ℕ} {F : Front T n → Condition}

theorem stem_mem_union
    (below : ∀ a, F a ≤ T.restrict a.val a.prop.1) (a : Front T n) :
    a.val ∈ (union F).tree :=
  ⟨a, Condition.stem_mem_of_le_restrict (below a)⟩

theorem amalgam_le (below : ∀ a, F a ≤ T.restrict a.val a.prop.1) : union F ≤ T :=
  union_le F (fun a => (below a).trans (T.restrict_le a.val a.prop.1))

/-- The union preserves exactly the chosen level, since every selected subtree
still contains its stem. -/
theorem amalgam_agree_level (below : ∀ a, F a ≤ T.restrict a.val a.prop.1)
    (s : List ℕ) (hlen : s.length = n) :
    s ∈ (union F).tree ↔ s ∈ T.tree := by
  constructor
  · intro hs
    exact amalgam_le below hs
  · intro hs
    exact stem_mem_union below ⟨s, hs, hlen⟩

/-- Above each selected stem, the union coincides with that stem's chosen
subtree. Prefixes are handled by downward closure. -/
theorem amalgam_restrict_le_member
    (below : ∀ a, F a ≤ T.restrict a.val a.prop.1) (a : Front T n) :
    (union F).restrict a.val (stem_mem_union below a) ≤ F a := by
  intro s hs
  rcases hs.2 with hsa | has
  · exact Descriptive.Tree.mem_of_prefix hsa (Condition.stem_mem_of_le_restrict (below a))
  · obtain ⟨b, hsb⟩ := hs.1
    have hablen : a.val.length = b.val.length := a.prop.2.trans b.prop.2.symm
    have habval : a.val = b.val := by
      rcases (below b hsb).2 with hsbpre | hbs
      · exact (has.trans hsbpre).eq_of_length hablen
      · exact (List.prefix_of_prefix_length_le has hbs hablen.le).eq_of_length hablen
    have hab : a = b := Subtype.ext habval
    subst b
    exact hsb

/-- A level amalgamation has exactly the join of its pieces' Boolean values. -/
theorem condition_amalgam_eq_iSup
    (below : ∀ a, F a ≤ T.restrict a.val a.prop.1) :
    condition Condition (union F) = ⨆ a : Front T n, condition Condition (F a) := by
  apply le_antisymm
  · apply le_of_dense_refinements
    intro Q hQ
    have hQU : Q ≤ union F := (condition_le_iff forcing_separative Q (union F)).mp hQ
    obtain ⟨s, hs, hlen⟩ := exists_node_at_level Q n
    let a : Front T n := ⟨s, (amalgam_le below) (hQU hs), hlen⟩
    have hRU : Q.restrict s hs ≤ (union F).restrict a.val (stem_mem_union below a) :=
      fun _ hu => ⟨hQU hu.1, hu.2⟩
    refine ⟨Q.restrict s hs, Q.restrict_le s hs, ?_⟩
    exact (condition_mono (hRU.trans (amalgam_restrict_le_member below a))).trans
      (le_iSup (fun a : Front T n => condition Condition (F a)) a)
  · exact iSup_le (fun a => condition_mono (member_le_union F a))

/-- A bounded Boolean-name coordinate can always be decided by refining an
actual condition. Partition values and completeness supply the refinement. -/
theorem decide_coordinate (x : BoundedName growthN B) (k : ℕ) (Q : Condition) :
    ∃ R : Condition, R ≤ Q ∧ ∃ i : Fin (growthN k), condition Condition R ≤ x.entry k i := by
  classical
  have hsup : (⨆ i : Fin (growthN k), condition Condition Q ⊓ x.entry k i) ≠ ⊥ := by
    rw [← inf_iSup_eq (condition Condition Q)
      (fun i : Fin (growthN k) => x.entry k i), x.row_cover k, inf_top_eq]
    exact condition_ne_bot Q
  have hex : ∃ i : Fin (growthN k), condition Condition Q ⊓ x.entry k i ≠ ⊥ := by
    by_contra hn
    apply hsup
    apply iSup_eq_bot.mpr
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  obtain ⟨R, hR⟩ := condition_dense hi
  exact ⟨R, (condition_le_iff forcing_separative R Q).mp (hR.trans inf_le_left),
    i, hR.trans inf_le_right⟩

/-- Every finite prefix of the name can be decided simultaneously. The vector
is an actual dependent function, total using the positive concrete arities. -/
theorem decide_prefix (x : BoundedName growthN B) (m : ℕ) (Q : Condition) :
    ∃ R : Condition, R ≤ Q ∧ ∃ z : ∀ k, Fin (growthN k),
      ∀ k, k < m → condition Condition R ≤ x.entry k (z k) := by
  classical
  induction m generalizing Q with
  | zero =>
    refine ⟨Q, le_rfl, (fun k => ⟨0, (growth_pos k).2⟩), ?_⟩
    intro k hk
    omega
  | succ m ih =>
    obtain ⟨R, hRQ, z, hz⟩ := ih Q
    obtain ⟨S, hSR, i, hi⟩ := decide_coordinate x m R
    refine ⟨S, hSR.trans hRQ, Function.update z m i, ?_⟩
    intro k hk
    by_cases hkm : k = m
    · subst k
      simpa only [Function.update_self] using hi
    · have hlt : k < m := by omega
      simpa only [Function.update_of_ne hkm] using
        (condition_mono hSR).trans (hz k hlt)

#print axioms union
#print axioms frontFintype
#print axioms amalgam_agree_level
#print axioms amalgam_restrict_le_member
#print axioms condition_amalgam_eq_iSup
#print axioms decide_coordinate
#print axioms decide_prefix

end

end Classicism.Meta.Research.MaxAtomicityJechShelahAmalgamation
