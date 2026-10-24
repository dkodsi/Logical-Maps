import Classicism.Results.Research.MaxAtomicityJechShelahTrees
import Mathlib.Order.Monotone.Basic

/-!
# Fusion for the concrete Jech--Shelah forcing

The input is a decreasing sequence of the actual tree conditions, with agreement
on the indicated finite levels and the source's retained large-splitting witnesses.
Its intersection is constructed and proved to satisfy the original growth
condition. No conditionhood or atomlessness of the intersection is assumed.

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), p. 751, fusion lemma
(9), together with the equivalent growth criterion (5) on p. 750. The proof below
works directly with condition (4), avoiding an assumed enumeration theorem:
at stage n it asks for the witness for every master node whose actual index is n.
The breadth-first enumeration will make that at most one node. Only monotonicity
of the retained levels is needed in this preservation proof; the source uses
strictly increasing levels. Source preparation is not a successful Lean check.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahFusion

open MaxAtomicityJechShelahTrees

/-- Growth gives arbitrarily long extensions above each particular node. -/
theorem extension_long (T : Condition) {s : List ℕ} (hs : s ∈ T.tree) (n : ℕ) :
    ∃ t : List ℕ, t ∈ T.tree ∧ s <+: t ∧ s.length + n ≤ t.length := by
  induction n with
  | zero => exact ⟨s, hs, List.prefix_refl _, le_rfl⟩
  | succ n ih =>
    obtain ⟨t, ht, hst, hlen⟩ := ih
    obtain ⟨u, hu, htu, f, hf, hchildren⟩ := T.bushy t ht 0
    exact ⟨u, hu, hst.trans htu.1, by have := htu.2; omega⟩

/-- In particular, every prescribed higher level has an extension of the node. -/
theorem extension_at_level (T : Condition) {s : List ℕ} (hs : s ∈ T.tree)
    (n : ℕ) (hns : s.length ≤ n) :
    ∃ t : List ℕ, t ∈ T.tree ∧ s <+: t ∧ t.length = n := by
  obtain ⟨u, hu, hsu, hlong⟩ := extension_long T hs n
  have hnu : n ≤ u.length := by omega
  have hlen : (u.take n).length = n := by
    simp only [List.length_take, Nat.min_eq_left hnu]
  refine ⟨u.take n, Descriptive.Tree.mem_of_prefix (List.take_prefix n u) hu, ?_, hlen⟩
  exact List.prefix_of_prefix_length_le hsu (List.take_prefix n u)
    (by simpa only [hlen] using hns)

/-- Exactly the data preserved during the fusion construction. -/
structure FusionSequence where
  tree : ℕ → Condition
  level : ℕ → ℕ
  decreasing : ∀ n, tree (n + 1) ≤ tree n
  level_mono : Monotone level
  agree_level : ∀ n (s : List ℕ), s.length = level n →
    (s ∈ (tree (n + 1)).tree ↔ s ∈ (tree n).tree)
  split : ∀ n (s : List ℕ), index s = n → s ∈ (tree n).tree →
    ∃ t : List ℕ, t ∈ (tree (n + 1)).tree ∧ StrictExtension s t ∧
      t.length < level (n + 1) ∧
      ∃ f : Fin (growthP (index t) ^ n) → ℕ,
        Function.Injective f ∧ ∀ i, t ++ [f i] ∈ (tree (n + 1)).tree

namespace FusionSequence

theorem tree_antitone (F : FusionSequence) : Antitone F.tree :=
  antitone_nat_of_succ_le F.decreasing

/-- Equality at the designated level implies equality at every lower level,
because the actual conditions have arbitrarily long extensions. -/
theorem agree_below (F : FusionSequence) (n : ℕ) (s : List ℕ)
    (hlen : s.length ≤ F.level n) :
    (s ∈ (F.tree (n + 1)).tree ↔ s ∈ (F.tree n).tree) := by
  constructor
  · exact F.decreasing n
  · intro hs
    obtain ⟨t, ht, hst, htlen⟩ := extension_at_level (F.tree n) hs (F.level n) hlen
    exact Descriptive.Tree.mem_of_prefix hst ((F.agree_level n t htlen).mpr ht)

/-- A node below a retained level survives every later tree. -/
theorem survives_later (F : FusionSequence) {k n : ℕ} (hkn : k ≤ n)
    {s : List ℕ} (hlen : s.length ≤ F.level k) (hs : s ∈ (F.tree k).tree) :
    s ∈ (F.tree n).tree := by
  induction n, hkn using Nat.le_induction with
  | base => exact hs
  | succ n hkn ih =>
    exact (F.agree_below n s (hlen.trans (F.level_mono hkn))).mpr ih

/-- Membership below a retained level also implies membership in all earlier
trees, hence in the full intersection. -/
theorem mem_all_of_retained (F : FusionSequence) {k : ℕ} {s : List ℕ}
    (hlen : s.length ≤ F.level k) (hs : s ∈ (F.tree k).tree) :
    ∀ n, s ∈ (F.tree n).tree := by
  intro n
  rcases le_total k n with hkn | hnk
  · exact F.survives_later hkn hlen hs
  · exact F.tree_antitone hnk hs

def intersection (F : FusionSequence) : Descriptive.tree ℕ :=
  ⟨{s | ∀ n, s ∈ (F.tree n).tree}, fun _ _ hs n =>
    Descriptive.Tree.mem_of_append (hs n)⟩

/-- The retained witness above a node belongs to the intersection itself. -/
theorem intersection_strict_extension (F : FusionSequence) {s : List ℕ}
    (hs : s ∈ F.intersection) :
    ∃ t : List ℕ, t ∈ F.intersection ∧ StrictExtension s t := by
  obtain ⟨t, ht, hst, hlen, f, hf, hchildren⟩ :=
    F.split (index s) s rfl (hs (index s))
  exact ⟨t, F.mem_all_of_retained hlen.le ht, hst⟩

/-- Iterating retained witnesses reaches arbitrarily high indices in the
intersection; `length_le_index` is enough, without surjectivity of index. -/
theorem intersection_extension_long (F : FusionSequence) {s : List ℕ}
    (hs : s ∈ F.intersection) (n : ℕ) :
    ∃ t : List ℕ, t ∈ F.intersection ∧ s <+: t ∧ s.length + n ≤ t.length := by
  induction n with
  | zero => exact ⟨s, hs, List.prefix_refl _, le_rfl⟩
  | succ n ih =>
    obtain ⟨t, ht, hst, hlen⟩ := ih
    obtain ⟨u, hu, htu⟩ := F.intersection_strict_extension ht
    exact ⟨u, hu, hst.trans htu.1, by have := htu.2; omega⟩

/-- The intersection is an actual forcing condition. In particular, the large
splitting property is proved rather than included as a field of the input. -/
def fuse (F : FusionSequence) : Condition where
  tree := F.intersection
  root_mem := fun n => (F.tree n).root_mem
  submaster := fun _ hs => (F.tree 0).submaster (hs 0)
  bushy := by
    intro s hs m
    obtain ⟨u, hu, hsu, hlong⟩ := F.intersection_extension_long hs m
    have hm : m ≤ index u := by
      have := length_le_index u
      omega
    obtain ⟨t, ht, hut, hlen, f, hf, hchildren⟩ :=
      F.split (index u) u rfl (hu (index u))
    have hpow : growthP (index t) ^ m ≤ growthP (index t) ^ index u :=
      Nat.pow_le_pow_right (growth_pos (index t)).1 hm
    let inc : Fin (growthP (index t) ^ m) → Fin (growthP (index t) ^ index u) :=
      fun i => ⟨i.val, i.isLt.trans_le hpow⟩
    refine ⟨t, F.mem_all_of_retained hlen.le ht,
      ⟨hsu.trans hut.1, lt_of_le_of_lt hsu.length_le hut.2⟩,
      (fun i => f (inc i)), ?_, ?_⟩
    · intro i j hij
      exact Fin.ext (congrArg Fin.val (hf hij))
    · intro i
      apply F.mem_all_of_retained ?_ (hchildren (inc i))
      simp only [List.length_append, List.length_singleton]
      omega

theorem fuse_le (F : FusionSequence) (n : ℕ) : F.fuse ≤ F.tree n :=
  fun _ hs => hs n

end FusionSequence

#print axioms extension_at_level
#print axioms FusionSequence.agree_below
#print axioms FusionSequence.survives_later
#print axioms FusionSequence.fuse
#print axioms FusionSequence.fuse_le

end Classicism.Meta.Research.MaxAtomicityJechShelahFusion
