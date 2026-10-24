import Classicism.Results.Research.MaxAtomicityJechShelahIndexedGenerators
import Classicism.Results.Research.MaxAtomicityJechShelahRigidityCriterion

/-!
# Exact indexed conditions and canonical cylinder membership

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 749--750,
definitions (1)--(6). The reindexing, uniqueness proofs, and connection to
the finite membership code are original formalization work (misc,
23 October 2026). No first-order definability or hereditary-universe adequacy
is assumed. Compilation belongs to the designated serial checker.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahIndexCoding

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahEnumeration MaxAtomicityJechShelahIndexedGenerators
open MaxAtomicityJechShelahCylinders MaxAtomicityJechShelahRigidityCriterion

noncomputable section

def Child (k j : ℕ) : Prop := offset k ≤ j ∧ j < offset k + growthN k
def Ancestor (i j : ℕ) : Prop := indexedNode i <+: indexedNode j

theorem child_lt {k j : ℕ} (h : Child k j) : k < j :=
  (index_lt_offset k).trans_le h.1

theorem indexedNode_injective : Function.Injective indexedNode := by
  intro i j h
  have := congrArg index h
  simpa only [indexedNode_index] using this

theorem child_iff_append (k j : ℕ) : Child k j ↔
    ∃ d : ℕ, d < growthN k ∧ indexedNode j = indexedNode k ++ [d] := by
  constructor
  · intro h
    let d := j - offset k
    have hd : d < growthN k := by dsimp [d]; have := h.1; have := h.2; omega
    have hm : MasterNode (indexedNode k ++ [d]) :=
      (master_append_iff _ d).2 ⟨indexedNode_master k, by simpa only [indexedNode_index] using hd⟩
    refine ⟨d, hd, index_injective _ _ (indexedNode_master j) hm ?_⟩
    rw [indexedNode_index, index_append, indexedNode_index]
    exact (Nat.add_sub_of_le h.1).symm
  · rintro ⟨d, hd, heq⟩
    have hi : j = offset k + d := by
      have := congrArg index heq
      simpa only [indexedNode_index, index_append] using this
    rw [hi]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hd _⟩

private theorem prefix_append_last {a b : List ℕ} {d : ℕ}
    (h : a <+: b ++ [d]) : a = b ++ [d] ∨ a <+: b := by
  by_cases hlen : a.length ≤ b.length
  · exact Or.inr (List.prefix_of_prefix_length_le h (b.prefix_append [d]) hlen)
  · left
    apply h.eq_of_length
    have hbound := h.length_le
    simp only [List.length_append, List.length_singleton] at hbound ⊢
    omega

/-- The ancestor relation satisfies the exact recursive law used by the
finite code, with recursion on the strictly smaller parent index. -/
theorem ancestor_recursion (i j : ℕ) :
    Ancestor i j ↔ i = j ∨ ∃ k, Child k j ∧ Ancestor i k := by
  constructor
  · intro h
    rcases List.eq_nil_or_concat (indexedNode j) with hj | ⟨s, d, hj⟩
    · left
      apply indexedNode_injective
      have hlen := h.length_le
      have hi : indexedNode i = [] := List.eq_nil_of_length_eq_zero (by
        simp only [hj, List.length_nil] at hlen
        omega)
      exact hi.trans hj.symm
    · have hj' : indexedNode j = s ++ [d] := by simpa only [List.concat_eq_append] using hj
      have hm : MasterNode (s ++ [d]) := hj' ▸ indexedNode_master j
      have hs := (master_append_iff s d).1 hm
      rcases prefix_append_last (hj' ▸ h) with heq | hpre
      · exact Or.inl (indexedNode_injective (heq.trans hj'.symm))
      · refine Or.inr ⟨index s, ?_, ?_⟩
        · apply (child_iff_append _ _).2
          exact ⟨d, hs.2, by simpa only [indexedNode_of_master s hs.1] using hj'⟩
        · simpa only [Ancestor, indexedNode_of_master s hs.1] using hpre
  · rintro (rfl | ⟨k, hk, hik⟩)
    · exact List.prefix_refl _
    · obtain ⟨d, hd, hj⟩ := (child_iff_append k j).1 hk
      exact hj.symm ▸ hik.trans ((indexedNode k).prefix_append [d])

/-- No extra solutions to the finite ancestor recursion are possible. -/
theorem ancestor_unique (R : ℕ → ℕ → Prop)
    (hR : ∀ i j, R i j ↔ i = j ∨ ∃ k, Child k j ∧ R i k) :
    ∀ i j, R i j ↔ Ancestor i j := by
  intro i j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rw [hR i j, ancestor_recursion]
    apply or_congr Iff.rfl
    apply exists_congr
    intro k
    constructor
    · rintro ⟨hk, hr⟩
      exact ⟨hk, (ih k (child_lt hk)).1 hr⟩
    · rintro ⟨hk, hr⟩
      exact ⟨hk, (ih k (child_lt hk)).2 hr⟩

def IndexCondition (I : Set ℕ) : Prop :=
  0 ∈ I ∧ (∀ j ∈ I, ∀ i, Ancestor i j → i ∈ I) ∧
    ∀ i ∈ I, ∀ m : ℕ, ∃ u ∈ I, i ≠ u ∧ Ancestor i u ∧
      ∃ f : Fin (growthP u ^ m) → ℕ, Function.Injective f ∧
        ∀ a, f a ∈ I ∧ Child u (f a)

theorem nodeIndices_indexCondition (T : Condition) : IndexCondition (nodeIndices T) := by
  refine ⟨⟨[], T.root_mem, rfl⟩, ?_, ?_⟩
  · intro j hj i hij
    obtain ⟨s, hs, hindex⟩ := hj
    have heq : indexedNode j = s := by
      rw [← hindex, indexedNode_of_master s (T.submaster hs)]
    exact ⟨indexedNode i, Descriptive.Tree.mem_of_prefix (heq ▸ hij) hs, indexedNode_index i⟩
  · intro i hi m
    obtain ⟨s, hs, hindex⟩ := hi
    obtain ⟨t, ht, hst, f, hf, hchildren⟩ := T.bushy s hs m
    refine ⟨index t, ⟨t, ht, rfl⟩, ?_, ?_, (fun a => index (t ++ [f a])), ?_, ?_⟩
    · intro heq
      have hst' : s = t := index_injective s t (T.submaster hs) (T.submaster ht)
        (hindex.trans heq)
      exact (Nat.ne_of_lt hst.2) (congrArg List.length hst')
    · simpa only [Ancestor, ← hindex, indexedNode_of_master s (T.submaster hs),
        indexedNode_of_master t (T.submaster ht)] using hst.1
    · intro a b hab
      apply hf
      simpa only [index_append, Nat.add_left_cancel_iff] using hab
    · intro a
      refine ⟨⟨t ++ [f a], hchildren a, rfl⟩, ?_⟩
      have hd := (master_append_iff t (f a)).1 (T.submaster (hchildren a)) |>.2
      rw [Child, index_append]
      exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hd _⟩

/-- Reconstruct the actual list tree from an indexed condition. -/
def ofIndexCondition (I : Set ℕ) (hI : IndexCondition I) : Condition where
  tree := ⟨{s | MasterNode s ∧ index s ∈ I}, by
    intro s d h
    have hs := (master_append_iff s d).1 h.1 |>.1
    refine ⟨hs, hI.2.1 (index (s ++ [d])) h.2 (index s) ?_⟩
    simpa only [Ancestor, indexedNode_of_master s hs,
      indexedNode_of_master (s ++ [d]) h.1] using s.prefix_append [d]⟩
  root_mem := ⟨True.intro, hI.1⟩
  submaster := fun _ h => h.1
  bushy := by
    intro s hs m
    obtain ⟨u, hu, hne, hanc, g, hg, hchildren⟩ := hI.2.2 (index s) hs.2 m
    have hpre : s <+: indexedNode u := by
      simpa only [Ancestor, indexedNode_of_master s hs.1] using hanc
    have hlt : s.length < (indexedNode u).length := by
      have hle := hpre.length_le
      apply lt_of_le_of_ne hle
      intro heq
      have hs' : s = indexedNode u := hpre.eq_of_length heq
      apply hne
      simpa only [indexedNode_index] using congrArg index hs'
    refine ⟨indexedNode u, ⟨indexedNode_master u, by simpa only [indexedNode_index] using hu⟩,
      ⟨hpre, hlt⟩, ?_⟩
    have hex : ∃ f : Fin (growthP u ^ m) → ℕ,
        Function.Injective f ∧ ∀ a,
          MasterNode (indexedNode u ++ [f a]) ∧ index (indexedNode u ++ [f a]) ∈ I := by
      refine ⟨fun a => g a - offset u, ?_, ?_⟩
      · intro a b hab
        apply hg
        have ha := (hchildren a).2.1
        have hb := (hchildren b).2.1
        omega
      · intro a
        have hc := (hchildren a).2
        have hlabel : g a - offset u < growthN u := by
          have := hc.1
          have := hc.2
          omega
        refine ⟨(master_append_iff _ _).2 ⟨indexedNode_master u,
          by simpa only [indexedNode_index] using hlabel⟩, ?_⟩
        rw [index_append, indexedNode_index, Nat.add_sub_of_le hc.1]
        exact (hchildren a).1
    simpa only [indexedNode_index] using hex

theorem nodeIndices_ofIndexCondition (I : Set ℕ) (hI : IndexCondition I) :
    nodeIndices (ofIndexCondition I hI) = I := by
  apply Set.ext
  intro j
  constructor
  · rintro ⟨s, hs, hindex⟩
    exact hindex ▸ hs.2
  · intro hj
    exact ⟨indexedNode j, ⟨indexedNode_master j, by simpa only [indexedNode_index] using hj⟩,
      indexedNode_index j⟩

theorem indexCondition_iff (I : Set ℕ) :
    IndexCondition I ↔ ∃ T : Condition, nodeIndices T = I := by
  constructor
  · intro h
    exact ⟨ofIndexCondition I h, nodeIndices_ofIndexCondition I h⟩
  · rintro ⟨T, rfl⟩
    exact nodeIndices_indexCondition T

theorem condition_le_iff_mem (T : Condition) (b : B) :
    condition Condition T ≤ b ↔ T ∈ (b : LowerSet Condition) := by
  exact (regularize_le_iff (LowerSet.Iic T) b).trans LowerSet.Iic_le

/-- This is the literal membership condition used by generatorOpen in the
finite formula, with the actual canonical indexed cylinder as its extension. -/
theorem mem_indexedGenerator_iff (T : Condition) (i : ℕ) :
    T ∈ (indexedGenerator i : LowerSet Condition) ↔
      ∀ j ∈ nodeIndices T, Ancestor j i ∨ Ancestor i j := by
  rw [← condition_le_iff_mem, indexedGenerator, cylinder_of_master (indexedNode_master i),
    condition_le_iff forcing_separative]
  constructor
  · intro h j hj
    obtain ⟨s, hs, hindex⟩ := hj
    have hp := (h hs).2
    simpa only [Ancestor, ← hindex, indexedNode_of_master s (T.submaster hs)] using hp
  · intro h s hs
    refine ⟨T.submaster hs, ?_⟩
    have hp := h (index s) ⟨s, hs, rfl⟩
    simpa only [Ancestor, indexedNode_of_master s (T.submaster hs)] using hp

/-- Standard numerical addition is determined by precisely the zero and
successor equations in the code, once graph functionality is established. -/
theorem add_relation_unique (A : ℕ → ℕ → ℕ → Prop)
    (unique : ∀ x y u v, A x y u → A x y v → u = v)
    (zero : ∀ x, A x 0 x)
    (step : ∀ x y v, A x (y + 1) v ↔ ∃ u, A x y u ∧ v = u + 1) :
    ∀ x y v, A x y v ↔ v = x + y := by
  intro x y
  induction y with
  | zero =>
    intro v
    constructor
    · intro h
      simpa only [Nat.add_zero] using unique x 0 v x h (zero x)
    · intro h
      simp only [Nat.add_zero] at h
      subst v
      exact zero x
  | succ y ih =>
    intro v
    rw [step]
    constructor
    · rintro ⟨u, hu, hv⟩
      rw [ih u] at hu
      simpa only [hu, Nat.add_succ] using hv
    · intro hv
      exact ⟨x + y, (ih _).2 rfl, by simpa only [Nat.add_succ] using hv⟩

theorem mul_relation_unique (M : ℕ → ℕ → ℕ → Prop)
    (unique : ∀ x y u v, M x y u → M x y v → u = v)
    (zero : ∀ x, M x 0 0)
    (step : ∀ x y v, M x (y + 1) v ↔ ∃ u, M x y u ∧ v = u + x) :
    ∀ x y v, M x y v ↔ v = x * y := by
  intro x y
  induction y with
  | zero =>
    intro v
    constructor
    · intro h
      simpa only [Nat.mul_zero] using unique x 0 v 0 h (zero x)
    · intro h
      simp only [Nat.mul_zero] at h
      subst v
      exact zero x
  | succ y ih =>
    intro v
    rw [step]
    constructor
    · rintro ⟨u, hu, hv⟩
      rw [ih u] at hu
      simpa only [hu, Nat.mul_succ] using hv
    · intro hv
      exact ⟨x * y, (ih _).2 rfl, by simpa only [Nat.mul_succ] using hv⟩

theorem pow_relation_unique (E : ℕ → ℕ → ℕ → Prop)
    (unique : ∀ x y u v, E x y u → E x y v → u = v)
    (zero : ∀ x, E x 0 1)
    (step : ∀ x y v, E x (y + 1) v ↔ ∃ u, E x y u ∧ v = u * x) :
    ∀ x y v, E x y v ↔ v = x ^ y := by
  intro x y
  induction y with
  | zero =>
    intro v
    constructor
    · intro h
      simpa only [pow_zero] using unique x 0 v 1 h (zero x)
    · intro h
      simp only [pow_zero] at h
      subst v
      exact zero x
  | succ y ih =>
    intro v
    rw [step]
    constructor
    · rintro ⟨u, hu, hv⟩
      rw [ih u] at hu
      simpa only [hu, pow_succ] using hv
    · intro hv
      exact ⟨x ^ y, (ih _).2 rfl, by simpa only [pow_succ] using hv⟩

theorem growth_unique (p n o : ℕ → ℕ)
    (p0 : p 0 = 1) (n0 : n 0 = 1) (o0 : o 0 = 1)
    (ps : ∀ k, p (k + 1) = p k * n k)
    (ns : ∀ k, n (k + 1) = 2 ^ p (k + 1))
    (os : ∀ k, o (k + 1) = o k + n k) :
    ∀ k, p k = growthP k ∧ n k = growthN k ∧ o k = offset k := by
  intro k
  induction k with
  | zero => exact ⟨p0, n0, o0⟩
  | succ k ih =>
    have hp : p (k + 1) = growthP (k + 1) := by
      rw [ps, ih.1, ih.2.1, growthP_succ]
    refine ⟨hp, ?_, ?_⟩
    · rw [ns, hp, growthN_succ]
    · rw [os, ih.2.2, ih.2.1, offset_succ]

#print axioms ancestor_unique
#print axioms indexCondition_iff
#print axioms mem_indexedGenerator_iff
#print axioms add_relation_unique
#print axioms growth_unique

end

end Classicism.Meta.Research.MaxAtomicityJechShelahIndexCoding
