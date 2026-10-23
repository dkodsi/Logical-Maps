import Classicism.Results.Research.MaxAtomicityJechShelahFiniteRefinement
import Classicism.Results.Research.MaxAtomicitySlalomThinning
import Mathlib.Data.Fintype.Sum

/-!
# Actual finite stages for the local Jech--Shelah slalom

Each stage splits above one old front node, keeps one extension of every other
front node, and thins the special block to one full-prefix color. Splitting even
when the currently scheduled master node is absent eliminates an unnecessary
case of the published recursion. All conditions and decisions are constructed;
the stage invariant is not an assumed slalom or an assumed fusion sequence.

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 753--754,
construction (14) and its finite bounds. The uniform splitting variant and
formal transcription are misc, 23 October 2026. This source awaits the designated
serial checker and does not claim a successful Lean check.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahLocalStage

set_option backward.isDefEq.respectTransparency false

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahEnumeration MaxAtomicityJechShelahFusion
open MaxAtomicityJechShelahCylinders MaxAtomicitySlalomInvariance
open MaxAtomicityJechShelahAmalgamation MaxAtomicityJechShelahFiniteRefinement
open MaxAtomicitySlalomThinning

noncomputable section

theorem growthP_mono : Monotone growthP := by
  apply monotone_nat_of_le_succ
  intro k
  rw [growthP_succ]
  exact Nat.le_mul_of_pos_right _ (growth_pos k).2

theorem growthP_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ growthP k :=
  hk.trans (index_le_growthP k)

theorem growthN_two (k : ℕ) (hk : 1 ≤ k) : 2 ≤ growthN k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using two_le_growthN_succ j

theorem sum_le_product {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) : p + q ≤ p * q := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem future_front_bound {L K m k n : ℕ}
    (hL : L < growthP K) (hKm : K ≤ m) (hm : n + 2 ≤ m) (hmk : m < k) :
    L + growthP m ^ n < growthP k := by
  have hLP : L < growthP m := hL.trans_le (growthP_mono hKm)
  have hpow := power_growth_bound n m hm
  calc
    L + growthP m ^ n ≤ L + growthN m := Nat.add_le_add_left hpow _
    _ < growthP m + growthN m := Nat.add_lt_add_right hLP _
    _ ≤ growthP m * growthN m := sum_le_product
      (growthP_two m (by omega)) (growthN_two m (by omega))
    _ = growthP (m + 1) := (growthP_succ m).symm
    _ ≤ growthP k := growthP_mono hmk

theorem restrict_below_prefix (T : Condition) {s t : List ℕ}
    (hs : s ∈ T.tree) (ht : t ∈ T.tree) (hst : s <+: t) :
    T.restrict t ht ≤ T.restrict s hs := by
  intro u hu
  refine ⟨hu.1, ?_⟩
  rcases hu.2 with hut | htu
  · exact List.prefix_or_prefix_of_prefix hut hst
  · exact Or.inr (hst.trans htu)

/-- The finite possible values of a coordinate at a named front. -/
def valueSet {I : Type*} [Fintype I] {k : ℕ} (z : I → Fin (growthN k)) :
    Finset (Fin (growthN k)) := Finset.univ.image z

theorem valueSet_card_le {I : Type*} [Fintype I] {k : ℕ}
    (z : I → Fin (growthN k)) : (valueSet z).card ≤ Fintype.card I :=
  Finset.card_image_le

/-- The source's two cardinal bounds, together with their actual decisions. -/
structure Stage (x : BoundedName growthN B) (A : Set ℕ) where
  tree : Condition
  level : ℕ
  cutoff : ℕ
  cutoff_two : 2 ≤ cutoff
  value : ∀ a : Front tree level, ∀ k, Fin (growthN k)
  decides : ∀ a k, k < cutoff →
    condition Condition (tree.restrict a.val a.prop.1) ≤ x.entry k (value a k)
  past : ∀ k ∈ A, k < cutoff → (valueSet (fun a => value a k)).card ≤ growthP k
  future : ∀ k ∈ A, cutoff ≤ k → Fintype.card (Front tree level) < growthP k
  avoids : ∀ s ∈ tree.tree, level ≤ s.length → index s ∉ A

/-- The output properties needed by fusion, in addition to the next finite
stage invariant. The split is strictly above the chosen old front node. -/
structure Advances {x : BoundedName growthN B} {A : Set ℕ}
    (S U : Stage x A) (v : Front S.tree S.level) (n : ℕ) : Prop where
  below : U.tree ≤ S.tree
  level_lt : S.level < U.level
  cutoff_lt : S.cutoff < U.cutoff
  agrees : ∀ s, s.length = S.level → (s ∈ U.tree.tree ↔ s ∈ S.tree.tree)
  split : ∃ t, t ∈ U.tree.tree ∧ StrictExtension v.val t ∧
    t.length < U.level ∧ ∃ f : Fin (growthP (index t) ^ n) → ℕ,
      Function.Injective f ∧ ∀ i, t ++ [f i] ∈ U.tree.tree

/-- A complete actual finite stage. The only set-theoretic hypothesis on A is
its unboundedness; avoidance is carried by the input stage itself. -/
theorem advance {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (S : Stage x A)
    (v : Front S.tree S.level) (n : ℕ) :
    ∃ U : Stage x A, Advances S U v n := by
  classical
  obtain ⟨K, hKA, hjK⟩ := unbounded S.cutoff
  obtain ⟨u, hu, hvu, hlong⟩ := extension_long S.tree v.prop.1 (K + n + 3)
  obtain ⟨t, ht, hut, f, hf, hchildren⟩ := S.tree.bushy u hu (n + 1)
  let m := index t
  let ell := t.length + 1
  have hvt : StrictExtension v.val t :=
    ⟨hvu.trans hut.1, lt_of_le_of_lt hvu.length_le hut.2⟩
  have hlevel : S.level < t.length := by simpa only [v.prop.2] using hvt.2
  have hutlen : u.length < t.length := hut.2
  have hKm : K < m := by have := length_le_index t; dsimp [m]; omega
  have hnm : n + 2 ≤ m := by have := length_le_index t; dsimp [m]; omega
  have hjm : S.cutoff < m := hjK.trans_lt hKm
  have hmA : m ∉ A := S.avoids t ht hlevel.le
  let Other := {a : Front S.tree S.level // a ≠ v}
  have hext : ∀ a : Other, ∃ w, w ∈ S.tree.tree ∧ a.val.val <+: w ∧ w.length = ell := by
    intro a
    exact extension_at_level S.tree a.val.prop.1 ell (by
      rw [a.val.prop.2]; dsimp [ell]; omega)
  choose w hw hprefix hlength using hext
  have hother := fun a : Other => decide_prefix x m (S.tree.restrict (w a) (hw a))
  choose G hG z hz using hother
  have hblock := fun i : Fin (growthP m ^ (n + 1)) =>
    decide_prefix x m (S.tree.restrict (t ++ [f i]) (hchildren i))
  choose H hH y hy using hblock
  let colors : Fin (growthP m ^ (n + 1)) → Color m := fun i k => y i k.val
  obtain ⟨color, e, he⟩ := thin_growth m n colors
  let I := Other ⊕ Fin (growthP m ^ n)
  letI : Nonempty I := ⟨Sum.inr ⟨0, pow_pos (growth_pos m).1 n⟩⟩
  let stem : I → List ℕ := Sum.elim w (fun i => t ++ [f (e i)])
  let F : I → Condition := Sum.elim G (fun i => H (e i))
  let val : ∀ i : I, ∀ k, Fin (growthN k) := Sum.elim z (fun i => y (e i))
  let parent : I → Front S.tree S.level := Sum.elim Subtype.val (fun _ => v)
  have valid : ∀ i, stem i ∈ S.tree.tree := by
    intro i; cases i with
    | inl a => exact hw a
    | inr i => exact hchildren (e i)
  have lengths : ∀ i, (stem i).length = ell := by
    intro i; cases i with
    | inl a => exact hlength a
    | inr i => simp only [stem, Sum.elim_inr, List.length_append, List.length_singleton, ell]
  have prefixes : ∀ i, (parent i).val <+: stem i := by
    intro i; cases i with
    | inl a => exact hprefix a
    | inr i => exact hvt.1.trans (List.prefix_append _ _)
  have same_parent : ∀ i j, stem i = stem j → parent i = parent j := by
    intro i j hij
    apply Subtype.ext
    have hlen : (parent i).val.length = (parent j).val.length :=
      (parent i).prop.2.trans (parent j).prop.2.symm
    have hj : (parent j).val <+: stem i := by simpa only [hij] using prefixes j
    exact (List.prefix_of_prefix_length_le (prefixes i) hj hlen.le).eq_of_length hlen
  have distinct : Function.Injective stem := by
    intro i j hij
    have hp := same_parent i j hij
    cases i with
    | inl a => cases j with
      | inl b => exact congrArg Sum.inl (Subtype.ext hp)
      | inr b => exact (a.prop hp).elim
    | inr a => cases j with
      | inl b => exact (b.prop hp.symm).elim
      | inr b =>
        apply congrArg Sum.inr
        apply e.injective
        apply hf
        have := List.append_cancel_left hij
        simpa only [List.singleton_inj] using this
  have below : ∀ i, F i ≤ S.tree.restrict (stem i) (valid i) := by
    intro i; cases i with
    | inl a => exact hG a
    | inr i => exact hH (e i)
  have decisions : ∀ i k, k < m → condition Condition (F i) ≤ x.entry k (val i k) := by
    intro i; cases i with
    | inl a => exact hz a
    | inr i => exact hy (e i)
  have below_parent : ∀ i, F i ≤ S.tree.restrict (parent i).val (parent i).prop.1 := by
    intro i
    exact (below i).trans (restrict_below_prefix S.tree (parent i).prop.1 (valid i) (prefixes i))
  have inherits : ∀ i k, k < S.cutoff → val i k = S.value (parent i) k := by
    intro i k hk
    exact (decision_preserved x k (below_parent i)
      (S.decides (parent i) k hk) (decisions i k (hk.trans hjm))).symm
  have covers : ∀ a : Front S.tree S.level, ∃ i, a.val <+: stem i := by
    intro a
    by_cases ha : a = v
    · subst a
      refine ⟨Sum.inr ⟨0, pow_pos (growth_pos m).1 n⟩, ?_⟩
      simpa only [parent, Sum.elim_inr] using
        (prefixes (Sum.inr ⟨0, pow_pos (growth_pos m).1 n⟩))
    · refine ⟨Sum.inl ⟨a, ha⟩, ?_⟩
      simpa only [parent, Sum.elim_inl] using (prefixes (Sum.inl ⟨a, ha⟩))
  let R := union F
  let equiv : I ≃ Front R ell := selectedFrontEquiv valid lengths distinct below
  let newval : ∀ a : Front R ell, ∀ k, Fin (growthN k) := fun a => val (equiv.symm a)
  have newval_eq (i : I) (k : ℕ) : newval (equiv i) k = val i k := by
    simp only [newval, Equiv.symm_apply_apply]
  have newdecides : ∀ a k, k < m →
      condition Condition (R.restrict a.val a.prop.1) ≤ x.entry k (newval a k) := by
    intro a k hk
    obtain ⟨i, rfl⟩ := equiv.surjective a
    change condition Condition (R.restrict (stem i) _) ≤ x.entry k (newval (equiv i) k)
    rw [newval_eq, selected_restrict_eq valid lengths distinct below]
    exact decisions i k hk
  have past : ∀ k ∈ A, k < m → (valueSet (fun a => newval a k)).card ≤ growthP k := by
    intro k hkA hkm
    by_cases hkj : k < S.cutoff
    · apply le_trans (Finset.card_le_card (show
          valueSet (fun a => newval a k) ⊆ valueSet (fun a => S.value a k) from ?_))
        (S.past k hkA hkj)
      intro b hb
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨parent (equiv.symm a), Finset.mem_univ _,
        (inherits (equiv.symm a) k hkj).symm⟩
    · let oldval : Front S.tree S.level → Fin (growthN k) :=
        fun a => if ha : a = v then color ⟨k, hkm⟩ else z ⟨a, ha⟩ k
      have hfactor : ∀ i, val i k = oldval (parent i) := by
        intro i; cases i with
        | inl a =>
          rcases a with ⟨a, ha⟩
          simp only [val, parent, Sum.elim_inl, oldval, dif_neg ha]
        | inr i =>
          have hc := congrFun (he i) ⟨k, hkm⟩
          simpa only [colors, val, parent, Sum.elim_inr, oldval, dif_pos rfl] using hc
      have hsub : valueSet (fun a => newval a k) ⊆ valueSet oldval := by
        intro b hb
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_image.mpr ⟨parent (equiv.symm a), Finset.mem_univ _,
          (hfactor (equiv.symm a)).symm⟩
      exact (Finset.card_le_card hsub).trans
        ((valueSet_card_le oldval).trans (S.future k hkA (by omega)).le)
  have future : ∀ k ∈ A, m ≤ k → Fintype.card (Front R ell) < growthP k := by
    intro k hkA hmk
    have hmk' : m < k := lt_of_le_of_ne hmk (by intro h; exact hmA (h.symm ▸ hkA))
    have hcard : Fintype.card (Front R ell) ≤
        Fintype.card (Front S.tree S.level) + growthP m ^ n := by
      rw [← Fintype.card_congr equiv]
      change Fintype.card (Other ⊕ Fin (growthP m ^ n)) ≤ _
      rw [Fintype.card_sum, Fintype.card_fin]
      exact Nat.add_le_add_right (Fintype.card_subtype_le (fun a : Front S.tree S.level => a ≠ v)) _
    exact hcard.trans_lt (future_front_bound (S.future K hKA hjK) hKm.le hnm hmk')
  let U : Stage x A := {
    tree := R
    level := ell
    cutoff := m
    cutoff_two := S.cutoff_two.trans hjm.le
    value := newval
    decides := newdecides
    past := past
    future := future
    avoids := by
      intro s hs hlen
      exact S.avoids s (selected_union_le valid below hs) (by dsimp [ell] at hlen; omega) }
  refine ⟨U, ?_⟩
  refine {
    below := selected_union_le valid below
    level_lt := by dsimp [U, ell]; omega
    cutoff_lt := hjm
    agrees := selected_preserves_level valid below S.level covers
    split := ?_ }
  have childmem : ∀ i : Fin (growthP m ^ n), t ++ [f (e i)] ∈ R.tree :=
    fun i => selected_stem_mem valid below (Sum.inr i)
  refine ⟨t, ?_, hvt, by dsimp [U, ell]; omega, fun i => f (e i), hf.comp e.injective, childmem⟩
  exact Descriptive.Tree.mem_of_prefix (List.prefix_append _ _)
    (childmem ⟨0, pow_pos (growth_pos m).1 n⟩)

#print axioms growthP_mono
#print axioms future_front_bound
#print axioms advance

end

end Classicism.Meta.Research.MaxAtomicityJechShelahLocalStage
