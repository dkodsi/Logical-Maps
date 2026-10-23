import Classicism.Results.Research.MaxAtomicityJechShelahAmalgamation

/-!
# Refinement along a selected finite level

The local slalom recursion retains one extension of each old front node, except
at one branch where it keeps many equal-color extensions. These lemmas verify
the geometric and Boolean parts for the actual selected stems: their union is
an actual condition, has exactly those stems at the new level, preserves the
old level whenever every old node has a selected extension, and restricts back
to each chosen subtree. Refining a decision preserves the decided value by
the actual name's disjoint partition law.

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 753--754, the
two cases in construction (14). Original formal transcription: misc,
23 October 2026, unpaginated. This does not assume or prove the complete
infinite-stage slalom bound. Source preparation is not a successful Lean check.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahFiniteRefinement

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahCylinders MaxAtomicitySlalomInvariance
open MaxAtomicityJechShelahAmalgamation

noncomputable section

variable {I : Type*} [Nonempty I]
variable {T : Condition} {level : ℕ} {stem : I → List ℕ}
variable (valid : ∀ i, stem i ∈ T.tree) (lengths : ∀ i, (stem i).length = level)
variable (distinct : Function.Injective stem)
variable {F : I → Condition} (below : ∀ i, F i ≤ T.restrict (stem i) (valid i))

theorem selected_stem_mem (i : I) : stem i ∈ (union F).tree :=
  ⟨i, Condition.stem_mem_of_le_restrict (below i)⟩

theorem selected_union_le : union F ≤ T :=
  union_le F (fun i => (below i).trans (T.restrict_le (stem i) (valid i)))

/-- At the selected level there are precisely the selected stems. -/
theorem selected_level_iff (s : List ℕ) (hlen : s.length = level) :
    s ∈ (union F).tree ↔ ∃ i, s = stem i := by
  constructor
  · rintro ⟨i, hi⟩
    have hslen : s.length = (stem i).length := hlen.trans (lengths i).symm
    rcases (below i hi).2 with hsi | his
    · exact ⟨i, hsi.eq_of_length hslen⟩
    · exact ⟨i, (his.eq_of_length hslen.symm).symm⟩
  · rintro ⟨i, rfl⟩
    exact selected_stem_mem valid below i

/-- The next front is concretely equivalent to the index set of chosen stems. -/
def selectedFrontEquiv : I ≃ Front (union F) level :=
  Equiv.ofBijective
    (fun i => ⟨stem i, selected_stem_mem valid below i, lengths i⟩)
    ⟨by
      intro i j h
      exact distinct (congrArg Subtype.val h), by
      intro a
      obtain ⟨i, hi⟩ := (selected_level_iff valid lengths below a.val a.prop.2).mp a.prop.1
      exact ⟨i, Subtype.ext hi.symm⟩⟩

theorem selected_front_card [Fintype I] : Fintype.card (Front (union F) level) = Fintype.card I :=
  (Fintype.card_congr (selectedFrontEquiv valid lengths distinct below)).symm

/-- Covering each old front node by a selected extension preserves that whole
level, even if many new stems lie above one old node. -/
theorem selected_preserves_level (oldLevel : ℕ)
    (covers : ∀ a : Front T oldLevel, ∃ i, a.val <+: stem i)
    (s : List ℕ) (hlen : s.length = oldLevel) :
    s ∈ (union F).tree ↔ s ∈ T.tree := by
  constructor
  · exact selected_union_le valid below
  · intro hs
    obtain ⟨i, hi⟩ := covers ⟨s, hs, hlen⟩
    exact ⟨i, Descriptive.Tree.mem_of_prefix hi
      (Condition.stem_mem_of_le_restrict (below i))⟩

/-- Restricting the union at one of the selected stems recovers exactly its
chosen subtree, rather than merely a common weakening. -/
theorem selected_restrict_eq (i : I) :
    (union F).restrict (stem i) (selected_stem_mem valid below i) = F i := by
  apply le_antisymm
  · intro s hs
    rcases hs.2 with hsi | his
    · exact Descriptive.Tree.mem_of_prefix hsi (Condition.stem_mem_of_le_restrict (below i))
    · obtain ⟨j, hj⟩ := hs.1
      have hlen : (stem i).length = (stem j).length := (lengths i).trans (lengths j).symm
      have hstems : stem i = stem j := by
        rcases (below j hj).2 with hsj | hjs
        · exact (his.trans hsj).eq_of_length hlen
        · exact (List.prefix_of_prefix_length_le his hjs hlen.le).eq_of_length hlen
      have hij := distinct hstems
      subst j
      exact hj
  · intro s hs
    exact ⟨⟨i, hs⟩, (below i hs).2⟩

/-- The Boolean value of a selected-stem refinement is the join of the values
of precisely the selected subtrees. -/
theorem selected_union_value :
    condition Condition (union F) = ⨆ i : I, condition Condition (F i) := by
  apply le_antisymm
  · apply le_of_dense_refinements
    intro Q hQ
    have hQU : Q ≤ union F := (condition_le_iff forcing_separative Q (union F)).mp hQ
    obtain ⟨s, hs, hlen⟩ := exists_node_at_level Q level
    obtain ⟨i, hsi⟩ := (selected_level_iff valid lengths below s hlen).mp (hQU hs)
    have hQi : stem i ∈ Q.tree := by simpa only [hsi] using hs
    have hR : Q.restrict (stem i) hQi ≤
        (union F).restrict (stem i) (selected_stem_mem valid below i) :=
      fun _ hu => ⟨hQU hu.1, hu.2⟩
    rw [selected_restrict_eq valid lengths distinct below i] at hR
    exact ⟨Q.restrict (stem i) hQi, Q.restrict_le (stem i) hQi,
      (condition_mono hR).trans (le_iSup (fun i => condition Condition (F i)) i)⟩
  · exact iSup_le (fun i => condition_mono (member_le_union F i))

/-- Partition disjointness forces actual decisions made by a nonzero condition
to agree. This supplies the coherence used for old-coordinate slalom bounds. -/
theorem decision_unique (x : BoundedName growthN B) (k : ℕ) (Q : Condition)
    {i j : Fin (growthN k)} (hi : condition Condition Q ≤ x.entry k i)
    (hj : condition Condition Q ≤ x.entry k j) : i = j := by
  classical
  by_contra hne
  apply condition_ne_bot Q
  apply le_bot_iff.mp
  calc
    condition Condition Q ≤ x.entry k i ⊓ x.entry k j := le_inf hi hj
    _ = ⊥ := x.row_disjoint k i j hne

theorem decision_preserved (x : BoundedName growthN B) (k : ℕ)
    {Q R : Condition} (hRQ : R ≤ Q) {i j : Fin (growthN k)}
    (hi : condition Condition Q ≤ x.entry k i)
    (hj : condition Condition R ≤ x.entry k j) : i = j :=
  decision_unique x k R ((condition_mono hRQ).trans hi) hj

/-- Simultaneous finite decisions on all selected stems are constructed by
choice from the already proved actual finite-decision theorem. -/
theorem decide_selected (x : BoundedName growthN B) (cutoff : ℕ) :
    ∃ G : I → Condition, (∀ i, G i ≤ T.restrict (stem i) (valid i)) ∧
      ∃ z : ∀ i : I, ∀ k, Fin (growthN k),
        ∀ i k, k < cutoff → condition Condition (G i) ≤ x.entry k (z i k) := by
  classical
  have h := fun i : I => decide_prefix x cutoff (T.restrict (stem i) (valid i))
  choose G hG z hz using h
  exact ⟨G, hG, z, hz⟩

#print axioms selectedFrontEquiv
#print axioms selected_front_card
#print axioms selected_preserves_level
#print axioms selected_restrict_eq
#print axioms selected_union_value
#print axioms decision_unique
#print axioms decision_preserved
#print axioms decide_selected

end

end Classicism.Meta.Research.MaxAtomicityJechShelahFiniteRefinement
