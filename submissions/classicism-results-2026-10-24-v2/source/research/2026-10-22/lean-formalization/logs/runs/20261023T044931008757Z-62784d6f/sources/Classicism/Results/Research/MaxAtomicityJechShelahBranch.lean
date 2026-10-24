import Classicism.Results.Research.MaxAtomicityJechShelahEnumeration
import Classicism.Results.Research.MaxAtomicityJechShelahRigidityCriterion
import Mathlib.Data.Fintype.Card

/-!
# The canonical branch escapes every ground slalom

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), p. 753,
the proof of (12). The branch is represented here by explicit finite Boolean
partitions rather than by a postulated forcing-name interpretation.

The row for a node records the next branch digit when the branch passes
through that node, and records zero otherwise. Its partition laws follow
from the actual cylinder algebra. Large splitting produces an unused digit
for every slalom. This proves the branch half of the rigidity criterion.
The separate local fusion estimate is not supplied by this module.
Source awaits the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahBranch

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahEnumeration MaxAtomicityJechShelahCylinders
open MaxAtomicityJechShelahRigidityCriterion MaxAtomicitySlalomInvariance

noncomputable section

private theorem successor_of_prefix {s a : List ℕ} (h : s <+: a)
    (hlen : a.length = s.length + 1) : ∃ i : ℕ, a = s ++ [i] := by
  obtain ⟨u, rfl⟩ := h
  have hu : u.length = 1 := by simpa only [List.length_append, Nat.add_left_cancel_iff] using hlen
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hu
  exact ⟨i, rfl⟩

theorem child_cylinder_le (s : List ℕ) (hs : MasterNode s)
    (i : Fin (growthN (index s))) : cylinder (s ++ [i.1]) ≤ cylinder s := by
  have hsi := (master_append_iff s i.1).2 ⟨hs, i.2⟩
  rw [cylinder_of_master hsi, cylinder_of_master hs]
  apply condition_mono
  intro a ha
  refine ⟨ha.1, ?_⟩
  rcases ha.2 with h | h
  · exact List.prefix_or_prefix_of_prefix h (s.prefix_append [i.1])
  · exact Or.inr ((s.prefix_append [i.1]).trans h)

/-- The next-level children cover exactly their parent cylinder. -/
theorem children_cover (s : List ℕ) (hs : MasterNode s) :
    (⨆ i : Fin (growthN (index s)), cylinder (s ++ [i.1])) = cylinder s := by
  apply le_antisymm
  · exact iSup_le (child_cylinder_le s hs)
  · apply le_of_dense_refinements
    intro Q hQ
    have hQS : Q ≤ masterCondition.restrict s hs := by
      apply (condition_le_iff forcing_separative _ _).1
      simpa only [cylinder_of_master hs] using hQ
    obtain ⟨a, ha, hlen⟩ := exists_node_at_level Q (s.length + 1)
    have hsa : s <+: a := by
      rcases (hQS ha).2 with h | h
      · have := h.length_le
        omega
      · exact h
    obtain ⟨i, hi⟩ := successor_of_prefix hsa hlen
    have hiN : i < growthN (index s) :=
      (master_append_iff s i).1 (hi ▸ Q.submaster ha) |>.2
    refine ⟨Q.restrict a ha, Q.restrict_le a ha, ?_⟩
    calc
      condition Condition (Q.restrict a ha) ≤ cylinder a := restrict_le_cylinder Q a ha
      _ = cylinder (s ++ [i]) := congrArg cylinder hi
      _ ≤ ⨆ j : Fin (growthN (index s)), cylinder (s ++ [j.1]) := le_iSup _ ⟨i, hiN⟩

def indexedNode (k : ℕ) : List ℕ := (masterIndexEquiv.symm k).1

theorem indexedNode_master (k : ℕ) : MasterNode (indexedNode k) :=
  (masterIndexEquiv.symm k).2

theorem indexedNode_index (k : ℕ) : index (indexedNode k) = k :=
  masterIndexEquiv.apply_symm_apply k

theorem indexedNode_of_index (s : List ℕ) (hs : MasterNode s) :
    indexedNode (index s) = s :=
  index_injective _ _ (indexedNode_master _) hs (indexedNode_index _)

def child (k : ℕ) (i : Fin (growthN k)) : B := cylinder (indexedNode k ++ [i.1])
def parent (k : ℕ) : B := cylinder (indexedNode k)

theorem child_le_parent (k : ℕ) (i : Fin (growthN k)) : child k i ≤ parent k := by
  have h := child_cylinder_le (indexedNode k) (indexedNode_master k)
  simpa only [indexedNode_index] using h i

theorem child_cover (k : ℕ) : (⨆ i : Fin (growthN k), child k i) = parent k := by
  simpa only [indexedNode_index, child, parent] using
    children_cover (indexedNode k) (indexedNode_master k)

theorem child_disjoint (k : ℕ) (i j : Fin (growthN k)) (hij : i ≠ j) :
    child k i ⊓ child k j = ⊥ := by
  apply cylinders_disjoint (by simp)
  intro h
  apply hij
  apply Fin.ext
  simpa using h

theorem child_inf_parent_compl (k : ℕ) (i : Fin (growthN k)) :
    child k i ⊓ (parent k)ᶜ = ⊥ := by
  apply le_bot_iff.mp
  calc
    child k i ⊓ (parent k)ᶜ ≤ parent k ⊓ (parent k)ᶜ :=
      inf_le_inf_right _ (child_le_parent k i)
    _ = ⊥ := inf_compl_eq_bot

def branchEntry (k : ℕ) (i : Fin (growthN k)) : B :=
  child k i ⊔ if i.1 = 0 then (parent k)ᶜ else ⊥

theorem child_le_branchEntry (k : ℕ) (i : Fin (growthN k)) : child k i ≤ branchEntry k i :=
  le_sup_left

theorem branchEntry_disjoint (k : ℕ) (i j : Fin (growthN k)) (hij : i ≠ j) :
    branchEntry k i ⊓ branchEntry k j = ⊥ := by
  classical
  have hboth : ¬ (i.1 = 0 ∧ j.1 = 0) := by
    rintro ⟨hi, hj⟩
    exact hij (Fin.ext (hi.trans hj.symm))
  by_cases hi : i.1 = 0 <;> by_cases hj : j.1 = 0
  · exact (hboth ⟨hi, hj⟩).elim
  · simp only [branchEntry, if_pos hi, if_neg hj, sup_bot_eq, inf_sup_right,
      child_disjoint k i j hij, inf_comm ((parent k)ᶜ), child_inf_parent_compl, bot_sup_eq]
  · simp only [branchEntry, if_neg hi, if_pos hj, sup_bot_eq, inf_sup_left,
      child_disjoint k i j hij, child_inf_parent_compl, bot_sup_eq]
  · simp only [branchEntry, if_neg hi, if_neg hj, sup_bot_eq, child_disjoint k i j hij]

theorem branchEntry_cover (k : ℕ) : (⨆ i : Fin (growthN k), branchEntry k i) = ⊤ := by
  apply top_le_iff.mp
  have hp : parent k ≤ ⨆ i : Fin (growthN k), branchEntry k i := by
    rw [← child_cover k]
    exact iSup_le (fun i => (child_le_branchEntry k i).trans (le_iSup _ i))
  let zero : Fin (growthN k) := ⟨0, (growth_pos k).2⟩
  have hc : (parent k)ᶜ ≤ branchEntry k zero := by
    simp only [branchEntry, zero, if_pos rfl]
    exact le_sup_right
  calc
    ⊤ = parent k ⊔ (parent k)ᶜ := sup_compl_eq_top.symm
    _ ≤ ⨆ i : Fin (growthN k), branchEntry k i := sup_le hp (hc.trans (le_iSup _ zero))

/-- The actual partition-valued name used to witness failure of coverage. -/
def branchName : BoundedName growthN B where
  entry := branchEntry
  row_disjoint := branchEntry_disjoint
  row_cover := branchEntry_cover

theorem entry_inf_slalomRow (u : Slalom growthN growthP) (k : ℕ)
    (i : Fin (growthN k)) (hi : i ∉ u.entries k) :
    branchName.entry k i ⊓ (⨆ j ∈ u.entries k, branchName.entry k j) = ⊥ := by
  rw [inf_iSup_eq]
  apply le_bot_iff.mp
  apply iSup_le
  intro j
  rw [inf_iSup_eq]
  apply iSup_le
  intro hj
  rw [branchName.row_disjoint k i j (by intro h; exact hi (h.symm ▸ hj))]

/-- Every ground slalom misses a next digit available below any condition.
This is a finite pigeonhole argument on the actual large splitting row. -/
theorem escape_slalom (T : Condition) (u : Slalom growthN growthP) :
    ∃ R : Condition, R ≤ T ∧ ∃ k ∈ nodeIndices T, ∃ i : Fin (growthN k),
      i ∉ u.entries k ∧ condition Condition R ≤ branchName.entry k i := by
  classical
  obtain ⟨v, hv, hlong⟩ := T.exists_long_node 2
  obtain ⟨s, hs, hvs, f, hf, hchildren⟩ := T.bushy v hv 2
  let k := index s
  have hk2 : 2 ≤ growthP k := by
    have := length_le_index s
    have := index_le_growthP (index s)
    have := hvs.2
    omega
  let digits : Fin (growthP k ^ 2) → Fin (growthN k) := fun i =>
    ⟨f i, (master_append_iff s (f i)).1 (T.submaster (hchildren i)) |>.2⟩
  have hd : Function.Injective digits := by
    intro i j h
    exact hf (congrArg Fin.val h)
  have hex : ∃ i : Fin (growthP k ^ 2), digits i ∉ u.entries k := by
    by_contra hn
    have hall : ∀ i, digits i ∈ u.entries k := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    let into : Fin (growthP k ^ 2) → {j // j ∈ u.entries k} := fun i => ⟨digits i, hall i⟩
    have hin : Function.Injective into := fun _ _ h => hd (congrArg Subtype.val h)
    have hc : growthP k ^ 2 ≤ (u.entries k).card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective into hin
    have hbound := hc.trans (u.card_le k)
    have hlt : growthP k < growthP k ^ 2 := by
      rw [pow_two]
      have := Nat.mul_lt_mul_of_pos_left (show 1 < growthP k by omega)
        (show 0 < growthP k by omega)
      simpa only [mul_one] using this
    exact (not_le_of_gt hlt) hbound
  obtain ⟨i, hi⟩ := hex
  refine ⟨T.restrict (s ++ [f i]) (hchildren i), T.restrict_le _ _,
    k, ⟨s, hs, rfl⟩, digits i, hi, ?_⟩
  calc
    condition Condition (T.restrict (s ++ [f i]) (hchildren i))
        ≤ cylinder (s ++ [f i]) := restrict_le_cylinder T _ _
    _ = child k (digits i) := by
      simp only [child, k, indexedNode_of_index s (T.submaster hs), digits]
    _ ≤ branchName.entry k (digits i) := child_le_branchEntry k (digits i)

theorem branch_inf_capture (T : Condition) (u : Slalom growthN growthP) :
    condition Condition T ⊓ capture (nodeIndices T) branchName u = ⊥ := by
  classical
  by_contra hn
  obtain ⟨Q, hQ⟩ := condition_dense hn
  have hQT : Q ≤ T :=
    (condition_le_iff forcing_separative Q T).1 (hQ.trans inf_le_left)
  obtain ⟨R, hRQ, k, hk, i, hi, hRi⟩ := escape_slalom Q u
  have hkT : k ∈ nodeIndices T := by
    obtain ⟨s, hs, hsk⟩ := hk
    exact ⟨s, hQT hs, hsk⟩
  have hcap : condition Condition R ≤ capture (nodeIndices T) branchName u :=
    (condition_mono hRQ).trans (hQ.trans inf_le_right)
  have hrow : condition Condition R ≤ ⨆ j ∈ u.entries k, branchName.entry k j :=
    hcap.trans ((iInf_le _ k).trans (iInf_le _ hkT))
  apply condition_ne_bot R
  apply le_bot_iff.mp
  calc
    condition Condition R ≤ branchName.entry k i ⊓
        (⨆ j ∈ u.entries k, branchName.entry k j) := le_inf hRi hrow
    _ = ⊥ := entry_inf_slalomRow u k i hi

/-- The branch witnesses failure of all ground slaloms on the indices of T. -/
theorem condition_le_branch_cover_compl (T : Condition) :
    condition Condition T ≤ (cover growthP (nodeIndices T) branchName)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff.mpr
  unfold cover
  rw [inf_iSup_eq]
  apply le_bot_iff.mp
  apply iSup_le
  intro u
  rw [branch_inf_capture T u]

/-- This discharges the branch field of SlalomSeparation for the actual
forcing. The separate local field still requires the fusion construction. -/
theorem condition_le_marker (T : Condition) : condition Condition T ≤ marker T :=
  (condition_le_branch_cover_compl T).trans
    (le_iSup (fun x : BoundedName growthN B =>
      (cover growthP (nodeIndices T) x)ᶜ) branchName)

end

end Classicism.Meta.Research.MaxAtomicityJechShelahBranch

#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahBranch.children_cover
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahBranch.branchName
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahBranch.escape_slalom
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahBranch.branch_inf_capture
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahBranch.condition_le_marker
