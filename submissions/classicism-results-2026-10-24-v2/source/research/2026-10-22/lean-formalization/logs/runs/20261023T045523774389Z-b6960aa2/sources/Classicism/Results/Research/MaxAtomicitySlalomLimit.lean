import Classicism.Results.Research.MaxAtomicityJechShelahAmalgamation

/-!
# Extracting one ground slalom from finite fusion decisions

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), p. 753,
the passage from (14) to (13). This proof uses the actual Boolean-valued
partition names and the constructed fusion condition.

The input consists of finite-stage decisions and their proved cardinal bounds,
not a slalom or a capture conclusion. A ground slalom is constructed by taking
the finite set of decided values at the least stage that decides a coordinate.
Its bounds and Boolean capture of the fused condition are then proved.
Constructing the finite-stage data for every input name remains a separate
obligation. Source awaits the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicitySlalomLimit

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahCylinders MaxAtomicityJechShelahFusion
open MaxAtomicityJechShelahAmalgamation MaxAtomicitySlalomInvariance

noncomputable section

/-- A condition is the Boolean join of its restrictions at any fixed level. -/
theorem condition_eq_iSup_restrictions (T : Condition) (l : ℕ) :
    condition Condition T =
      ⨆ a : Front T l, condition Condition (T.restrict a.1 a.2.1) := by
  apply le_antisymm
  · apply le_of_dense_refinements
    intro Q hQ
    have hQT : Q ≤ T := (condition_le_iff forcing_separative Q T).1 hQ
    obtain ⟨s, hs, hlen⟩ := exists_node_at_level Q l
    let a : Front T l := ⟨s, hQT hs, hlen⟩
    have hR : Q.restrict s hs ≤ T.restrict a.1 a.2.1 :=
      fun _ hv => ⟨hQT hv.1, hv.2⟩
    refine ⟨Q.restrict s hs, Q.restrict_le s hs, ?_⟩
    exact (condition_mono hR).trans (le_iSup _ a)
  · exact iSup_le (fun a => condition_mono (T.restrict_le a.1 a.2.1))

/-- Finite data maintained by the local fusion construction. Values outside
the decided initial segment are arbitrary; the correctness fields quantify
only over the specified coordinates and cutoff. -/
structure FusionReadout (A : Set ℕ) (x : BoundedName growthN B) where
  fusion : FusionSequence
  cutoff : ℕ → ℕ
  cofinal : ∀ k : ℕ, ∃ n : ℕ, k < cutoff n
  value : ∀ n : ℕ, Front (fusion.tree n) (fusion.level n) → ∀ k : ℕ, Fin (growthN k)
  decided : ∀ n a k, k ∈ A → k < cutoff n →
    condition Condition ((fusion.tree n).restrict a.1 a.2.1) ≤ x.entry k (value n a k)
  bound : ∀ n k, k ∈ A → k < cutoff n →
    (Finset.univ.image (fun a : Front (fusion.tree n) (fusion.level n) => value n a k)).card
      ≤ growthP k

namespace FusionReadout

variable {A : Set ℕ} {x : BoundedName growthN B} (F : FusionReadout A x)

def stage (k : ℕ) : ℕ := Nat.find (F.cofinal k)

theorem stage_spec (k : ℕ) : k < F.cutoff (F.stage k) := Nat.find_spec (F.cofinal k)

/-- A particular ground finite set for each coordinate, chosen from actual
finite-stage data. This does not use a Boolean choice or a generic object. -/
def slalom : Slalom growthN growthP := by
  classical
  exact {
  entries := fun k => if k ∈ A then
    Finset.univ.image (fun a : Front (F.fusion.tree (F.stage k)) (F.fusion.level (F.stage k)) =>
      F.value (F.stage k) a k) else ∅
  card_le := fun k => by
    by_cases hk : k ∈ A
    · simp only [if_pos hk]
      exact F.bound (F.stage k) k hk (F.stage_spec k)
    · simp only [if_neg hk, Finset.card_empty]
      exact Nat.zero_le _ }

theorem selected_value_mem (k : ℕ) (hk : k ∈ A)
    (a : Front (F.fusion.tree (F.stage k)) (F.fusion.level (F.stage k))) :
    F.value (F.stage k) a k ∈ F.slalom.entries k := by
  classical
  simp only [slalom, if_pos hk]
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

theorem stage_le_slalom_row (k : ℕ) (hk : k ∈ A) :
    condition Condition (F.fusion.tree (F.stage k)) ≤
      ⨆ i ∈ F.slalom.entries k, x.entry k i := by
  rw [condition_eq_iSup_restrictions _ (F.fusion.level (F.stage k))]
  apply iSup_le
  intro a
  exact (F.decided (F.stage k) a k hk (F.stage_spec k)).trans
    (le_iSup_of_le (F.value (F.stage k) a k)
      (le_iSup_of_le (F.selected_value_mem k hk a) le_rfl))

/-- The actual fused condition is captured by the constructed single slalom. -/
theorem fuse_le_capture :
    condition Condition F.fusion.fuse ≤ capture A x F.slalom := by
  apply le_iInf
  intro k
  apply le_iInf
  intro hk
  exact (condition_mono (F.fusion.fuse_le (F.stage k))).trans
    (F.stage_le_slalom_row k hk)

theorem fuse_le_cover : condition Condition F.fusion.fuse ≤ cover growthP A x :=
  F.fuse_le_capture.trans (le_iSup _ F.slalom)

end FusionReadout

end

end Classicism.Meta.Research.MaxAtomicitySlalomLimit

#print axioms Classicism.Meta.Research.MaxAtomicitySlalomLimit.condition_eq_iSup_restrictions
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomLimit.FusionReadout.stage_spec
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomLimit.FusionReadout.slalom
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomLimit.FusionReadout.fuse_le_capture
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomLimit.FusionReadout.fuse_le_cover
