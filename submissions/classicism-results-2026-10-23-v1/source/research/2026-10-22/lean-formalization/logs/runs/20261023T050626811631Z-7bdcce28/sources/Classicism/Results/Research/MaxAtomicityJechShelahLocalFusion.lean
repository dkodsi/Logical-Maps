import Classicism.Results.Research.MaxAtomicityJechShelahLocalStage
import Classicism.Results.Research.MaxAtomicitySlalomLimit
import Classicism.Results.Research.MaxAtomicityJechShelahBranch

/-!
# The local slalom construction and rigidity of the concrete completion

This module constructs the initial finite stage, recursively applies the actual
stage theorem, forms the actual fusion condition, and extracts its ground
slalom. For each name the construction works densely below a stem outside T;
the same fixed stem therefore lies below every name's cover. This is the
uniform Boolean estimate required by the rigidity criterion, not a choice of
one condition simultaneously deciding all names.

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 753--754,
the local half of (13) and the proof of rigidity. The uniform-stage recursion
and explicit Boolean organization are original transcription (misc,
23 October 2026). These proof sources await the designated serial Lean checker.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahLocalFusion

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahEnumeration MaxAtomicityJechShelahFusion
open MaxAtomicityJechShelahCylinders MaxAtomicitySlalomInvariance
open MaxAtomicityJechShelahAmalgamation MaxAtomicityJechShelahFiniteRefinement
open MaxAtomicityJechShelahLocalStage MaxAtomicitySlalomLimit
open MaxAtomicityJechShelahRigidityCriterion MaxAtomicityJechShelahBranch

noncomputable section

theorem nodeIndices_unbounded (T : Condition) (j : ℕ) :
    ∃ k ∈ nodeIndices T, j ≤ k := by
  obtain ⟨s, hs, hlen⟩ := T.exists_long_node j
  exact ⟨index s, ⟨s, hs, rfl⟩, hlen.trans (length_le_index s)⟩

/-- A sufficiently long forbidden stem supplies all initial bounds. The
finite prefix is decided on the whole refined condition, so its front has at
most one possible value at every coordinate. -/
theorem initial_stage (T Q : Condition) (x : BoundedName growthN B)
    (b : List ℕ) (hb : b ∈ Q.tree) (hnot : b ∉ T.tree) (hblen : 2 ≤ b.length) :
    ∃ S : Stage x (nodeIndices T), S.tree ≤ Q := by
  classical
  obtain ⟨R, hRQ, z, hz⟩ := decide_prefix x b.length (Q.restrict b hb)
  have hbR : b ∈ R.tree := Condition.stem_mem_of_le_restrict hRQ
  have front_eq : ∀ a : Front R b.length, a.val = b := by
    intro a
    rcases (hRQ a.prop.1).2 with hab | hba
    · exact hab.eq_of_length a.prop.2
    · exact (hba.eq_of_length a.prop.2.symm).symm
  have front_card : Fintype.card (Front R b.length) ≤ 1 := by
    have h := Fintype.card_le_of_injective
      (fun _ : Front R b.length => (0 : Fin 1)) (by
        intro a c _
        exact Subtype.ext ((front_eq a).trans (front_eq c).symm))
    simpa only [Fintype.card_fin] using h
  let S : Stage x (nodeIndices T) := {
    tree := R
    level := b.length
    cutoff := b.length
    cutoff_two := hblen
    value := fun _ => z
    decides := fun a k hk => (condition_mono (R.restrict_le a.val a.prop.1)).trans (hz k hk)
    past := fun k _ _ => (valueSet_card_le (fun _ : Front R b.length => z k)).trans
      (front_card.trans (growth_pos k).1)
    future := fun k _ hk => front_card.trans_lt (by
      have := growthP_two k (hblen.trans hk)
      omega)
    avoids := by
      intro s hs hlen hindex
      have hbs : b <+: s := by
        rcases (hRQ hs).2 with hsb | hbs
        · have heq : s = b := hsb.eq_of_length_le hlen
          simpa only [heq] using List.prefix_refl b
        · exact hbs
      obtain ⟨a, ha, hai⟩ := hindex
      have has : a = s := index_injective a s (T.submaster ha) (R.submaster hs) hai
      exact hnot (Descriptive.Tree.mem_of_prefix hbs (has ▸ ha)) }
  exact ⟨S, hRQ.trans (Q.restrict_le b hb)⟩

/-- The scheduled successor includes the retained split for the unique
master node of index n, if that node still occurs in the current tree. -/
structure Next {x : BoundedName growthN B} {A : Set ℕ}
    (S U : Stage x A) (n : ℕ) : Prop where
  below : U.tree ≤ S.tree
  level_lt : S.level < U.level
  cutoff_lt : S.cutoff < U.cutoff
  agrees : ∀ s, s.length = S.level → (s ∈ U.tree.tree ↔ s ∈ S.tree.tree)
  split : ∀ s, index s = n → s ∈ S.tree.tree →
    ∃ t, t ∈ U.tree.tree ∧ StrictExtension s t ∧
      t.length < U.level ∧ ∃ f : Fin (growthP (index t) ^ n) → ℕ,
        Function.Injective f ∧ ∀ i, t ++ [f i] ∈ U.tree.tree

theorem next_exists {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (S : Stage x A) (n : ℕ)
    (hn : n ≤ S.level) : ∃ U : Stage x A, Next S U n := by
  classical
  by_cases hex : ∃ s, index s = n ∧ s ∈ S.tree.tree
  · obtain ⟨s, hsi, hs⟩ := hex
    have hindex : index s ≤ S.level := by simpa only [hsi] using hn
    have hlen : s.length ≤ S.level := (length_le_index s).trans hindex
    obtain ⟨v, hv, hsv, hvlen⟩ := extension_at_level S.tree hs S.level hlen
    let a : Front S.tree S.level := ⟨v, hv, hvlen⟩
    obtain ⟨U, hU⟩ := advance unbounded S a n
    refine ⟨U, hU.below, hU.level_lt, hU.cutoff_lt, hU.agrees, ?_⟩
    intro s' hs'i hs'
    have heq : s' = s := index_injective s' s (S.tree.submaster hs')
      (S.tree.submaster hs) (hs'i.trans hsi.symm)
    subst s'
    obtain ⟨t, ht, hvt, htlen, f, hf, hchildren⟩ := hU.split
    exact ⟨t, ht, ⟨hsv.trans hvt.1, lt_of_le_of_lt hsv.length_le hvt.2⟩,
      htlen, f, hf, hchildren⟩
  · let a : Front S.tree S.level := Classical.choice inferInstance
    obtain ⟨U, hU⟩ := advance unbounded S a n
    refine ⟨U, hU.below, hU.level_lt, hU.cutoff_lt, hU.agrees, ?_⟩
    intro s hsi hs
    exact (hex ⟨s, hsi, hs⟩).elim

def chooseNext {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (S : Stage x A) (n : ℕ)
    (hn : n ≤ S.level) : Stage x A :=
  Classical.choose (next_exists unbounded S n hn)

theorem chooseNext_spec {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (S : Stage x A) (n : ℕ)
    (hn : n ≤ S.level) : Next S (chooseNext unbounded S n hn) n :=
  Classical.choose_spec (next_exists unbounded S n hn)

/-- Natural-number recursion carries the scheduling inequality, so every
requested master node lies at or below the retained level. -/
def tower {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (start : Stage x A) :
    (n : ℕ) → {S : Stage x A // n ≤ S.level}
  | 0 => ⟨start, Nat.zero_le _⟩
  | n + 1 =>
    let previous := tower unbounded start n
    ⟨chooseNext unbounded previous.val n previous.prop,
      previous.prop.trans_lt (chooseNext_spec unbounded previous.val n previous.prop).level_lt⟩

def stageAt {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (start : Stage x A) (n : ℕ) : Stage x A :=
  (tower unbounded start n).val

theorem stageAt_next {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (start : Stage x A) (n : ℕ) :
    Next (stageAt unbounded start n) (stageAt unbounded start (n + 1)) n :=
  chooseNext_spec unbounded (tower unbounded start n).val n (tower unbounded start n).prop

theorem stageAt_cutoff_bound {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (start : Stage x A) (n : ℕ) :
    n ≤ (stageAt unbounded start n).cutoff := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact ih.trans_lt (stageAt_next unbounded start n).cutoff_lt

/-- The fusion sequence is built from the recursion, rather than postulated. -/
def localFusion {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (start : Stage x A) : FusionSequence where
  tree := fun n => (stageAt unbounded start n).tree
  level := fun n => (stageAt unbounded start n).level
  decreasing := fun n => (stageAt_next unbounded start n).below
  level_mono := monotone_nat_of_le_succ (fun n => (stageAt_next unbounded start n).level_lt.le)
  agree_level := fun n => (stageAt_next unbounded start n).agrees
  split := fun n => (stageAt_next unbounded start n).split

def localReadout {x : BoundedName growthN B} {A : Set ℕ}
    (unbounded : ∀ j, ∃ k ∈ A, j ≤ k) (start : Stage x A) : FusionReadout A x where
  fusion := localFusion unbounded start
  cutoff := fun n => (stageAt unbounded start n).cutoff
  cofinal := fun k => ⟨k + 1, (Nat.lt_succ_self k).trans_le
    (stageAt_cutoff_bound unbounded start (k + 1))⟩
  value := fun n => (stageAt unbounded start n).value
  decided := fun n a k _ hk => (stageAt unbounded start n).decides a k hk
  bound := fun n k hkA hk => (stageAt unbounded start n).past k hkA hk

/-- Below every condition containing a sufficiently long forbidden stem,
every actual bounded name has a refinement captured by a ground slalom. -/
theorem exists_local_capture (T Q : Condition) (x : BoundedName growthN B)
    (b : List ℕ) (hb : b ∈ Q.tree) (hnot : b ∉ T.tree) (hblen : 2 ≤ b.length) :
    ∃ R : Condition, R ≤ Q ∧
      condition Condition R ≤ cover growthP (nodeIndices T) x := by
  obtain ⟨start, hstart⟩ := initial_stage T Q x b hb hnot hblen
  let F := localReadout (nodeIndices_unbounded T) start
  refine ⟨F.fusion.fuse, ?_, F.fuse_le_cover⟩
  exact (F.fusion.fuse_le 0).trans hstart

/-- The same fixed forbidden stem is below every name's cover, because the
previous construction is dense below that stem for each name separately. -/
theorem local_separation (T Q : Condition) (hQT : ¬ Q ≤ T) :
    ∃ R : Condition, R ≤ Q ∧ condition Condition R ≤ (marker T)ᶜ := by
  classical
  have hex : ∃ s, s ∈ Q.tree ∧ s ∉ T.tree := by
    by_contra h
    apply hQT
    intro s hs
    by_contra hnot
    exact h ⟨s, hs, hnot⟩
  obtain ⟨s, hs, hnot⟩ := hex
  obtain ⟨b, hb, hsb, hlen⟩ := extension_long Q hs 2
  have hblen : 2 ≤ b.length := by omega
  have hbnot : b ∉ T.tree := fun h => hnot (Descriptive.Tree.mem_of_prefix hsb h)
  let R := Q.restrict b hb
  have hcover : ∀ x : BoundedName growthN B,
      condition Condition R ≤ cover growthP (nodeIndices T) x := by
    intro x
    apply le_of_dense_refinements
    intro S hS
    have hSR : S ≤ Q.restrict b hb := (condition_le_iff forcing_separative S R).mp hS
    have hbS : b ∈ S.tree := Condition.stem_mem_of_le_restrict hSR
    exact exists_local_capture T S x b hbS hbnot hblen
  refine ⟨R, Q.restrict_le b hb, ?_⟩
  calc
    condition Condition R ≤ ⨅ x : BoundedName growthN B,
        cover growthP (nodeIndices T) x := le_iInf hcover
    _ = (marker T)ᶜ := by simp only [marker, invariant, compl_iSup, compl_compl]

/-- Both substantive slalom estimates have now been constructed for the
concrete forcing. No SlalomSeparation hypothesis remains in this declaration. -/
theorem actual_slalomSeparation : SlalomSeparation where
  branch := condition_le_marker
  local := local_separation

/-- Rigidity of the actual regular-open completion of the concrete JS forcing.
This theorem is unconditional ordinary mathematics; its source still needs
the designated serial Lean compilation and transitive axiom audit. -/
theorem actual_rigid : MaxAtomicityRigidTransport.Rigid B :=
  rigid_of_slalomSeparation actual_slalomSeparation

#print axioms initial_stage
#print axioms next_exists
#print axioms localFusion
#print axioms localReadout
#print axioms exists_local_capture
#print axioms local_separation
#print axioms actual_slalomSeparation
#print axioms actual_rigid

end

end Classicism.Meta.Research.MaxAtomicityJechShelahLocalFusion
