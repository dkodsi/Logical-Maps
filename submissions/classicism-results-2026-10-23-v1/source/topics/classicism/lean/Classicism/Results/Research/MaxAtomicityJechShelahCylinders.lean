import Classicism.Results.Research.MaxAtomicityJechShelahTrees
import Classicism.Results.Research.MaxAtomicityCountableGenerator
import Mathlib.Logic.Equiv.List

/-!
# Countable complete generation by the actual branch cylinders

Direct source: the tree forcing and branch construction of Jech--Shelah,
Journal of Algebra 182 (1996), pp. 749--750; the explicit Boolean calculation
and proofs here are original (misc, unpaginated).

For each condition T its Boolean value is the meet, over natural levels n,
of the join of cylinders of nodes of T at level n. This equality is proved
using stem restriction, incompatibility at equal levels, and the density of
conditions in the concrete regular completion. Every completion element is
then a join of condition values, proving complete generation. Encoding finite
sequences by natural numbers supplies an actual countable family.

The final splitter is an external algebraic function. Pure definability and
rigidity remain separate obligations. All sources await the serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahCylinders

set_option backward.isDefEq.respectTransparency false

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityCountableGenerator MaxAtomicityWellOrder

noncomputable section

abbrev B := Completion Condition

private theorem gap_ne_bot {a b : B} (h : ¬ a ≤ b) : a ⊓ bᶜ ≠ ⊥ := by
  intro hz
  apply h
  calc
    a = (a ⊓ b) ⊔ (a ⊓ bᶜ) := (sup_inf_inf_compl (x := a) (y := b)).symm
    _ = a ⊓ b := by rw [hz, sup_bot_eq]
    _ ≤ b := inf_le_right

private theorem eq_bot_of_bounds {a b : B} (h : a ≤ b) (hc : a ≤ bᶜ) : a = ⊥ := by
  apply le_bot_iff.mp
  calc
    a ≤ b ⊓ bᶜ := le_inf h hc
    _ = ⊥ := inf_compl_eq_bot

/-- Dense tests by actual conditions determine Boolean order. -/
theorem le_of_condition_tests {a b : B}
    (h : ∀ T : Condition, condition Condition T ≤ a → condition Condition T ≤ b) :
    a ≤ b := by
  classical
  by_contra hn
  obtain ⟨T, hT⟩ := condition_dense (gap_ne_bot hn)
  exact condition_ne_bot T (eq_bot_of_bounds (h T (hT.trans inf_le_left))
    (hT.trans inf_le_right))

/-- It suffices to find a refinement below b under every condition below a. -/
theorem le_of_dense_refinements {a b : B}
    (h : ∀ T : Condition, condition Condition T ≤ a →
      ∃ S : Condition, S ≤ T ∧ condition Condition S ≤ b) : a ≤ b := by
  classical
  by_contra hn
  obtain ⟨T, hT⟩ := condition_dense (gap_ne_bot hn)
  obtain ⟨S, hST, hSb⟩ := h T (hT.trans inf_le_left)
  exact condition_ne_bot S (eq_bot_of_bounds hSb
    ((condition_mono hST).trans (hT.trans inf_le_right)))

theorem exists_node_at_level (T : Condition) (n : ℕ) :
    ∃ s : List ℕ, s ∈ T.tree ∧ s.length = n := by
  obtain ⟨s, hs, hn⟩ := T.exists_long_node n
  exact ⟨s.take n, Descriptive.Tree.mem_of_prefix (s.take_prefix n) hs,
    by simp only [List.length_take, Nat.min_eq_left hn]⟩

/-- The Boolean value that the generic branch extends a given finite sequence. -/
def cylinder (s : List ℕ) : B := by
  classical
  exact if hs : MasterNode s then condition Condition (masterCondition.restrict s hs) else ⊥

theorem cylinder_of_master {s : List ℕ} (hs : MasterNode s) :
    cylinder s = condition Condition (masterCondition.restrict s hs) := by
  simp only [cylinder, dif_pos hs]

theorem restrict_le_cylinder (T : Condition) (s : List ℕ) (hs : s ∈ T.tree) :
    condition Condition (T.restrict s hs) ≤ cylinder s := by
  rw [cylinder_of_master (T.submaster hs)]
  apply condition_mono
  intro a ha
  exact ⟨T.submaster ha.1, ha.2⟩

theorem cylinders_disjoint {s t : List ℕ} (hlen : s.length = t.length) (hne : s ≠ t) :
    cylinder s ⊓ cylinder t = ⊥ := by
  classical
  by_cases hs : MasterNode s
  · by_cases ht : MasterNode t
    · rw [cylinder_of_master hs, cylinder_of_master ht]
      by_contra h
      exact masterCondition.restrictions_incompatible hs ht hlen hne
        ((condition_inf_ne_bot_iff _ _).1 h)
    · simp only [cylinder, dif_neg ht, inf_bot_eq]
  · simp only [cylinder, dif_neg hs, bot_inf_eq]

def levelJoin (T : Condition) (n : ℕ) : B :=
  ⨆ s : {s : List ℕ // s ∈ T.tree ∧ s.length = n}, cylinder s.1

theorem condition_le_levelJoin (T : Condition) (n : ℕ) :
    condition Condition T ≤ levelJoin T n := by
  apply le_of_dense_refinements
  intro Q hQ
  have hQT : Q ≤ T := (condition_le_iff forcing_separative Q T).1 hQ
  obtain ⟨s, hs, hlen⟩ := exists_node_at_level Q n
  refine ⟨Q.restrict s hs, Q.restrict_le s hs, ?_⟩
  exact (restrict_le_cylinder Q s hs).trans
    (le_iSup (fun s : {s : List ℕ // s ∈ T.tree ∧ s.length = n} => cylinder s.1)
      ⟨s, hQT hs, hlen⟩)

theorem cylinder_inf_levelJoin_of_not_mem (T : Condition) {s : List ℕ}
    (hs : s ∉ T.tree) : cylinder s ⊓ levelJoin T s.length = ⊥ := by
  unfold levelJoin
  rw [inf_iSup_eq (cylinder s)
    (fun t : {t : List ℕ // t ∈ T.tree ∧ t.length = s.length} => cylinder t.1)]
  apply le_bot_iff.mp
  apply iSup_le
  intro t
  have hne : s ≠ t.1 := by
    intro h
    apply hs
    simpa only [h] using t.2.1
  rw [cylinders_disjoint t.2.2.symm hne]

/-- The concrete condition is recovered from its countably many level tests. -/
theorem condition_eq_iInf_levelJoin (T : Condition) :
    condition Condition T = ⨅ n : ℕ, levelJoin T n := by
  apply le_antisymm
  · exact le_iInf (condition_le_levelJoin T)
  · apply le_of_condition_tests
    intro Q hQ
    apply condition_mono
    classical
    by_contra hnot
    have hex : ∃ s : List ℕ, s ∈ Q.tree ∧ s ∉ T.tree := by
      by_contra hn
      apply hnot
      intro s hs
      by_contra hst
      exact hn ⟨s, hs, hst⟩
    obtain ⟨s, hs, hst⟩ := hex
    let R := Q.restrict s hs
    have hRlevel : condition Condition R ≤ levelJoin T s.length :=
      (condition_mono (Q.restrict_le s hs)).trans (hQ.trans (iInf_le _ s.length))
    have hRcyl : condition Condition R ≤ cylinder s := restrict_le_cylinder Q s hs
    apply condition_ne_bot R
    apply le_bot_iff.mp
    calc
      condition Condition R ≤ cylinder s ⊓ levelJoin T s.length := le_inf hRcyl hRlevel
      _ = ⊥ := cylinder_inf_levelJoin_of_not_mem T hst

theorem completeClosed_iSup {S : Set B} (hS : CompleteClosed S)
    {I : Type*} (f : I → B) (hf : ∀ i, f i ∈ S) : (⨆ i, f i) ∈ S := by
  have h := hS.2.2 (Set.range f) (by rintro _ ⟨i, rfl⟩; exact hf i)
  simpa only [sSup_range] using h

theorem completeClosed_iInf {S : Set B} (hS : CompleteClosed S)
    {I : Type*} (f : I → B) (hf : ∀ i, f i ∈ S) : (⨅ i, f i) ∈ S := by
  have h := hS.2.1 _ (completeClosed_iSup hS (fun i => (f i)ᶜ)
    (fun i => hS.2.1 _ (hf i)))
  simpa only [compl_iSup, compl_compl] using h

/-- Every element of the actual completion is a join of condition values. -/
theorem eq_iSup_conditions (b : B) :
    b = ⨆ T : {T : Condition // condition Condition T ≤ b}, condition Condition T.1 := by
  apply le_antisymm
  · apply le_of_condition_tests
    intro T hT
    exact le_iSup
      (fun Q : {Q : Condition // condition Condition Q ≤ b} => condition Condition Q.1)
      ⟨T, hT⟩
  · exact iSup_le (fun T => T.2)

/-- Complete generation is a conclusion about the actual cylinder family. -/
theorem cylinders_completely_generate : CompletelyGenerates cylinder := by
  intro S hS hc b
  have hcondition : ∀ T : Condition, condition Condition T ∈ S := by
    intro T
    rw [condition_eq_iInf_levelJoin]
    apply completeClosed_iInf hS
    intro n
    exact completeClosed_iSup hS _ (fun s => hc s.1)
  rw [eq_iSup_conditions b]
  exact completeClosed_iSup hS _ (fun T => hcondition T.1)

/-- A fixed natural-number enumeration; failed decoding contributes bottom. -/
def generator (n : ℕ) : B :=
  match Encodable.decode (α := List ℕ) n with
  | some s => cylinder s
  | none => ⊥

theorem generator_encode (s : List ℕ) : generator (Encodable.encode s) = cylinder s := by
  simp only [generator, Encodable.encodek]

theorem generator_completely_generates : CompletelyGenerates generator := by
  intro S hS hg
  apply cylinders_completely_generate S hS
  intro s
  rw [← generator_encode s]
  exact hg _

/-- Atomlessness and complete generation now supply an actual total splitter
on the concrete Jech--Shelah completion. This is not yet a pure C term. -/
def branchSplitter : B → B :=
  splitter generator generator_completely_generates (fun _ h => forcing_completion_atomless h)

theorem branchSplitter_splits {b : B} (hb : b ≠ ⊥) :
    b ⊓ branchSplitter b ≠ ⊥ ∧ b ⊓ (branchSplitter b)ᶜ ≠ ⊥ :=
  splitter_splits generator generator_completely_generates
    (fun _ h => forcing_completion_atomless h) hb

end

end Classicism.Meta.Research.MaxAtomicityJechShelahCylinders

#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahCylinders.condition_eq_iInf_levelJoin
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahCylinders.cylinders_completely_generate
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahCylinders.generator_completely_generates
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahCylinders.branchSplitter_splits
