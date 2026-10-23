import Classicism.Results.Research.MaxAtomicityJechShelahEnumeration
import Classicism.Results.Research.MaxAtomicityJechShelahCylinders

/-!
# Canonical master-index generators

The generator numbered n is the cylinder of the unique master node whose
actual breadth-first index is n. This uses the proved index equivalence and
does not depend on an implementation of Encodable for finite lists. Complete
generation follows from the already proved cylinder theorem.

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 749--750,
definition (3) and the branch generators; the explicit reindexing proof is
original formalization work (misc, 23 October 2026). Pure definability is a
separate obligation. Compilation belongs to the designated serial checker.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahIndexedGenerators

open MaxAtomicityJechShelahTrees MaxAtomicityJechShelahEnumeration
open MaxAtomicityJechShelahCylinders MaxAtomicityCountableGenerator

noncomputable section

def indexedNode (n : ℕ) : List ℕ := (masterIndexEquiv.symm n).val

theorem indexedNode_master (n : ℕ) : MasterNode (indexedNode n) :=
  (masterIndexEquiv.symm n).prop

theorem indexedNode_index (n : ℕ) : index (indexedNode n) = n :=
  masterIndexEquiv.apply_symm_apply n

theorem indexedNode_of_master (s : List ℕ) (hs : MasterNode s) :
    indexedNode (index s) = s :=
  index_injective _ _ (indexedNode_master _) hs (indexedNode_index _)

def indexedGenerator (n : ℕ) : B := cylinder (indexedNode n)

theorem indexedGenerator_index (s : List ℕ) (hs : MasterNode s) :
    indexedGenerator (index s) = cylinder s := by
  unfold indexedGenerator
  rw [indexedNode_of_master s hs]

theorem indexedGenerator_completely_generates :
    CompletelyGenerates indexedGenerator := by
  intro S hS hg
  apply cylinders_completely_generate S hS
  intro s
  by_cases hs : MasterNode s
  · rw [← indexedGenerator_index s hs]
    exact hg _
  · simpa only [cylinder, dif_neg hs] using hS.1

def indexedSplitter : B → B :=
  splitter indexedGenerator indexedGenerator_completely_generates
    (fun _ h => forcing_completion_atomless h)

theorem indexedSplitter_splits {b : B} (hb : b ≠ ⊥) :
    b ⊓ indexedSplitter b ≠ ⊥ ∧ b ⊓ (indexedSplitter b)ᶜ ≠ ⊥ :=
  splitter_splits indexedGenerator indexedGenerator_completely_generates
    (fun _ h => forcing_completion_atomless h) hb

#print axioms indexedNode_index
#print axioms indexedGenerator_completely_generates
#print axioms indexedSplitter_splits

end

end Classicism.Meta.Research.MaxAtomicityJechShelahIndexedGenerators
