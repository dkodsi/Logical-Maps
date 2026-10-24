import Classicism.Results.Research.MaxAtomicitySetCodeAbsoluteness
import Classicism.Results.Research.MaxAtomicityRegularOpenCode

/-!
# The canonical coded poset has exactly the actual Boolean completion

Direct source: the regular-lower-set construction and actual set codes in this
formalization (misc, 23 October 2026, unpaginated). The finite regularity
predicate is interpreted using the actual poset coding and representation of
every subset. Its solutions are proved to be precisely the coded elements of
the already constructed Boolean algebra; no completeness premise is inserted.
This supplies the completion component of finite JSCode adequacy.
-/

namespace Classicism.Meta.Research.MaxAtomicityCanonicalCompletion

open MaxAtomicityHereditaryUniverse MaxAtomicityHereditaryGraphs
open MaxAtomicityJechShelahTrees MaxAtomicityJechShelahCylinders
open MaxAtomicityJechShelahSetCodes MaxAtomicitySetCodeAbsoluteness
open MaxAtomicityRegularOpenCode

noncomputable section

abbrev D := B → B
abbrev R := codeRelation B

def canonicalPoset : D := encode B posetCode posetCode_mem_universeSet
def canonicalOrder : D := encode B orderGraph orderGraph_mem_universe

def treeEmbedding : Condition ↪ D where
  toFun T := encode B (treeCode T) (treeCode_mem_universeSet T)
  inj' := by
    intro T S h
    apply treeCode_injective
    simpa only [present_encode] using congrArg (present B) h

theorem present_treeEmbedding (T : Condition) : present B (treeEmbedding T) = treeCode T :=
  present_encode B _ _

theorem canonical_poset_range (a : D) :
    R a canonicalPoset ↔ ∃ T : Condition, treeEmbedding T = a := by
  rw [canonicalPoset, mem_encoded, mem_posetCode]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, present_injective B ((present_treeEmbedding T).trans hT)⟩
  · rintro ⟨T, rfl⟩
    exact ⟨T, (present_treeEmbedding T).symm⟩

theorem canonical_order_iff (T S : Condition) :
    MaxAtomicitySetFormulaTools.Ordinary.GraphApp R canonicalOrder
      (treeEmbedding T) (treeEmbedding S) ↔ T ≤ S := by
  rw [graphApp_iff, present_treeEmbedding, present_treeEmbedding]
  change ZFSet.pair (treeCode T) (treeCode S) ∈
    present B (encode B orderGraph orderGraph_mem_universe) ↔ _
  rw [present_encode, mem_orderGraph]

def posetCoding : PosetCoding D Condition R canonicalPoset canonicalOrder where
  point := treeEmbedding
  mem_carrier := canonical_poset_range
  order_iff := canonical_order_iff

/-- Explicit subset codes establish the full representation hypothesis. -/
theorem subset_represented (S : Set Condition) :
    posetCoding.Represents S (encode B (subsetPosetCode S) (subsetPosetCode_mem_universe S)) := by
  intro d
  change present B d ∈ present B (encode B (subsetPosetCode S)
    (subsetPosetCode_mem_universe S)) ↔ ∃ T, treeEmbedding T = d ∧ T ∈ S
  rw [present_encode, subsetPosetCode, ZFSet.mem_range]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T.val, present_injective B ((present_treeEmbedding T.val).trans hT), T.property⟩
  · rintro ⟨T, hT, hTS⟩
    exact ⟨⟨T, hTS⟩, (present_treeEmbedding T).symm.trans (congrArg (present B) hT)⟩

theorem posetCoding_full : posetCoding.Full :=
  fun S => ⟨encode B (subsetPosetCode S) (subsetPosetCode_mem_universe S), subset_represented S⟩

theorem carrier_represents (b : B) :
    posetCoding.Represents (((b : LowerSet Condition) : Set Condition)) (carrierEmbedding b) := by
  intro d
  change present B d ∈ present B (carrierEmbedding b) ↔
    ∃ T, treeEmbedding T = d ∧ T ∈ (b : LowerSet Condition)
  rw [present_carrierEmbedding, codeOpen, ZFSet.mem_range]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T.val, present_injective B ((present_treeEmbedding T.val).trans hT), T.property⟩
  · rintro ⟨T, hT, hTb⟩
    exact ⟨⟨T, hTb⟩, (present_treeEmbedding T).symm.trans (congrArg (present B) hT)⟩

/-- Every solution of the finite regularity formula is the code of an actual
regular lower set, and every actual regular lower set satisfies the formula. -/
theorem regular_iff_carrier (X : D) :
    Ordinary.Regular R canonicalPoset canonicalOrder X ↔ ∃ b : B, carrierEmbedding b = X := by
  constructor
  · intro hX
    let b : B := posetCoding.decodeRegular posetCoding_full ⟨X, hX⟩
    have hrep : posetCoding.Represents (((b : LowerSet Condition) : Set Condition)) X :=
      posetCoding.represents_decoded hX.1.1
    refine ⟨b, codeRelation_extensional B _ _ ?_⟩
    intro d
    exact (carrier_represents b d).trans (hrep d).symm
  · rintro ⟨b, rfl⟩
    exact (posetCoding.regular_iff posetCoding_full (carrier_represents b)).2 b.property

theorem canonical_algebraCarrier :
    Ordinary.AlgebraCarrier R canonicalPoset canonicalOrder canonicalCarrier := by
  intro X
  exact (canonical_carrier_range X).trans (regular_iff_carrier X).symm

theorem algebraCarrier_unique (c : D)
    (hc : Ordinary.AlgebraCarrier R canonicalPoset canonicalOrder c) :
    c = canonicalCarrier := by
  apply codeRelation_extensional B
  intro X
  exact (hc X).trans (canonical_algebraCarrier X).symm

end

end Classicism.Meta.Research.MaxAtomicityCanonicalCompletion

#print axioms Classicism.Meta.Research.MaxAtomicityCanonicalCompletion.posetCoding
#print axioms Classicism.Meta.Research.MaxAtomicityCanonicalCompletion.posetCoding_full
#print axioms Classicism.Meta.Research.MaxAtomicityCanonicalCompletion.regular_iff_carrier
#print axioms Classicism.Meta.Research.MaxAtomicityCanonicalCompletion.canonical_algebraCarrier
#print axioms Classicism.Meta.Research.MaxAtomicityCanonicalCompletion.algebraCarrier_unique
