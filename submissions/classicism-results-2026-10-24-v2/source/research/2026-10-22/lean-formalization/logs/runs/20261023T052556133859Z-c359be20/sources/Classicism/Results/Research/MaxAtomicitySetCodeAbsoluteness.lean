import Classicism.Results.Research.MaxAtomicityHereditaryGraphs
import Classicism.Results.Research.MaxAtomicityPureSelector

/-!
# Finite set-code absoluteness and the canonical selector presentation

The inverse presentation map is constructed explicitly. Transitivity of the
hereditary universe makes all elements of a represented set available to the
finite formulas. Pair closure supplies the actual singleton, unordered-pair,
and Kuratowski-pair witnesses. Thus graph application is absolute, rather than
assumed to have its intended meaning.

The second part constructs the exact `Presentation` record required by the
finite pure selector, for the actual canonical algebra, naturals, and cylinder
graph. It does not assert that the separate finite JSCode formula holds or
that arbitrary JSCode witnesses have these canonical values.

Original proof/transcription: misc, 23 October 2026. No compiler is invoked by
this module's author; the designated serial checker owns verification.
-/

namespace Classicism.Meta.Research.MaxAtomicitySetCodeAbsoluteness

open MaxAtomicityHereditaryCover MaxAtomicityHereditaryUniverse
open MaxAtomicityHereditaryGraphs MaxAtomicitySetFormulaTools
open MaxAtomicityJechShelahSetCodes MaxAtomicityJechShelahIndexedGenerators
open MaxAtomicityJechShelahCylinders MaxAtomicityPureSelector

noncomputable section

variable (K : Type) [Infinite K]

/-- A definite inverse, with proof-irrelevant membership evidence. -/
def encode (z : ZFSet) (hz : z ∈ universeSet K) : K → K :=
  (presentationEquiv K).symm ⟨z, hz⟩

@[simp] theorem present_encode (z : ZFSet) (hz : z ∈ universeSet K) :
    present K (encode K z hz) = z :=
  congrArg Subtype.val ((presentationEquiv K).apply_symm_apply ⟨z, hz⟩)

@[simp] theorem encode_present (a : K → K) :
    encode K (present K a) (present_mem K a) = a :=
  (presentationEquiv K).symm_apply_apply a

theorem equal_iff (a b : K → K) : a = b ↔ present K a = present K b :=
  ⟨congrArg (present K), present_injective K⟩

@[simp] theorem mem_encoded (a : K → K) (z : ZFSet) (hz : z ∈ universeSet K) :
    codeRelation K a (encode K z hz) ↔ present K a ∈ z := by
  change present K a ∈ present K (encode K z hz) ↔ _
  rw [present_encode]

@[simp] theorem encoded_mem (z : ZFSet) (hz : z ∈ universeSet K) (a : K → K) :
    codeRelation K (encode K z hz) a ↔ z ∈ present K a := by
  change present K (encode K z hz) ∈ present K a ↔ _
  rw [present_encode]

/-- Every quantifier in a subset formula sees every actual member of its left
set. This is the exact use of transitivity in subset absoluteness. -/
theorem subset_iff (a b : K → K) :
    Ordinary.Subset (codeRelation K) a b ↔ present K a ⊆ present K b := by
  constructor
  · intro h z hz
    have hzH := universeSet_transitive K _ (present_mem K a) z hz
    exact (encoded_mem K z hzH b).1 (h (encode K z hzH) ((encoded_mem K z hzH a).2 hz))
  · intro h d hd
    exact h hd

theorem empty_iff (a : K → K) :
    Ordinary.Empty (codeRelation K) a ↔ present K a = ∅ := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      have hzH := universeSet_transitive K _ (present_mem K a) z hz
      exact (h (encode K z hzH) ((encoded_mem K z hzH a).2 hz)).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim
  · intro h d hd
    change present K d ∈ present K a at hd
    rw [h] at hd
    exact ZFSet.notMem_empty _ hd

/-- Equality of a represented row with any set that actually belongs to H. -/
theorem row_iff_eq (a : K → K) (z : ZFSet) (hzH : z ∈ universeSet K) :
    (∀ d : K → K, codeRelation K d a ↔ present K d ∈ z) ↔ present K a = z := by
  constructor
  · intro h
    have heq : a = encode K z hzH := codeRelation_extensional K a (encode K z hzH)
      (fun d => (h d).trans (mem_encoded K d z hzH).symm)
    exact (congrArg (present K) heq).trans (present_encode K z hzH)
  · intro h d
    change present K d ∈ present K a ↔ present K d ∈ z
    rw [h]

theorem singleton_iff (a s : K → K) :
    Ordinary.Singleton (codeRelation K) a s ↔ present K s = ({present K a} : ZFSet) := by
  have hmem : ({present K a} : ZFSet) ∈ universeSet K :=
    (mem_universeSet K _).2 (hereditary_singleton K (present_hereditary K a))
  rw [← row_iff_eq K s _ hmem]
  apply forall_congr'
  intro d
  rw [ZFSet.mem_singleton, ← equal_iff K d a]
  rfl

theorem unorderedPair_iff (a b p : K → K) :
    Ordinary.UnorderedPair (codeRelation K) a b p ↔
      present K p = ({present K a, present K b} : ZFSet) := by
  have hmem : ({present K a, present K b} : ZFSet) ∈ universeSet K :=
    (mem_universeSet K _).2
      (hereditary_unorderedPair K (present_hereditary K a) (present_hereditary K b))
  rw [← row_iff_eq K p _ hmem]
  apply forall_congr'
  intro d
  rw [ZFSet.mem_pair, ← equal_iff K d a, ← equal_iff K d b]
  rfl

theorem orderedPair_iff (a b p : K → K) :
    Ordinary.OrderedPair (codeRelation K) a b p ↔
      present K p = ZFSet.pair (present K a) (present K b) := by
  constructor
  · rintro ⟨s, t, hs, ht, hp⟩
    rw [singleton_iff] at hs
    rw [unorderedPair_iff] at ht hp
    simpa only [hs, ht, ZFSet.pair] using hp
  · intro hp
    have hsH : ({present K a} : ZFSet) ∈ universeSet K :=
      (mem_universeSet K _).2 (hereditary_singleton K (present_hereditary K a))
    have htH : ({present K a, present K b} : ZFSet) ∈ universeSet K :=
      (mem_universeSet K _).2
        (hereditary_unorderedPair K (present_hereditary K a) (present_hereditary K b))
    refine ⟨encode K _ hsH, encode K _ htH, ?_, ?_, ?_⟩
    · exact (singleton_iff K _ _).2 (present_encode K _ _)
    · exact (unorderedPair_iff K _ _ _).2 (present_encode K _ _)
    · apply (unorderedPair_iff K _ _ _).2
      simpa only [present_encode, ZFSet.pair] using hp

/-- Quantification over ordered-pair codes is equivalent to literal
Kuratowski-pair membership; the required pair code is constructed in H. -/
theorem graphApp_iff (f a b : K → K) :
    Ordinary.GraphApp (codeRelation K) f a b ↔
      ZFSet.pair (present K a) (present K b) ∈ present K f := by
  constructor
  · rintro ⟨p, hp, hf⟩
    change present K p ∈ present K f at hf
    simpa only [(orderedPair_iff K a b p).1 hp] using hf
  · intro h
    have hpH : ZFSet.pair (present K a) (present K b) ∈ universeSet K :=
      (mem_universeSet K _).2
        (hereditary_pair K (present_hereditary K a) (present_hereditary K b))
    refine ⟨encode K _ hpH, (orderedPair_iff K _ _ _).2 (present_encode K _ _), ?_⟩
    exact (encoded_mem K _ hpH f).2 h

section Canonical

/-- The concrete c,w,G arguments, now in the actual object-type domain B→B. -/
def canonicalCarrier : B → B := encode B algebraCode algebraCode_mem_universeSet
def canonicalNaturals : B → B := encode B naturalsCode naturalsCode_mem_universeSet
def canonicalGraph : B → B := encode B generatorGraph generatorGraph_mem_universe

def carrierEmbedding : B ↪ (B → B) where
  toFun b := encode B (codeOpen b) (codeOpen_mem_universeSet b)
  inj' := by
    intro b c h
    apply codeOpen_injective
    simpa only [present_encode] using congrArg (present B) h

def naturalEmbedding : ℕ ↪ (B → B) where
  toFun n := encode B (natural n) (natural_mem_universeSet n)
  inj' := by
    intro m n h
    apply natural_injective
    simpa only [present_encode] using congrArg (present B) h

@[simp] theorem present_carrierEmbedding (b : B) :
    present B (carrierEmbedding b) = codeOpen b := present_encode B _ _

@[simp] theorem present_naturalEmbedding (n : ℕ) :
    present B (naturalEmbedding n) = natural n := present_encode B _ _

theorem canonical_carrier_range (a : B → B) :
    codeRelation B a canonicalCarrier ↔ ∃ b : B, carrierEmbedding b = a := by
  rw [canonicalCarrier, mem_encoded, mem_algebraCode]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, present_injective B ?_⟩
    exact (present_carrierEmbedding b).trans hb
  · rintro ⟨b, rfl⟩
    exact ⟨b, (present_carrierEmbedding b).symm⟩

theorem canonical_number_range (a : B → B) :
    codeRelation B a canonicalNaturals ↔ ∃ n : ℕ, naturalEmbedding n = a := by
  rw [canonicalNaturals, mem_encoded, mem_naturalsCode]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, present_injective B ((present_naturalEmbedding n).trans hn)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, (present_naturalEmbedding n).symm⟩

theorem canonical_predecessor (n : ℕ) (a : B → B) :
    codeRelation B a (naturalEmbedding n) ↔ ∃ j, j < n ∧ naturalEmbedding j = a := by
  change present B a ∈ present B (naturalEmbedding n) ↔ _
  rw [present_naturalEmbedding, mem_natural]
  constructor
  · rintro ⟨j, hj, hja⟩
    exact ⟨j, hj, present_injective B ((present_naturalEmbedding j).trans hja)⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (present_naturalEmbedding j).symm⟩

theorem canonical_graph (n : ℕ) (a : B → B) :
    Ordinary.GraphApp (codeRelation B) canonicalGraph (naturalEmbedding n) a ↔
      a = carrierEmbedding (indexedGenerator n) := by
  rw [graphApp_iff, present_naturalEmbedding]
  change ZFSet.pair (natural n) (present B a) ∈
    present B (encode B generatorGraph generatorGraph_mem_universe) ↔ _
  rw [present_encode, generatorGraph, mem_graphOf]
  constructor
  · rintro ⟨m, hmn, hma⟩
    have hmn' : m = n := natural_injective hmn
    subst m
    apply present_injective B
    exact hma.symm.trans (present_carrierEmbedding _).symm
  · intro h
    exact ⟨n, rfl, by rw [h, present_carrierEmbedding]⟩

/-- Every field of selector presentation is derived from the actual ZFSet
codes. There is no formula-adequacy premise in this construction. -/
def canonicalPresentation : Presentation (codeRelation B)
    canonicalCarrier canonicalNaturals canonicalGraph indexedGenerator where
  carrier := carrierEmbedding
  carrier_range := canonical_carrier_range
  carrier_order := fun b c => by
    rw [subset_iff, present_carrierEmbedding, present_carrierEmbedding]
    exact codeOpen_subset_iff b c
  number := naturalEmbedding
  number_range := canonical_number_range
  predecessor := canonical_predecessor
  graph := canonical_graph

end Canonical

#print axioms present_encode
#print axioms subset_iff
#print axioms singleton_iff
#print axioms unorderedPair_iff
#print axioms orderedPair_iff
#print axioms graphApp_iff
#print axioms canonicalPresentation

end

end Classicism.Meta.Research.MaxAtomicitySetCodeAbsoluteness
