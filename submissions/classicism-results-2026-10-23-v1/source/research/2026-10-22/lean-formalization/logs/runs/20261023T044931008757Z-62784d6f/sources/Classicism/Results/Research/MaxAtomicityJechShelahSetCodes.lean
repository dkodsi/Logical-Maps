import Classicism.Results.Research.MaxAtomicityConcreteModel
import Classicism.Results.Research.MaxAtomicityJechShelahEnumeration
import Classicism.Results.Research.MaxAtomicityJechShelahRigidityCriterion

/-!
# Actual hereditary-small codes for the JS poset and its completion

Direct source: the explicit JS tree and regular-lower-set construction in the
local formalization (misc, 23 October 2026, unpaginated). The natural-number
codes are the Mostowski collapse of ordinary strict order on Nat, so they do
not depend on a selected well-order or on any new ordinal library.

All objects below are actual ZFSet values. Their size bounds use actual
embeddings: Nat into an infinite carrier, tree conditions into their separative
Boolean completion, subsets into their underlying carrier, and B into itself.
The concrete model supplies Infinite B; no cardinality bound is postulated.

This proves coding, injectivity, order preservation/reflection, and membership
in the constructed hereditary universe. It does not claim that a finite
first-order JSCode formula has yet been proved to characterize these objects.
The designated serial checker owns compilation and axiom inspection.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes

open MaxAtomicityMostowski MaxAtomicityHereditaryCover MaxAtomicityHereditaryUniverse
open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahEnumeration MaxAtomicityJechShelahCylinders
open MaxAtomicityJechShelahRigidityCriterion

noncomputable section

/-- The canonical finite von Neumann ordinals, constructed by collapse. -/
def natural (n : ℕ) : ZFSet := collapse Nat.lt_wfRel.wf n

theorem natural_injective : Function.Injective natural :=
  collapse_injective Nat.lt_wfRel.wf (wellOrder_extensional (fun m n : ℕ => m < n))

theorem mem_natural (n : ℕ) (z : ZFSet) :
    z ∈ natural n ↔ ∃ m : ℕ, m < n ∧ natural m = z :=
  mem_collapse Nat.lt_wfRel.wf n z

theorem natural_mem_natural (m n : ℕ) : natural m ∈ natural n ↔ m < n :=
  collapse_mem_iff Nat.lt_wfRel.wf
    (wellOrder_extensional (fun m n : ℕ => m < n)) m n

theorem natural_zero : natural 0 = ∅ := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨m, hm, _⟩ := (mem_natural 0 z).1 hz
    exact False.elim (Nat.not_lt_zero m hm)
  · intro hz
    exact False.elim (ZFSet.notMem_empty z hz)

theorem natural_succ (n : ℕ) : natural (n + 1) = insert (natural n) (natural n) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_insert_iff]
  constructor
  · intro hz
    obtain ⟨m, hm, hmz⟩ := (mem_natural (n + 1) z).1 hz
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hlt | heq
    · exact Or.inr ((mem_natural n z).2 ⟨m, hlt, hmz⟩)
    · exact Or.inl (hmz.symm.trans (congrArg natural heq))
  · intro hz
    rcases hz with hz | hz
    · exact (mem_natural (n + 1) z).2 ⟨n, Nat.lt_succ_self n, hz.symm⟩
    · obtain ⟨m, hm, hmz⟩ := (mem_natural n z).1 hz
      exact (mem_natural (n + 1) z).2 ⟨m, Nat.lt.step hm, hmz⟩

theorem natural_hereditary (K : Type) [Infinite K] (n : ℕ) :
    HereditarilySmall K (natural n) := by
  apply collapse_hereditarilySmall K Nat.lt_wfRel.wf
    (wellOrder_extensional (fun m n : ℕ => m < n))
  intro m
  exact ⟨(Function.Embedding.subtype (fun i : ℕ => i < m)).trans
    (Infinite.natEmbedding K)⟩

def naturalsCode : ZFSet := ZFSet.range natural

theorem mem_naturalsCode (z : ZFSet) : z ∈ naturalsCode ↔ ∃ n, natural n = z :=
  ZFSet.mem_range

theorem natural_mem_naturalsCode (n : ℕ) : natural n ∈ naturalsCode :=
  (mem_naturalsCode _).2 ⟨n, rfl⟩

theorem naturalsCode_hereditary (K : Type) [Infinite K] :
    HereditarilySmall K naturalsCode :=
  hereditary_range K (Infinite.natEmbedding K) natural (natural_hereditary K)

/-- A real is represented by exactly the natural-number codes it contains. -/
def realCode (A : Set ℕ) : ZFSet := ZFSet.range (fun i : A => natural i.val)

theorem mem_realCode (A : Set ℕ) (n : ℕ) : natural n ∈ realCode A ↔ n ∈ A := by
  change natural n ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact natural_injective hi ▸ i.property
  · intro hn
    exact ⟨⟨n, hn⟩, rfl⟩

theorem realCode_subset_iff (A C : Set ℕ) : realCode A ⊆ realCode C ↔ A ⊆ C := by
  constructor
  · intro h n hn
    exact (mem_realCode C n).1 (h ((mem_realCode A n).2 hn))
  · intro h z hz
    obtain ⟨i, hi⟩ := ZFSet.mem_range.mp hz
    rw [← hi]
    exact (mem_realCode C i.val).2 (h i.property)

theorem realCode_injective : Function.Injective realCode := by
  intro A C h
  apply Set.ext
  intro n
  rw [← mem_realCode A n, h, mem_realCode C n]

theorem realCode_subset_naturalsCode (A : Set ℕ) : realCode A ⊆ naturalsCode := by
  intro z hz
  obtain ⟨i, hi⟩ := ZFSet.mem_range.mp hz
  exact hi ▸ natural_mem_naturalsCode i.val

theorem realCode_hereditary (K : Type) [Infinite K] (A : Set ℕ) :
    HereditarilySmall K (realCode A) :=
  hereditary_range K ((Function.Embedding.subtype A).trans (Infinite.natEmbedding K))
    (fun i : A => natural i.val) (fun i => natural_hereditary K i.val)

theorem nodeIndices_order_iff (T S : Condition) : nodeIndices T ⊆ nodeIndices S ↔ T ≤ S := by
  constructor
  · intro h s hs
    obtain ⟨t, ht, hts⟩ := h ⟨s, hs, rfl⟩
    have hts' : t = s := index_injective t s (S.submaster ht) (T.submaster hs) hts
    exact hts' ▸ ht
  · intro h k hk
    obtain ⟨s, hs, hsk⟩ := hk
    exact ⟨s, h hs, hsk⟩

def treeCode (T : Condition) : ZFSet := realCode (nodeIndices T)

theorem treeCode_subset_iff (T S : Condition) : treeCode T ⊆ treeCode S ↔ T ≤ S :=
  (realCode_subset_iff (nodeIndices T) (nodeIndices S)).trans (nodeIndices_order_iff T S)

theorem treeCode_injective : Function.Injective treeCode := by
  intro T S h
  apply le_antisymm
  · apply (treeCode_subset_iff T S).1
    intro z hz
    rw [← h]
    exact hz
  · apply (treeCode_subset_iff S T).1
    intro z hz
    rw [h]
    exact hz

theorem treeCode_hereditary (T : Condition) : HereditarilySmall B (treeCode T) :=
  realCode_hereditary B (nodeIndices T)

/-- Separativity gives the needed actual injection of conditions into B. -/
def conditionEmbedding : Condition ↪ B where
  toFun := condition Condition
  inj' := by
    intro T S h
    exact le_antisymm
      ((condition_le_iff forcing_separative T S).1 h.le)
      ((condition_le_iff forcing_separative S T).1 h.ge)

def posetCode : ZFSet := ZFSet.range treeCode

theorem mem_posetCode (z : ZFSet) : z ∈ posetCode ↔ ∃ T : Condition, treeCode T = z :=
  ZFSet.mem_range

theorem treeCode_mem_posetCode (T : Condition) : treeCode T ∈ posetCode :=
  (mem_posetCode _).2 ⟨T, rfl⟩

theorem posetCode_hereditary : HereditarilySmall B posetCode :=
  hereditary_range B conditionEmbedding treeCode treeCode_hereditary

/-- The code of an actual regular lower set is the set of its condition codes. -/
def codeOpen (b : B) : ZFSet :=
  ZFSet.range (fun T : {T : Condition // T ∈ (b : LowerSet Condition)} => treeCode T.val)

theorem mem_codeOpen (b : B) (T : Condition) :
    treeCode T ∈ codeOpen b ↔ T ∈ (b : LowerSet Condition) := by
  change treeCode T ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨S, hS⟩
    exact treeCode_injective hS ▸ S.property
  · intro hT
    exact ⟨⟨T, hT⟩, rfl⟩

theorem codeOpen_subset_posetCode (b : B) : codeOpen b ⊆ posetCode := by
  intro z hz
  obtain ⟨T, hT⟩ := ZFSet.mem_range.mp hz
  exact hT ▸ treeCode_mem_posetCode T.val

theorem codeOpen_subset_iff (b c : B) : codeOpen b ⊆ codeOpen c ↔ b ≤ c := by
  constructor
  · intro h T hT
    exact (mem_codeOpen c T).1 (h ((mem_codeOpen b T).2 hT))
  · intro h z hz
    obtain ⟨T, hT⟩ := ZFSet.mem_range.mp hz
    rw [← hT]
    exact (mem_codeOpen c T.val).2 (h T.property)

theorem codeOpen_injective : Function.Injective codeOpen := by
  intro b c h
  apply Heyting.Regular.coe_injective
  apply LowerSet.ext
  apply Set.ext
  intro T
  rw [← mem_codeOpen b T, h, mem_codeOpen c T]

theorem codeOpen_hereditary (b : B) : HereditarilySmall B (codeOpen b) :=
  hereditary_range B
    ((Function.Embedding.subtype (fun T : Condition => T ∈ (b : LowerSet Condition))).trans
      conditionEmbedding)
    (fun T : {T : Condition // T ∈ (b : LowerSet Condition)} => treeCode T.val)
    (fun T => treeCode_hereditary T.val)

def algebraCode : ZFSet := ZFSet.range codeOpen

theorem mem_algebraCode (z : ZFSet) : z ∈ algebraCode ↔ ∃ b : B, codeOpen b = z :=
  ZFSet.mem_range

theorem codeOpen_mem_algebraCode (b : B) : codeOpen b ∈ algebraCode :=
  (mem_algebraCode _).2 ⟨b, rfl⟩

theorem algebraCode_hereditary : HereditarilySmall B algebraCode :=
  hereditary_range B (Function.Embedding.refl B) codeOpen codeOpen_hereditary

theorem natural_mem_universeSet (n : ℕ) : natural n ∈ universeSet B :=
  (mem_universeSet B _).2 (natural_hereditary B n)

theorem naturalsCode_mem_universeSet : naturalsCode ∈ universeSet B :=
  (mem_universeSet B _).2 (naturalsCode_hereditary B)

theorem realCode_mem_universeSet (A : Set ℕ) : realCode A ∈ universeSet B :=
  (mem_universeSet B _).2 (realCode_hereditary B A)

theorem treeCode_mem_universeSet (T : Condition) : treeCode T ∈ universeSet B :=
  (mem_universeSet B _).2 (treeCode_hereditary T)

theorem posetCode_mem_universeSet : posetCode ∈ universeSet B :=
  (mem_universeSet B _).2 posetCode_hereditary

theorem codeOpen_mem_universeSet (b : B) : codeOpen b ∈ universeSet B :=
  (mem_universeSet B _).2 (codeOpen_hereditary b)

theorem algebraCode_mem_universeSet : algebraCode ∈ universeSet B :=
  (mem_universeSet B _).2 algebraCode_hereditary

end

end Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes

#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.natural_injective
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.natural_mem_natural
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.natural_hereditary
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.realCode_injective
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.treeCode_subset_iff
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.conditionEmbedding
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.posetCode_hereditary
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.codeOpen_injective
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.algebraCode_hereditary
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahSetCodes.algebraCode_mem_universeSet
