import Classicism.Results.Research.MaxAtomicityJechShelahSetCodes
import Classicism.Results.Research.MaxAtomicityJechShelahIndexedGenerators

/-!
# Concrete small graphs inside the hereditary universe

Direct source: the finite coding construction in this formalization (misc,
23 October 2026, unpaginated). Finite pairing and small indexed ranges give
actual graph sets. The order graph uses an actual injection of Condition²
into the infinite Boolean carrier; no graph-existence hypothesis is assumed.
These are set-coding proofs, not yet finite formula adequacy certificates.
-/

namespace Classicism.Meta.Research.MaxAtomicityHereditaryGraphs

open MaxAtomicityHereditaryCover MaxAtomicityHereditaryUniverse
open MaxAtomicityJechShelahTrees MaxAtomicityJechShelahCylinders
open MaxAtomicityJechShelahSetCodes MaxAtomicityJechShelahIndexedGenerators

noncomputable section

variable (K : Type) [Infinite K]

private def boolIntoNat : Bool ↪ ℕ where
  toFun b := if b then 1 else 0
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

theorem hereditary_unorderedPair {x y : ZFSet}
    (hx : HereditarilySmall K x) (hy : HereditarilySmall K y) :
    HereditarilySmall K ({x, y} : ZFSet) := by
  let f : Bool → ZFSet := fun b => if b then x else y
  have hf : ∀ b, HereditarilySmall K (f b) := by
    intro b; cases b
    · exact hy
    · exact hx
  have heq : ZFSet.range f = ({x, y} : ZFSet) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range, ZFSet.mem_pair]
    constructor
    · rintro ⟨b, hb⟩
      cases b
      · exact Or.inr hb.symm
      · exact Or.inl hb.symm
    · rintro (rfl | rfl)
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
  rw [← heq]
  exact hereditary_range K (boolIntoNat.trans (Infinite.natEmbedding K)) f hf

theorem hereditary_singleton {x : ZFSet} (hx : HereditarilySmall K x) :
    HereditarilySmall K ({x} : ZFSet) := by
  simpa only [ZFSet.pair_eq_singleton] using hereditary_unorderedPair K hx hx

theorem hereditary_pair {x y : ZFSet}
    (hx : HereditarilySmall K x) (hy : HereditarilySmall K y) :
    HereditarilySmall K (ZFSet.pair x y) :=
  hereditary_unorderedPair K (hereditary_singleton K hx)
    (hereditary_unorderedPair K hx hy)

/-- The cardinal identity supplies a real embedding of pairs, used only in
external size calculations. -/
def productEmbedding : (K × K) ↪ K := by
  apply Classical.choice
  apply (Cardinal.le_def (K × K) K).mp
  simpa only [Cardinal.mk_prod, Cardinal.lift_id,
    Cardinal.mul_eq_self (Cardinal.aleph0_le_mk K)] using
    (le_rfl : Cardinal.mk K ≤ Cardinal.mk K)

def graphOf {A : Type} (f g : A → ZFSet) : ZFSet :=
  ZFSet.range (fun a => ZFSet.pair (f a) (g a))

theorem mem_graphOf {A : Type} (f g : A → ZFSet) (x y : ZFSet) :
    ZFSet.pair x y ∈ graphOf f g ↔ ∃ a, f a = x ∧ g a = y := by
  rw [graphOf, ZFSet.mem_range]
  exact exists_congr (fun a => ZFSet.pair_inj)

theorem graphOf_hereditary {A : Type} (e : A ↪ K) (f g : A → ZFSet)
    (hf : ∀ a, HereditarilySmall K (f a))
    (hg : ∀ a, HereditarilySmall K (g a)) :
    HereditarilySmall K (graphOf f g) :=
  hereditary_range K e _ (fun a => hereditary_pair K (hf a) (hg a))

/-- Every subset of the forcing has a code in H, even though its full power
set need not be an element of H. -/
def subsetPosetCode (S : Set Condition) : ZFSet :=
  ZFSet.range (fun T : S => treeCode T.val)

theorem mem_subsetPosetCode (S : Set Condition) (T : Condition) :
    treeCode T ∈ subsetPosetCode S ↔ T ∈ S := by
  rw [subsetPosetCode, ZFSet.mem_range]
  constructor
  · rintro ⟨Q, hQ⟩
    exact treeCode_injective hQ ▸ Q.property
  · intro hT
    exact ⟨⟨T, hT⟩, rfl⟩

theorem subsetPosetCode_subset (S : Set Condition) : subsetPosetCode S ⊆ posetCode := by
  intro z hz
  obtain ⟨T, hT⟩ := ZFSet.mem_range.mp hz
  exact hT ▸ treeCode_mem_posetCode T.val

theorem subsetPosetCode_hereditary (S : Set Condition) :
    HereditarilySmall B (subsetPosetCode S) :=
  hereditary_range B ((Function.Embedding.subtype S).trans conditionEmbedding)
    (fun T : S => treeCode T.val) (fun T => treeCode_hereditary T.val)

def conditionPairsEmbedding : (Condition × Condition) ↪ B :=
  (conditionEmbedding.prodMap conditionEmbedding).trans (productEmbedding B)

/-- Actual graph of the forcing order, with orientation strengthening ≤ weaker. -/
def orderGraph : ZFSet :=
  graphOf
    (fun p : {p : Condition × Condition // p.1 ≤ p.2} => treeCode p.val.1)
    (fun p : {p : Condition × Condition // p.1 ≤ p.2} => treeCode p.val.2)

theorem mem_orderGraph (T S : Condition) :
    ZFSet.pair (treeCode T) (treeCode S) ∈ orderGraph ↔ T ≤ S := by
  rw [orderGraph, mem_graphOf]
  constructor
  · rintro ⟨p, hp, hq⟩
    have hT := treeCode_injective hp
    have hS := treeCode_injective hq
    simpa only [hT, hS] using p.property
  · intro h
    exact ⟨⟨(T, S), h⟩, rfl, rfl⟩

theorem orderGraph_hereditary : HereditarilySmall B orderGraph :=
  graphOf_hereditary B
    ((Function.Embedding.subtype (fun p : Condition × Condition => p.1 ≤ p.2)).trans
      conditionPairsEmbedding)
    _ _ (fun p => treeCode_hereditary p.val.1) (fun p => treeCode_hereditary p.val.2)

/-- Actual graph of the canonical breadth-first cylinder generators. -/
def generatorGraph : ZFSet := graphOf natural (fun n => codeOpen (indexedGenerator n))

theorem mem_generatorGraph (n : ℕ) (b : B) :
    ZFSet.pair (natural n) (codeOpen b) ∈ generatorGraph ↔ indexedGenerator n = b := by
  rw [generatorGraph, mem_graphOf]
  constructor
  · rintro ⟨m, hmn, hmb⟩
    have hmn' := natural_injective hmn
    exact hmn' ▸ codeOpen_injective hmb
  · intro h
    exact ⟨n, rfl, congrArg codeOpen h⟩

theorem generatorGraph_hereditary : HereditarilySmall B generatorGraph :=
  graphOf_hereditary B (Infinite.natEmbedding B) _ _
    (natural_hereditary B) (fun n => codeOpen_hereditary (indexedGenerator n))

/-- All unary natural-number recursions have concrete small graph codes. -/
def natGraph (f : ℕ → ℕ) : ZFSet := graphOf natural (fun n => natural (f n))

theorem natGraph_hereditary (f : ℕ → ℕ) : HereditarilySmall B (natGraph f) :=
  graphOf_hereditary B (Infinite.natEmbedding B) _ _
    (natural_hereditary B) (fun n => natural_hereditary B (f n))

theorem mem_natGraph (f : ℕ → ℕ) (m n : ℕ) :
    ZFSet.pair (natural m) (natural n) ∈ natGraph f ↔ f m = n := by
  rw [natGraph, mem_graphOf]
  constructor
  · rintro ⟨k, hkm, hfn⟩
    exact natural_injective hkm ▸ natural_injective hfn
  · intro h
    exact ⟨m, rfl, congrArg natural h⟩

def natPairsIntoB : (ℕ × ℕ) ↪ B :=
  (productEmbedding ℕ).trans (Infinite.natEmbedding B)

def natBinaryGraph (f : ℕ → ℕ → ℕ) : ZFSet :=
  graphOf (fun p : ℕ × ℕ => ZFSet.pair (natural p.1) (natural p.2))
    (fun p => natural (f p.1 p.2))

theorem natBinaryGraph_hereditary (f : ℕ → ℕ → ℕ) :
    HereditarilySmall B (natBinaryGraph f) :=
  graphOf_hereditary B natPairsIntoB _ _
    (fun p => hereditary_pair B (natural_hereditary B p.1) (natural_hereditary B p.2))
    (fun p => natural_hereditary B (f p.1 p.2))

theorem mem_natBinaryGraph (f : ℕ → ℕ → ℕ) (m n k : ℕ) :
    ZFSet.pair (ZFSet.pair (natural m) (natural n)) (natural k) ∈ natBinaryGraph f ↔
      f m n = k := by
  rw [natBinaryGraph, mem_graphOf]
  constructor
  · rintro ⟨p, hpair, hval⟩
    obtain ⟨hm, hn⟩ := ZFSet.pair_inj.mp hpair
    have hm' := natural_injective hm
    have hn' := natural_injective hn
    simpa only [hm', hn'] using natural_injective hval
  · intro h
    exact ⟨(m, n), rfl, congrArg natural h⟩

def natRelationGraph (R : ℕ → ℕ → Prop) : ZFSet :=
  graphOf (fun p : {p : ℕ × ℕ // R p.1 p.2} => natural p.val.1)
    (fun p : {p : ℕ × ℕ // R p.1 p.2} => natural p.val.2)

theorem natRelationGraph_hereditary (R : ℕ → ℕ → Prop) :
    HereditarilySmall B (natRelationGraph R) :=
  graphOf_hereditary B
    ((Function.Embedding.subtype (fun p : ℕ × ℕ => R p.1 p.2)).trans natPairsIntoB)
    _ _ (fun p => natural_hereditary B p.val.1) (fun p => natural_hereditary B p.val.2)

theorem mem_natRelationGraph (R : ℕ → ℕ → Prop) (m n : ℕ) :
    ZFSet.pair (natural m) (natural n) ∈ natRelationGraph R ↔ R m n := by
  rw [natRelationGraph, mem_graphOf]
  constructor
  · rintro ⟨p, hpm, hpn⟩
    have hm := natural_injective hpm
    have hn := natural_injective hpn
    simpa only [hm, hn] using p.property
  · intro h
    exact ⟨⟨(m, n), h⟩, rfl, rfl⟩

theorem subsetPosetCode_mem_universe (S : Set Condition) :
    subsetPosetCode S ∈ universeSet B :=
  (mem_universeSet B _).2 (subsetPosetCode_hereditary S)

theorem orderGraph_mem_universe : orderGraph ∈ universeSet B :=
  (mem_universeSet B _).2 orderGraph_hereditary

theorem generatorGraph_mem_universe : generatorGraph ∈ universeSet B :=
  (mem_universeSet B _).2 generatorGraph_hereditary

theorem natGraph_mem_universe (f : ℕ → ℕ) : natGraph f ∈ universeSet B :=
  (mem_universeSet B _).2 (natGraph_hereditary f)

end

end Classicism.Meta.Research.MaxAtomicityHereditaryGraphs

#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryGraphs.hereditary_pair
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryGraphs.productEmbedding
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryGraphs.mem_orderGraph
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryGraphs.orderGraph_mem_universe
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryGraphs.mem_generatorGraph
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryGraphs.generatorGraph_mem_universe
