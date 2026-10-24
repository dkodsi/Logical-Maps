import Classicism.Results.Research.MaxAtomicityJechShelahArithmeticSemantics
import Classicism.Results.Research.MaxAtomicityCodedFunctions

/-!
# Actual canonical witnesses for the finite arithmetic code

All graph witnesses are encoded small ZFSet graphs. Unary and binary totality,
functionality, numerical values, and the ancestry relation are proved for
these witnesses. The complete finite Ordinary.Arithmetic predicate then follows
from ordinary natural-number arithmetic and the actual tree-index recurrence.
No arithmetic-coding adequacy or witness-existence assertion is assumed.

Original formal proof: misc, 23 October 2026, for the arithmetic recurrences
of Jech--Shelah, Journal of Algebra 182 (1996), pp. 749--750. Source awaits the
designated serial checker.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahArithmeticExistence

open MaxAtomicityHereditaryUniverse MaxAtomicityHereditaryGraphs
open MaxAtomicityJechShelahSetCodes MaxAtomicitySetCodeAbsoluteness
open MaxAtomicityJechShelahCylinders MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahSyntax MaxAtomicityJechShelahArithmeticSemantics
open MaxAtomicityJechShelahIndexCoding MaxAtomicityCodedFunctions

noncomputable section

namespace F
abbrev OrderedPair := MaxAtomicitySetFormulaTools.Ordinary.OrderedPair (D := D)
abbrev GraphApp := MaxAtomicitySetFormulaTools.Ordinary.GraphApp (D := D)
end F

def pairCode (x y : D) : D :=
  encode B (ZFSet.pair (present B x) (present B y))
    ((mem_universeSet B _).2
      (hereditary_pair B (present_hereditary B x) (present_hereditary B y)))

@[simp] theorem present_pairCode (x y : D) :
    present B (pairCode x y) = ZFSet.pair (present B x) (present B y) := present_encode B _ _

theorem orderedPair_pairCode (x y : D) : F.OrderedPair R x y (pairCode x y) :=
  (orderedPair_iff B _ _ _).2 (present_pairCode x y)

theorem orderedPair_eq_pairCode {x y p : D} (h : F.OrderedPair R x y p) : p = pairCode x y :=
  present_injective B (((orderedPair_iff B _ _ _).1 h).trans (present_pairCode x y).symm)

def pairNumber (p : ℕ × ℕ) : D := pairCode (number p.1) (number p.2)

theorem pairNumber_injective : Function.Injective pairNumber := by
  intro p q h
  have hp := congrArg (present B) h
  simp only [pairNumber, present_pairCode, present_naturalEmbedding] at hp
  obtain ⟨h1, h2⟩ := ZFSet.pair_inj.mp hp
  exact Prod.ext (natural_injective h1) (natural_injective h2)

def unary (f : ℕ → ℕ) : D :=
  functionCode (Infinite.natEmbedding B) number (fun n => number (f n))

def binary (f : ℕ → ℕ → ℕ) : D :=
  functionCode natPairsIntoB pairNumber (fun p => number (f p.1 p.2))

def relation (r : ℕ → ℕ → Prop) : D :=
  functionCode
    ((Function.Embedding.subtype (fun p : ℕ × ℕ => r p.1 p.2)).trans natPairsIntoB)
    (fun p => number p.val.1) (fun p => number p.val.2)

theorem present_unary (f : ℕ → ℕ) : present B (unary f) = natGraph f := by
  simp only [unary, present_functionCode, present_naturalEmbedding, natGraph]

theorem present_binary (f : ℕ → ℕ → ℕ) : present B (binary f) = natBinaryGraph f := by
  simp only [binary, present_functionCode, pairNumber, present_pairCode,
    present_naturalEmbedding, natBinaryGraph]

theorem present_relation (r : ℕ → ℕ → Prop) : present B (relation r) = natRelationGraph r := by
  simp only [relation, present_functionCode, present_naturalEmbedding, natRelationGraph]

theorem unary_app (f : ℕ → ℕ) (m n : ℕ) :
    F.GraphApp R (unary f) (number m) (number n) ↔ n = f m := by
  rw [unary, functionCode_app]
  constructor
  · rintro ⟨k, hkm, hfn⟩
    have hk : k = m := naturalEmbedding.injective hkm
    subst k
    exact (naturalEmbedding.injective hfn).symm
  · intro h
    exact ⟨m, rfl, congrArg number h.symm⟩

theorem binary_app (f : ℕ → ℕ → ℕ) (m n k : ℕ) :
    Ordinary.GraphApp₂ R (binary f) (number m) (number n) (number k) ↔ k = f m n := by
  constructor
  · rintro ⟨xy, hxy, hg⟩
    have hxy' : xy = pairNumber (m, n) := orderedPair_eq_pairCode hxy
    rw [binary, functionCode_app] at hg
    obtain ⟨p, hpin, hpout⟩ := hg
    have hp : p = (m, n) := pairNumber_injective (hpin.trans hxy')
    subst p
    exact (naturalEmbedding.injective hpout).symm
  · intro h
    refine ⟨pairNumber (m, n), orderedPair_pairCode _ _, ?_⟩
    exact (functionCode_app natPairsIntoB pairNumber (fun p => number (f p.1 p.2)) _ _).2
      ⟨(m, n), rfl, congrArg number h.symm⟩

theorem relation_app (r : ℕ → ℕ → Prop) (m n : ℕ) :
    F.GraphApp R (relation r) (number m) (number n) ↔ r m n := by
  rw [relation, functionCode_app]
  constructor
  · rintro ⟨p, hm, hn⟩
    have hm' := naturalEmbedding.injective hm
    have hn' := naturalEmbedding.injective hn
    simpa only [hm', hn'] using p.property
  · intro h
    exact ⟨⟨(m, n), h⟩, rfl, rfl⟩

theorem forall_omega (P : D → Prop) :
    (∀ x, R x canonicalNaturals → P x) ↔ ∀ n : ℕ, P (number n) := by
  constructor
  · intro h n
    exact h (number n) (number_in_omega n)
  · intro h x hx
    obtain ⟨n, rfl⟩ := (canonical_number_range x).1 hx
    exact h n

theorem exists_omega (P : D → Prop) :
    (∃ x, R x canonicalNaturals ∧ P x) ↔ ∃ n : ℕ, P (number n) := by
  constructor
  · rintro ⟨x, hx, hP⟩
    obtain ⟨n, rfl⟩ := (canonical_number_range x).1 hx
    exact ⟨n, hP⟩
  · rintro ⟨n, hn⟩
    exact ⟨number n, number_in_omega n, hn⟩

theorem unary_on (f : ℕ → ℕ) : Ordinary.UnaryOn R canonicalNaturals (unary f) := by
  refine ⟨functionCode_function _ _ _ naturalEmbedding.injective,
    functionCode_domain _ _ _ _ canonical_number_range, ?_⟩
  intro x hx
  obtain ⟨n, rfl⟩ := (canonical_number_range x).1 hx
  exact ⟨number (f n), number_in_omega _, (unary_app f n (f n)).2 rfl⟩

theorem binary_on (f : ℕ → ℕ → ℕ) : Ordinary.BinaryOn R canonicalNaturals (binary f) := by
  refine ⟨functionCode_function _ _ _ pairNumber_injective, ?_, ?_⟩
  · intro p hp
    change present B p ∈ present B (binary f) at hp
    rw [present_binary, natBinaryGraph, graphOf, ZFSet.mem_range] at hp
    obtain ⟨a, ha⟩ := hp
    refine ⟨number a.1, number_in_omega _, number a.2, number_in_omega _,
      number (f a.1 a.2), number_in_omega _, pairNumber a, orderedPair_pairCode _ _, ?_⟩
    apply (orderedPair_iff B _ _ _).2
    simpa only [pairNumber, present_pairCode, present_naturalEmbedding] using ha.symm
  · intro x hx y hy
    obtain ⟨m, rfl⟩ := (canonical_number_range x).1 hx
    obtain ⟨n, rfl⟩ := (canonical_number_range y).1 hy
    exact ⟨number (f m n), number_in_omega _, (binary_app f m n (f m n)).2 rfl⟩

theorem relation_on (r : ℕ → ℕ → Prop) : Ordinary.RelationOn R canonicalNaturals (relation r) := by
  intro p hp
  change present B p ∈ present B (relation r) at hp
  rw [present_relation, natRelationGraph, graphOf, ZFSet.mem_range] at hp
  obtain ⟨a, ha⟩ := hp
  exact ⟨number a.val.1, number_in_omega _, number a.val.2, number_in_omega _,
    (orderedPair_iff B _ _ _).2 (by simpa only [present_naturalEmbedding] using ha.symm)⟩

/-- All eleven named parameters are actual elements of the hereditary code. -/
def parameters : Parameters D where
  w := canonicalNaturals
  zero := number 0
  one := number 1
  two := number 2
  add := binary (fun m n => m + n)
  mul := binary (fun m n => m * n)
  pow := binary (fun m n => m ^ n)
  p := unary growthP
  n := unary growthN
  offset := unary offset
  ancestor := relation Ancestor

theorem add_recursion : Ordinary.AddRecursion R parameters := by
  constructor
  · rw [forall_omega]
    intro x
    exact (binary_app (fun m n => m + n) x 0 x).2 (Nat.add_zero x).symm
  · simp only [parameters, forall_omega, exists_omega, binary_app, successor_numbers]
    intro x y y' v h
    subst y'
    simp only [exists_eq_left, Nat.add_succ]

theorem mul_recursion : Ordinary.MulRecursion R parameters := by
  constructor
  · rw [forall_omega]
    intro x
    exact (binary_app (fun m n => m * n) x 0 0).2 (Nat.mul_zero x).symm
  · simp only [parameters, forall_omega, exists_omega, binary_app, successor_numbers]
    intro x y y' v h
    subst y'
    simp only [exists_eq_left, Nat.mul_succ]

theorem pow_recursion : Ordinary.PowRecursion R parameters := by
  constructor
  · rw [forall_omega]
    intro x
    exact (binary_app (fun m n => m ^ n) x 0 1).2 (pow_zero x).symm
  · simp only [parameters, forall_omega, exists_omega, binary_app, successor_numbers]
    intro x y y' v h
    subst y'
    simp only [exists_eq_left, pow_succ]

theorem growth_recursion : Ordinary.GrowthRecursion R parameters := by
  refine ⟨(unary_app growthP 0 1).2 rfl, (unary_app growthN 0 1).2 rfl,
    (unary_app offset 0 1).2 rfl, ?_⟩
  simp only [parameters, forall_omega, unary_app, binary_app, successor_numbers]
  intro k k' p n o p' n' o' hk hp hn ho hp' hn' ho'
  subst k'; subst p; subst n; subst o; subst p'; subst n'; subst o'
  exact ⟨growthP_succ k, growthN_succ k, offset_succ k⟩

theorem canonical_child (k j : ℕ) : Ordinary.Child R parameters (number k) (number j) ↔ Child k j :=
  child_decoded rfl (binary_app (fun x y => x + y)) (unary_app growthN) (unary_app offset) k j

theorem ancestor_recursion_code : Ordinary.AncestorRecursion R parameters := by
  refine ⟨relation_on Ancestor, ?_⟩
  rw [forall_omega]
  intro i
  rw [forall_omega]
  intro j
  simp only [parameters, relation_app, naturalEmbedding.injective.eq_iff,
    exists_omega, canonical_child]
  exact ancestor_recursion i j

/-- Existence of the actual finite arithmetic witnesses, with no decoding or
recursion premise. This is the existence half complementary to arithmetic_decoded. -/
theorem canonical_arithmetic : Ordinary.Arithmetic R parameters :=
  ⟨(omega_iff _).2 rfl, (empty_iff_zero _).2 rfl,
    (successor_number 0 _).2 rfl, (successor_number 1 _).2 rfl,
    number_in_omega 0, number_in_omega 1, number_in_omega 2,
    binary_on (fun x y => x + y), binary_on (fun x y => x * y),
    binary_on (fun x y => x ^ y), unary_on growthP, unary_on growthN,
    unary_on offset, add_recursion, mul_recursion, pow_recursion,
    growth_recursion, ancestor_recursion_code⟩

/-- The exact arithmetic-existence interface used by the canonical JSCode proof. -/
theorem canonical_arithmetic_exists :
    ∃ a : Parameters D, a.w = canonicalNaturals ∧ Ordinary.Arithmetic R a :=
  ⟨parameters, rfl, canonical_arithmetic⟩

#print axioms unary_on
#print axioms binary_on
#print axioms relation_on
#print axioms add_recursion
#print axioms mul_recursion
#print axioms pow_recursion
#print axioms growth_recursion
#print axioms ancestor_recursion_code
#print axioms canonical_arithmetic
#print axioms canonical_arithmetic_exists

end

end Classicism.Meta.Research.MaxAtomicityJechShelahArithmeticExistence
