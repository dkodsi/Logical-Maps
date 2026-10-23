import Classicism.Results.Research.MaxAtomicityJechShelahSyntax
import Classicism.Results.Research.MaxAtomicityJechShelahIndexCoding
import Classicism.Results.Research.MaxAtomicitySetCodeAbsoluteness

/-!
# Standardness and uniqueness of the finite arithmetic code

This module interprets the finite omega and arithmetic formulas in the actual
Type-0 presentation of the hereditary universe. The least-inductive-set
formula determines the externally standard naturals because their actual set
code belongs to that universe. The arithmetic graphs are then determined by
ordinary induction, not by an assumed internal categoricity principle.

Direct source: the explicit original coding proof (misc, 23 October 2026,
unpaginated), for the growth recursions of Jech--Shelah, Journal of Algebra 182
(1996), pp. 749--750. This file is part of the remaining JSCode adequacy bridge;
it does not assert the final C inconsistency. Compilation is owned by the
designated serial checker.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahArithmeticSemantics

open MaxAtomicityHereditaryUniverse MaxAtomicityJechShelahSetCodes
open MaxAtomicityJechShelahCylinders MaxAtomicitySetCodeAbsoluteness
open MaxAtomicityJechShelahSyntax

noncomputable section

abbrev D := B → B
abbrev R := codeRelation B
abbrev number := naturalEmbedding

namespace O
abbrev Empty := MaxAtomicitySetFormulaTools.Ordinary.Empty (D := D)
abbrev Subset := MaxAtomicitySetFormulaTools.Ordinary.Subset (D := D)
abbrev OrderedPair := MaxAtomicitySetFormulaTools.Ordinary.OrderedPair (D := D)
abbrev GraphApp := MaxAtomicitySetFormulaTools.Ordinary.GraphApp (D := D)
abbrev FunctionGraph := MaxAtomicitySetFormulaTools.Ordinary.FunctionGraph (D := D)
end O

theorem successor_iff (x y : D) :
    Ordinary.Successor R x y ↔ present B y = insert (present B x) (present B x) := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      have hzH := universeSet_transitive B _ (present_mem B y) z hz
      have hd := (h (encode B z hzH)).1 ((encoded_mem B z hzH y).2 hz)
      rcases hd with hd | hd
      · exact Or.inr ((encoded_mem B z hzH x).1 hd)
      · exact Or.inl ((present_encode B z hzH).symm.trans (congrArg (present B) hd))
    · rintro (hz | hz)
      · subst z
        exact (h x).2 (Or.inr rfl)
      · have hzH := universeSet_transitive B _ (present_mem B x) z hz
        exact (encoded_mem B z hzH y).1
          ((h (encode B z hzH)).2 (Or.inl ((encoded_mem B z hzH x).2 hz)))
  · intro h d
    change present B d ∈ present B y ↔ present B d ∈ present B x ∨ d = x
    rw [h, ZFSet.mem_insert_iff, ← equal_iff B d x]
    exact or_comm

theorem number_mem (m n : ℕ) : R (number m) (number n) ↔ m < n := by
  change present B (number m) ∈ present B (number n) ↔ _
  rw [present_naturalEmbedding, present_naturalEmbedding, natural_mem_natural]

theorem empty_iff_zero (x : D) : O.Empty R x ↔ x = number 0 := by
  rw [empty_iff B, equal_iff B x (number 0), present_naturalEmbedding, natural_zero]

theorem successor_number (m : ℕ) (y : D) :
    Ordinary.Successor R (number m) y ↔ y = number (m + 1) := by
  rw [successor_iff, equal_iff B y (number (m + 1)), present_naturalEmbedding,
    present_naturalEmbedding, natural_succ]

theorem successor_numbers (m n : ℕ) :
    Ordinary.Successor R (number m) (number n) ↔ n = m + 1 := by
  rw [successor_number]
  exact naturalEmbedding.injective.eq_iff

theorem number_in_omega (n : ℕ) : R (number n) canonicalNaturals :=
  (canonical_number_range _).2 ⟨n, rfl⟩

theorem canonical_inductive : Ordinary.InductiveSet R canonicalNaturals := by
  refine ⟨⟨number 0, number_in_omega 0, (empty_iff_zero _).2 rfl⟩, ?_⟩
  intro x hx
  obtain ⟨n, rfl⟩ := (canonical_number_range x).1 hx
  exact ⟨number (n + 1), number_in_omega _, (successor_number n _).2 rfl⟩

theorem number_in_inductive {I : D} (hI : Ordinary.InductiveSet R I) (n : ℕ) :
    R (number n) I := by
  induction n with
  | zero =>
    obtain ⟨z, hz, he⟩ := hI.1
    exact (empty_iff_zero z).1 he ▸ hz
  | succ n ih =>
    obtain ⟨y, hy, hs⟩ := hI.2 (number n) ih
    exact (successor_number n y).1 hs ▸ hy

/-- Leastness quantifies over the actual canonical omega witness in H;
ordinary external induction proves the converse containment. -/
theorem omega_iff (w : D) : Ordinary.Omega R w ↔ w = canonicalNaturals := by
  constructor
  · intro hw
    apply codeRelation_extensional B
    intro x
    constructor
    · exact hw.2 canonicalNaturals canonical_inductive x
    · intro hx
      obtain ⟨n, rfl⟩ := (canonical_number_range x).1 hx
      exact number_in_inductive hw.1 n
  · rintro rfl
    refine ⟨canonical_inductive, ?_⟩
    intro I hI x hx
    obtain ⟨n, rfl⟩ := (canonical_number_range x).1 hx
    exact number_in_inductive hI n

theorem graphApp₂_unique {f x y u v : D} (hf : O.FunctionGraph R f)
    (hu : Ordinary.GraphApp₂ R f x y u) (hv : Ordinary.GraphApp₂ R f x y v) : u = v := by
  obtain ⟨p, hp, hpu⟩ := hu
  obtain ⟨q, hq, hqv⟩ := hv
  have hpq : p = q := present_injective B
    (((orderedPair_iff B x y p).1 hp).trans ((orderedPair_iff B x y q).1 hq).symm)
  subst q
  exact hf.2 p u v ⟨hpu, hqv⟩

theorem graphApp₂_nat_unique {f : D} (hf : O.FunctionGraph R f) :
    ∀ x y u v, Ordinary.GraphApp₂ R f (number x) (number y) (number u) →
      Ordinary.GraphApp₂ R f (number x) (number y) (number v) → u = v := by
  intro x y u v hu hv
  exact naturalEmbedding.injective (graphApp₂_unique hf hu hv)

/-- Unary totality and graph functionality produce an actual numerical
function; no choice or correctness premise is inserted into the object code. -/
theorem unary_decodable {w f : D} (hw : w = canonicalNaturals)
    (hf : Ordinary.UnaryOn R w f) :
    ∃ F : ℕ → ℕ, ∀ k v, O.GraphApp R f (number k) (number v) ↔ v = F k := by
  classical
  have hex : ∀ k : ℕ, ∃ v : ℕ, O.GraphApp R f (number k) (number v) := by
    intro k
    have hk : R (number k) w := hw.symm ▸ number_in_omega k
    obtain ⟨v, hv, hfv⟩ := hf.2.2 (number k) hk
    rw [hw] at hv
    obtain ⟨n, rfl⟩ := (canonical_number_range v).1 hv
    exact ⟨n, hfv⟩
  let F : ℕ → ℕ := fun k => Classical.choose (hex k)
  have hF : ∀ k, O.GraphApp R f (number k) (number (F k)) :=
    fun k => Classical.choose_spec (hex k)
  refine ⟨F, ?_⟩
  intro k v
  constructor
  · intro hv
    exact naturalEmbedding.injective (hf.1.2 (number k) (number v) (number (F k)) ⟨hv, hF k⟩)
  · rintro rfl
    exact hF k

structure Decoded (a : Parameters D) : Prop where
  omega : a.w = canonicalNaturals
  zero : a.zero = number 0
  one : a.one = number 1
  two : a.two = number 2
  add : ∀ x y v, Ordinary.GraphApp₂ R a.add (number x) (number y) (number v) ↔ v = x + y
  mul : ∀ x y v, Ordinary.GraphApp₂ R a.mul (number x) (number y) (number v) ↔ v = x * y
  pow : ∀ x y v, Ordinary.GraphApp₂ R a.pow (number x) (number y) (number v) ↔ v = x ^ y
  p : ∀ k v, O.GraphApp R a.p (number k) (number v) ↔ v = MaxAtomicityJechShelahTrees.growthP k
  n : ∀ k v, O.GraphApp R a.n (number k) (number v) ↔ v = MaxAtomicityJechShelahTrees.growthN k
  offset : ∀ k v, O.GraphApp R a.offset (number k) (number v) ↔ v = MaxAtomicityJechShelahTrees.offset k
  ancestor : ∀ i j, O.GraphApp R a.ancestor (number i) (number j) ↔
    MaxAtomicityJechShelahIndexCoding.Ancestor i j

theorem leNat_numbers (m n : ℕ) : Ordinary.LeNat R (number m) (number n) ↔ m ≤ n := by
  change (number m = number n ∨ R (number m) (number n)) ↔ _
  rw [naturalEmbedding.injective.eq_iff, number_mem]
  omega

theorem child_decoded {a : Parameters D}
    (hw : a.w = canonicalNaturals)
    (hadd : ∀ x y v, Ordinary.GraphApp₂ R a.add (number x) (number y) (number v) ↔ v = x + y)
    (hn : ∀ k v, O.GraphApp R a.n (number k) (number v) ↔ v = MaxAtomicityJechShelahTrees.growthN k)
    (ho : ∀ k v, O.GraphApp R a.offset (number k) (number v) ↔ v = MaxAtomicityJechShelahTrees.offset k)
    (k j : ℕ) : Ordinary.Child R a (number k) (number j) ↔
      MaxAtomicityJechShelahIndexCoding.Child k j := by
  constructor
  · rintro ⟨o, how, n, hnw, e, hew, hko, hkn, hoe, hle, hlt⟩
    rw [hw] at how hnw hew
    obtain ⟨o, rfl⟩ := (canonical_number_range o).1 how
    obtain ⟨n, rfl⟩ := (canonical_number_range n).1 hnw
    obtain ⟨e, rfl⟩ := (canonical_number_range e).1 hew
    have ho' := (ho k o).1 hko
    have hn' := (hn k n).1 hkn
    have he' := (hadd o n e).1 hoe
    have hle' := (leNat_numbers o j).1 hle
    have hlt' := (number_mem j e).1 hlt
    exact ⟨by simpa only [ho'] using hle', by simpa only [he', ho', hn'] using hlt'⟩
  · intro h
    let o := MaxAtomicityJechShelahTrees.offset k
    let n := MaxAtomicityJechShelahTrees.growthN k
    have hmem : ∀ n, R (number n) a.w := fun n => hw.symm ▸ number_in_omega n
    exact ⟨number o, hmem o, number n, hmem n, number (o + n), hmem _,
      (ho k o).2 rfl, (hn k n).2 rfl, (hadd o n (o + n)).2 rfl,
      (leNat_numbers o j).2 h.1, (number_mem j (o + n)).2 h.2⟩

/-- All arithmetic and ancestry values are derived from the actual finite
formula's ordinary interpretation. This is a soundness statement, not a
postulate that such auxiliary witnesses exist. -/
theorem arithmetic_decoded {a : Parameters D} (h : Ordinary.Arithmetic R a) : Decoded a := by
  classical
  rcases h with ⟨hw, hz, h1, h2, hzw, h1w, h2w, hA, hM, hE, hP, hN, hO,
    hAr, hMr, hEr, hGr, hAnc⟩
  have hw' := (omega_iff a.w).1 hw
  have hz' := (empty_iff_zero a.zero).1 hz
  have h1' : a.one = number 1 := by
    rw [hz'] at h1
    exact (successor_number 0 a.one).1 h1
  have h2' : a.two = number 2 := by
    rw [h1'] at h2
    exact (successor_number 1 a.two).1 h2
  have hmem : ∀ k, R (number k) a.w := fun k => hw'.symm ▸ number_in_omega k
  have add : ∀ x y v, Ordinary.GraphApp₂ R a.add (number x) (number y) (number v) ↔ v = x + y := by
    apply MaxAtomicityJechShelahIndexCoding.add_relation_unique
      (fun x y v => Ordinary.GraphApp₂ R a.add (number x) (number y) (number v))
      (graphApp₂_nat_unique hA.1)
    · intro x
      simpa only [hz'] using hAr.1 (number x) (hmem x)
    · intro x y v
      have hs := hAr.2 (number x) (hmem x) (number y) (hmem y)
        (number (y + 1)) (hmem _) (number v) (hmem v) ((successor_number y _).2 rfl)
      rw [hs]
      constructor
      · rintro ⟨u, huw, hxu, huv⟩
        rw [hw'] at huw
        obtain ⟨u, rfl⟩ := (canonical_number_range u).1 huw
        exact ⟨u, hxu, (successor_numbers u v).1 huv⟩
      · rintro ⟨u, hxu, huv⟩
        exact ⟨number u, hmem u, hxu, (successor_numbers u v).2 huv⟩
  have mul : ∀ x y v, Ordinary.GraphApp₂ R a.mul (number x) (number y) (number v) ↔ v = x * y := by
    apply MaxAtomicityJechShelahIndexCoding.mul_relation_unique
      (fun x y v => Ordinary.GraphApp₂ R a.mul (number x) (number y) (number v))
      (graphApp₂_nat_unique hM.1)
    · intro x
      simpa only [hz'] using hMr.1 (number x) (hmem x)
    · intro x y v
      have hs := hMr.2 (number x) (hmem x) (number y) (hmem y)
        (number (y + 1)) (hmem _) (number v) (hmem v) ((successor_number y _).2 rfl)
      rw [hs]
      constructor
      · rintro ⟨u, huw, hxu, huv⟩
        rw [hw'] at huw
        obtain ⟨u, rfl⟩ := (canonical_number_range u).1 huw
        exact ⟨u, hxu, (add u x v).1 huv⟩
      · rintro ⟨u, hxu, huv⟩
        exact ⟨number u, hmem u, hxu, (add u x v).2 huv⟩
  have pow : ∀ x y v, Ordinary.GraphApp₂ R a.pow (number x) (number y) (number v) ↔ v = x ^ y := by
    apply MaxAtomicityJechShelahIndexCoding.pow_relation_unique
      (fun x y v => Ordinary.GraphApp₂ R a.pow (number x) (number y) (number v))
      (graphApp₂_nat_unique hE.1)
    · intro x
      simpa only [hz', h1'] using hEr.1 (number x) (hmem x)
    · intro x y v
      have hs := hEr.2 (number x) (hmem x) (number y) (hmem y)
        (number (y + 1)) (hmem _) (number v) (hmem v) ((successor_number y _).2 rfl)
      rw [hs]
      constructor
      · rintro ⟨u, huw, hxu, huv⟩
        rw [hw'] at huw
        obtain ⟨u, rfl⟩ := (canonical_number_range u).1 huw
        exact ⟨u, hxu, (mul u x v).1 huv⟩
      · rintro ⟨u, hxu, huv⟩
        exact ⟨number u, hmem u, hxu, (mul u x v).2 huv⟩
  obtain ⟨p, hp⟩ := unary_decodable hw' hP
  obtain ⟨n, hn⟩ := unary_decodable hw' hN
  obtain ⟨o, ho⟩ := unary_decodable hw' hO
  have p0 : p 0 = 1 := ((hp 0 1).1 (by simpa only [hz', h1'] using hGr.1)).symm
  have n0 : n 0 = 1 := ((hn 0 1).1 (by simpa only [hz', h1'] using hGr.2.1)).symm
  have o0 : o 0 = 1 := ((ho 0 1).1 (by simpa only [hz', h1'] using hGr.2.2.1)).symm
  have step : ∀ k, p (k + 1) = p k * n k ∧ n (k + 1) = 2 ^ p (k + 1) ∧
      o (k + 1) = o k + n k := by
    intro k
    have hs := hGr.2.2.2 (number k) (hmem k) (number (k + 1)) (hmem _)
      (number (p k)) (hmem _) (number (n k)) (hmem _) (number (o k)) (hmem _)
      (number (p (k + 1))) (hmem _) (number (n (k + 1))) (hmem _)
      (number (o (k + 1))) (hmem _) ((successor_number k _).2 rfl)
      ((hp k _).2 rfl) ((hn k _).2 rfl) ((ho k _).2 rfl)
      ((hp (k + 1) _).2 rfl) ((hn (k + 1) _).2 rfl) ((ho (k + 1) _).2 rfl)
    refine ⟨(mul _ _ _).1 hs.1, ?_, (add _ _ _).1 hs.2.2⟩
    exact (pow 2 _ _).1 (by simpa only [h2'] using hs.2.1)
  have hgrowth := MaxAtomicityJechShelahIndexCoding.growth_unique p n o p0 n0 o0
    (fun k => (step k).1) (fun k => (step k).2.1) (fun k => (step k).2.2)
  have pExact : ∀ k v, O.GraphApp R a.p (number k) (number v) ↔ v = MaxAtomicityJechShelahTrees.growthP k := by
    intro k v
    simpa only [(hgrowth k).1] using hp k v
  have nExact : ∀ k v, O.GraphApp R a.n (number k) (number v) ↔ v = MaxAtomicityJechShelahTrees.growthN k := by
    intro k v
    simpa only [(hgrowth k).2.1] using hn k v
  have oExact : ∀ k v, O.GraphApp R a.offset (number k) (number v) ↔ v = MaxAtomicityJechShelahTrees.offset k := by
    intro k v
    simpa only [(hgrowth k).2.2] using ho k v
  refine ⟨hw', hz', h1', h2', add, mul, pow, pExact, nExact, oExact, ?_⟩
  apply MaxAtomicityJechShelahIndexCoding.ancestor_unique
    (fun i j => O.GraphApp R a.ancestor (number i) (number j))
  intro i j
  rw [hAnc.2 (number i) (hmem i) (number j) (hmem j)]
  apply or_congr naturalEmbedding.injective.eq_iff
  constructor
  · rintro ⟨k, hkw, hchild, hik⟩
    rw [hw'] at hkw
    obtain ⟨k, rfl⟩ := (canonical_number_range k).1 hkw
    exact ⟨k, (child_decoded hw' add nExact oExact k j).1 hchild, hik⟩
  · rintro ⟨k, hchild, hik⟩
    exact ⟨number k, hmem k, (child_decoded hw' add nExact oExact k j).2 hchild, hik⟩

#print axioms omega_iff
#print axioms graphApp₂_unique
#print axioms unary_decodable
#print axioms arithmetic_decoded

end

end Classicism.Meta.Research.MaxAtomicityJechShelahArithmeticSemantics
