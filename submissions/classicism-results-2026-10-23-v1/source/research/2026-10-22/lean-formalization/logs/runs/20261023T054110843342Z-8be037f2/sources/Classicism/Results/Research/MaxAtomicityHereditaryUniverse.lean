import Classicism.Results.Research.MaxAtomicityHereditaryCover
import Mathlib.Data.W.Cardinal
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# A set of all hereditarily K-small sets

Direct source: the original universe-code argument in
`max-atomicity-inconsistency-proof.md`, section 3 (misc, unpaginated), with
the W-type construction supplied here. This file constructs the universe as
the range of a decoding function on a small W-type. It does not assume that
the hereditary-small class is a set, or assume its upper cardinality bound.

The branching labels are arbitrary subsets of K. A tree decodes to the set
of its decoded children. Every hereditarily K-small set has such a tree,
by membership induction and an actual embedding of each member set into K.

This is external classical set theory. Compilation is reserved to the
designated serial checker; source preparation is not a successful Lean check.
-/

namespace Classicism.Meta.Research.MaxAtomicityHereditaryUniverse

open MaxAtomicityMostowski MaxAtomicityHereditaryCover
open Cardinal

universe u

noncomputable section

variable (K : Type u)

/-- Well-founded trees whose children at any node are indexed by a subset of K. -/
abbrev SmallTree := WType (fun s : Set K => s)

/-- Decode a tree as an actual extensional ZFSet. -/
def decode : SmallTree K → ZFSet.{u}
  | .mk _ f => ZFSet.range (fun i => decode (f i))

theorem mem_decode (s : Set K) (f : s → SmallTree K) (z : ZFSet.{u}) :
    z ∈ decode K (.mk s f) ↔ ∃ i : s, decode K (f i) = z :=
  ZFSet.mem_range

/-- A small indexed family of hereditarily small sets has a hereditarily
small range. Repeated family values do not require an injective enumeration:
the right inverse of the actual surjection supplies the needed embedding. -/
theorem hereditary_range {A : Type u} (e : A ↪ K) (f : A → ZFSet.{u})
    (hf : ∀ a, HereditarilySmall K (f a)) :
    HereditarilySmall K (ZFSet.range f) := by
  classical
  apply ZFSet.hereditarily_iff.mpr
  constructor
  · let q : A → {z : ZFSet.{u} // z ∈ ZFSet.range f} :=
      fun a => ⟨f a, ZFSet.mem_range_self a⟩
    have hq : Function.Surjective q := by
      intro z
      obtain ⟨a, ha⟩ := ZFSet.mem_range.mp z.2
      exact ⟨a, Subtype.ext ha⟩
    exact ⟨(Function.Embedding.ofSurjective q hq).trans e⟩
  · intro z hz
    obtain ⟨a, ha⟩ := ZFSet.mem_range.mp hz
    exact ha ▸ hf a

theorem decode_hereditary (w : SmallTree K) :
    HereditarilySmall K (decode K w) := by
  induction w with
  | mk s f ih =>
    exact hereditary_range K (Function.Embedding.subtype s) (fun i => decode K (f i)) ih

/-- Every set satisfying the hereditary member bound has a representing tree.
The recursion is genuine membership induction; the result is not postulated. -/
theorem hereditary_has_tree (x : ZFSet.{u}) :
    HereditarilySmall K x → ∃ w : SmallTree K, decode K w = x := by
  classical
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    obtain ⟨e⟩ := ZFSet.Hereditarily.self hx
    let s : Set K := Set.range e
    let member : s → {z : ZFSet.{u} // z ∈ x} :=
      fun i => Classical.choose i.2
    have member_spec (i : s) : e (member i) = i.1 := Classical.choose_spec i.2
    have member_surj : Function.Surjective member := by
      intro z
      refine ⟨⟨e z, ⟨z, rfl⟩⟩, ?_⟩
      apply e.injective
      exact member_spec ⟨e z, ⟨z, rfl⟩⟩
    have child_exists (i : s) :
        ∃ w : SmallTree K, decode K w = (member i).1 :=
      ih (member i).1 (member i).2 (ZFSet.Hereditarily.mem hx (member i).2)
    let f : s → SmallTree K := fun i => Classical.choose (child_exists i)
    have f_spec (i : s) : decode K (f i) = (member i).1 :=
      Classical.choose_spec (child_exists i)
    refine ⟨.mk s f, ?_⟩
    apply ZFSet.ext
    intro z
    rw [mem_decode]
    constructor
    · rintro ⟨i, hi⟩
      rw [← hi, f_spec]
      exact (member i).2
    · intro hz
      obtain ⟨i, hi⟩ := member_surj ⟨z, hz⟩
      exact ⟨i, (f_spec i).trans (congrArg Subtype.val hi)⟩

/-- An actual set containing exactly the hereditarily K-small sets. -/
def universeSet : ZFSet.{u} := ZFSet.range (decode K)

theorem mem_universeSet (x : ZFSet.{u}) :
    x ∈ universeSet K ↔ HereditarilySmall K x := by
  change x ∈ ZFSet.range (decode K) ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    exact hw ▸ decode_hereditary K w
  · exact hereditary_has_tree K x

theorem universeSet_transitive :
    ∀ x : ZFSet.{u}, x ∈ universeSet K →
      ∀ y : ZFSet.{u}, y ∈ x → y ∈ universeSet K := by
  intro x hx y hy
  exact (mem_universeSet K y).2
    (ZFSet.Hereditarily.mem ((mem_universeSet K x).1 hx) hy)

/-- The cardinal calculation is carried out on the indexing W-type, using
the proved least-fixed-point bound in Mathlib. -/
theorem smallTree_card_le [Infinite K] :
    Cardinal.mk (SmallTree K) ≤ 2 ^ Cardinal.mk K := by
  have hK : ℵ₀ ≤ #K := aleph0_le_mk K
  have hpow : (2 : Cardinal.{u}) ^ #K ≠ 0 := by
    exact ne_of_gt (lt_of_le_of_lt (zero_le : 0 ≤ #K) (cantor #K))
  apply WType.cardinalMk_le_of_le
  calc
    (sum fun s : Set K => (2 ^ #K) ^ #s)
        ≤ #(Set K) * ⨆ s : Set K, (2 ^ #K) ^ #s := sum_le_mk_mul_iSup _
    _ ≤ (2 ^ #K) * (2 ^ #K) := by
      rw [mk_set]
      apply mul_le_mul' le_rfl
      apply ciSup_le'
      intro s
      calc
        (2 ^ #K) ^ #s ≤ (2 ^ #K) ^ #K :=
          power_le_power_left hpow (mk_set_le s)
        _ = 2 ^ #K := by rw [← power_mul, mul_eq_self hK]
    _ = 2 ^ #K := mul_eq_self (hK.trans (cantor #K).le)

/-- This range bound is universe-polymorphic in ZFSet's cardinal API. -/
theorem universeSet_card_le [Infinite K] :
    ZFSet.card (universeSet K) ≤ 2 ^ Cardinal.mk K := by
  have h := ZFSet.lift_card_range_le (f := decode K)
  have hrange : ZFSet.card (universeSet K) ≤ Cardinal.mk (SmallTree K) := by
    simpa only [Cardinal.lift_id, universeSet] using h
  exact hrange.trans (smallTree_card_le K)

/-- A well-order is extensional in its predecessor sets. -/
theorem wellOrder_extensional {A : Type u} (r : A → A → Prop)
    [IsWellOrder A r] : MaxAtomicityMostowski.Extensional r := by
  intro x y h
  rcases trichotomous_of r x y with hxy | hxy | hyx
  · exact False.elim ((irrefl x) ((h x).2 hxy))
  · exact hxy
  · exact False.elim ((irrefl y) ((h y).1 hyx))

/-- Well-order collapse supplies distinct hereditary-small codes for all K
elements. This choice occurs only in external cardinality metatheory. -/
def elementCode (x : K) : ZFSet.{u} :=
  collapse (WellOrderingRel.isWellOrder (α := K)).wf x

theorem elementCode_injective : Function.Injective (elementCode K) :=
  collapse_injective (WellOrderingRel.isWellOrder (α := K)).wf
    (wellOrder_extensional (@WellOrderingRel K))

theorem elementCode_hereditary (x : K) : HereditarilySmall K (elementCode K x) := by
  apply collapse_hereditarilySmall K
    (WellOrderingRel.isWellOrder (α := K)).wf
    (wellOrder_extensional (@WellOrderingRel K))
  intro y
  exact ⟨Function.Embedding.subtype (fun z : K => WellOrderingRel z y)⟩

/-- Encode a subset by the set of codes of its members. -/
def subsetCode (s : Set K) : ZFSet.{u} :=
  ZFSet.range (fun i : s => elementCode K i.1)

theorem subsetCode_hereditary (s : Set K) : HereditarilySmall K (subsetCode K s) :=
  hereditary_range K (Function.Embedding.subtype s)
    (fun i : s => elementCode K i.1) (fun i => elementCode_hereditary K i.1)

theorem mem_subsetCode (s : Set K) (x : K) :
    elementCode K x ∈ subsetCode K s ↔ x ∈ s := by
  change elementCode K x ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    have hix : i.1 = x := elementCode_injective K hi
    exact hix ▸ i.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem subsetCode_injective : Function.Injective (subsetCode K) := by
  intro s t h
  apply Set.ext
  intro x
  rw [← mem_subsetCode K s x, h, mem_subsetCode K t x]

/-- The lower bound is witnessed by an actual injection of all subsets of K. -/
def subsetsIntoUniverse : Set K ↪ (universeSet K : Set ZFSet.{u}) where
  toFun s := ⟨subsetCode K s, (mem_universeSet K _).2 (subsetCode_hereditary K s)⟩
  inj' := fun _ _ h => subsetCode_injective K (congrArg Subtype.val h)

theorem universeSet_card_ge : 2 ^ Cardinal.mk K ≤ ZFSet.card (universeSet K) := by
  let e : Set K ↪ Shrink (universeSet K) :=
    (subsetsIntoUniverse K).trans (equivShrink (universeSet K)).toEmbedding
  simpa only [Cardinal.mk_set, ZFSet.card] using Cardinal.mk_le_of_injective e.injective

/-- The full cardinal equation used by the pure universe code. -/
theorem universeSet_card [Infinite K] :
    ZFSet.card (universeSet K) = 2 ^ Cardinal.mk K :=
  le_antisymm (universeSet_card_le K) (universeSet_card_ge K)

/-- The higher-type domain K → K has exactly the required size. -/
theorem universeSet_card_eq_function [Infinite K] :
    ZFSet.card (universeSet K) = Cardinal.mk (K → K) := by
  rw [universeSet_card, Cardinal.mk_arrow, Cardinal.lift_id,
    Cardinal.power_self_eq (Cardinal.aleph0_le_mk K)]

/-- An actual equivalence, chosen from the proved cardinal equality. -/
def codeEquiv [Infinite K] : (K → K) ≃ Shrink (universeSet K) :=
  Classical.choice (Cardinal.eq.mp (universeSet_card_eq_function K).symm)

/-- The size calculation gives a presentation on the exact function domain. -/
def presentationEquiv [Infinite K] : (K → K) ≃ (universeSet K : Set ZFSet.{u}) :=
  (codeEquiv K).trans (equivShrink (universeSet K)).symm

def present [Infinite K] (x : K → K) : ZFSet.{u} :=
  (presentationEquiv K x).1

theorem present_injective [Infinite K] : Function.Injective (present K) := by
  intro x y h
  apply (presentationEquiv K).injective
  exact Subtype.ext h

theorem present_mem [Infinite K] (x : K → K) : present K x ∈ universeSet K :=
  (presentationEquiv K x).2

theorem present_hereditary [Infinite K] (x : K → K) :
    HereditarilySmall K (present K x) :=
  (mem_universeSet K _).1 (present_mem K x)

theorem present_surjective [Infinite K] (z : ZFSet.{u}) (hz : z ∈ universeSet K) :
    ∃ x : K → K, present K x = z := by
  obtain ⟨x, hx⟩ := (presentationEquiv K).surjective ⟨z, hz⟩
  exact ⟨x, congrArg Subtype.val hx⟩

/-- The concrete membership relation that will be interpreted by a crisp term. -/
def codeRelation [Infinite K] (x y : K → K) : Prop := present K x ∈ present K y

theorem codeRelation_wellFounded [Infinite K] : WellFounded (codeRelation K) :=
  InvImage.wf (present K) ZFSet.mem_wf

theorem codeRelation_extensional [Infinite K] :
    MaxAtomicityMostowski.Extensional (codeRelation K) := by
  intro x y h
  apply present_injective K
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    have hzM := universeSet_transitive K _ (present_mem K x) z hz
    obtain ⟨v, hv⟩ := present_surjective K z hzM
    rw [← hv] at hz ⊢
    exact (h v).1 hz
  · intro hz
    have hzM := universeSet_transitive K _ (present_mem K y) z hz
    obtain ⟨v, hv⟩ := present_surjective K z hzM
    rw [← hv] at hz ⊢
    exact (h v).2 hz

theorem codeRelation_rows [Infinite K] : RowsSmall K (codeRelation K) := by
  intro x
  obtain ⟨e⟩ := ZFSet.Hereditarily.self (present_hereditary K x)
  let j : {y : K → K // codeRelation K y x} ↪
      {z : ZFSet.{u} // z ∈ present K x} :=
    { toFun := fun y => ⟨present K y.1, y.2⟩
      inj' := by
        intro y z hyz
        apply Subtype.ext
        have hval : present K y.1 = present K z.1 :=
          congrArg (fun w : {w : ZFSet.{u} // w ∈ present K x} => w.1) hyz
        exact present_injective K hval }
  exact ⟨j.trans e⟩

theorem codeRelation_fills [Infinite K] : FillsSmall K (codeRelation K) := by
  intro X hX
  obtain ⟨e⟩ := hX
  let f : X → ZFSet.{u} := fun x => present K x.1
  have hf : HereditarilySmall K (ZFSet.range f) :=
    hereditary_range K e f (fun x => present_hereditary K x.1)
  obtain ⟨x, hx⟩ := present_surjective K (ZFSet.range f)
    ((mem_universeSet K _).2 hf)
  refine ⟨x, ?_⟩
  intro y
  change present K y ∈ present K x ↔ y ∈ X
  rw [hx, ZFSet.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    have hvy : v.1 = y := present_injective K hv
    exact hvy ▸ v.2
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

end

end Classicism.Meta.Research.MaxAtomicityHereditaryUniverse

#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.hereditary_has_tree
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.mem_universeSet
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.smallTree_card_le
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.universeSet_card
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.codeEquiv
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.codeRelation_wellFounded
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.codeRelation_extensional
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.codeRelation_rows
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryUniverse.codeRelation_fills
