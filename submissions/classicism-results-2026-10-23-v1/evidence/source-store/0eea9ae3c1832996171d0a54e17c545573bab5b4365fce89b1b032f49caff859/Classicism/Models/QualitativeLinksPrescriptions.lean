import Classicism.Models.QualitativeLinksBase
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite binary prescriptions by actual qualitative-link collapses

Original formalization (misc), 23 October 2026. This proves the finite
binary-prescription ingredient used in the `tame-rigidity` argument of
`models/symmetric-qualitative-links.yaml` (11 October 2026, unpaginated).
Its source antecedent is the extension construction in the proof of
Proposition 50, p. 26, of Dorr's 30 July 2026 draft. The explicit cutoff
map below proves this particular ingredient directly; it does not claim
the more general extension theorem or any higher-type semantic verdict.
-/

namespace Classicism.Meta.Intensional.QualitativeLinks.Prescriptions

open CategoryTheory
noncomputable section

/-- A bound for every point coordinate occurring in a node. -/
def index : Node → Nat
  | .point n => n
  | .companion n _ => n
  | .link n m _ _ => max n m

theorem finite_index_bound {U : Set Node} (hU : U.Finite) :
    ∃ N : Nat, 2 ≤ N ∧ ∀ z ∈ U, index z < N := by
  obtain ⟨K, hK⟩ := (hU.image index).bddAbove
  refine ⟨max 2 (K + 1), le_max_left _ _, ?_⟩
  intro z hz
  have hk : index z ≤ K := hK ⟨z, hz, rfl⟩
  omega

/-- Collapse the initial segment and shift the untouched tail onto Nat. -/
def pointMap (N n : Nat) : Nat := if n < N then 0 else n - N

@[simp] theorem pointMap_low {N n : Nat} (h : n < N) : pointMap N n = 0 := by
  simp [pointMap, h]

@[simp] theorem pointMap_high (N n : Nat) : pointMap N (N + n) = n := by
  have h : ¬ N + n < N := by omega
  simp [pointMap, h]

/-- Only the collapsed finite region uses the prescribed bits. All
uncollapsed fibres keep their full tail, providing explicit preimages. -/
def prescriptionFn (N : Nat) (U : Set Node) (b : Node → Bool) : Node → Node := by
  classical
  exact fun z => match z with
    | .point n => .point (pointMap N n)
    | .companion n s =>
        if n < N then .companion 0 (if z ∈ U then b z else false)
        else .companion (n - N) s
    | .link n m k _ =>
        if h : pointMap N n ≠ pointMap N m then
          .link (pointMap N n) (pointMap N m) k h
        else .companion (pointMap N n) (if z ∈ U then b z else decide (k % 2 = 1))

theorem prescription_preserves (N : Nat) (U : Set Node) (b : Node → Bool) :
    Preserves (prescriptionFn N U b) := by
  classical
  intro x y z h
  cases h with
  | companion n s =>
      by_cases hn : n < N
      · simpa only [prescriptionFn, if_pos hn, pointMap_low hn] using
          R.companion 0 (if Node.companion n s ∈ U then b (.companion n s) else false)
      · simpa only [prescriptionFn, if_neg hn, pointMap, if_neg hn] using
          R.companion (n - N) s
  | link n m k hnm =>
      simp only [prescriptionFn]
      split
      · exact R.link _ _ _ _
      · rename_i h
        have he : pointMap N n = pointMap N m := not_not.mp h
        rw [← he]
        exact R.companion _ _

/-- Surjectivity uses the untouched translated tail and needs no
finiteness or compatibility assumption on the prescribed set. -/
theorem prescription_surjective (N : Nat) (U : Set Node) (b : Node → Bool) :
    Function.Surjective (prescriptionFn N U b) := by
  classical
  intro z
  cases z with
  | point n =>
      refine ⟨.point (N + n), ?_⟩
      simp [prescriptionFn]
  | companion n s =>
      refine ⟨.companion (N + n) s, ?_⟩
      have h : ¬ N + n < N := by omega
      simp [prescriptionFn, h]
  | link n m k hnm =>
      refine ⟨.link (N + n) (N + m) k (by omega), ?_⟩
      simp [prescriptionFn, hnm]

theorem prescription_collapses {N : Nat} (hN : 2 ≤ N)
    (U : Set Node) (b : Node → Bool) : Collapses (prescriptionFn N U b) := by
  refine ⟨prescription_surjective N U b, prescription_preserves N U b, ?_⟩
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  simp only [prescriptionFn, pointMap_low h0, pointMap_low h1]

theorem prescription_arrow {N : Nat} (hN : 2 ≤ N)
    (U : Set Node) (b : Node → Bool) : Arrow (prescriptionFn N U b) :=
  Or.inr (prescription_collapses hN U b)

theorem prescription_eq {N : Nat} {U : Set Node} {b : Node → Bool} {z : Node}
    (hz : z ∈ U) (hn : Nonpoint z) (hi : index z < N) :
    prescriptionFn N U b z = .companion 0 (b z) := by
  classical
  cases z with
  | point n => exact hn.elim
  | companion n s =>
      have h : n < N := hi
      simp [prescriptionFn, h, hz]
  | link n m k hnm =>
      have hn : n < N := lt_of_le_of_lt (le_max_left n m) hi
      have hm : m < N := lt_of_le_of_lt (le_max_right n m) hi
      simp [prescriptionFn, pointMap_low hn, pointMap_low hm, hz]

/-- Any binary assignment on finitely many nonpoints is realized by a
surjective R-preserving arrow collapsing the distinguished point pair. -/
theorem finite_prescription {U : Set Node} (hU : U.Finite)
    (hV : ∀ z ∈ U, Nonpoint z) (b : Node → Bool) :
    ∃ f : Node → Node, Collapses f ∧ ∀ z ∈ U, f z = .companion 0 (b z) := by
  obtain ⟨N, hN, hbound⟩ := finite_index_bound hU
  exact ⟨prescriptionFn N U b, prescription_collapses hN U b,
    fun z hz => prescription_eq hz (hV z hz) (hbound z hz)⟩

/-- The same realization packaged as an arrow of the actual Base 3 category. -/
theorem finite_prescription_arrow {U : Set Node} (hU : U.Finite)
    (hV : ∀ z ∈ U, Nonpoint z) (b : Node → Bool) :
    ∃ f : star ⟶ star, Collapses (FunCat.fn f) ∧
      ∀ z ∈ U, FunCat.fn f z = .companion 0 (b z) := by
  obtain ⟨f, hf, hp⟩ := finite_prescription hU hV b
  exact ⟨FunCat.arr f (Or.inr hf), hf, hp⟩

end
end Classicism.Meta.Intensional.QualitativeLinks.Prescriptions
