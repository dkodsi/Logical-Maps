import Classicism.Results.Research.MaxAtomicityJechShelahTrees
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-!
# The finite counting step in slalom thinning

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 752–754,
the finite-color thinning in the local slalom argument. The exact formulas,
embedding-valued pigeonhole lemma, and Lean proofs here are original
transcription (misc, 23 October 2026).

Colors record every bounded coordinate below m, which is stronger than recording
only coordinates in A below m. Their cardinality is exactly P_m by the actual
growth recurrence. Pigeonhole produces an injective selection of P_m^n source
indices of one common color. The positivity premise is explicit, including
the n=0 case; the tree growth sequence supplies it.

This is only the finite combinatorial step. It does not assume or prove fusion,
name decisions, local slalom capture, cylinder identification, or rigidity.
The designated serial checker owns compilation and axiom inspection.
-/

namespace Classicism.Meta.Research.MaxAtomicitySlalomThinning

open scoped BigOperators
open MaxAtomicityJechShelahTrees

/-- A pigeonhole conclusion with an actual injective enumeration of the chosen
fiber, rather than only an inequality about its cardinality. -/
theorem monochromatic_embedding {S C : Type*} [Fintype S] [Fintype C] [Nonempty C]
    (z : S → C) (r : ℕ) (hcap : Fintype.card C * r ≤ Fintype.card S) :
    ∃ c : C, ∃ e : Fin r ↪ S, ∀ i, z (e i) = c := by
  classical
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card z hcap
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := Finset.univ.filter (fun a : S => z a = c))
    (by simpa only [Fintype.card_fin] using hc)
  refine ⟨c, e, ?_⟩
  intro i
  exact (Finset.mem_filter.mp (he ⟨i, rfl⟩)).2

/-- At most P colors among P^(n+1) indices leave P^n indices of one color.
Nonemptiness of the color type follows from z and P>0; it is not assumed. -/
theorem thin_power {C : Type*} [Fintype C] (P n : ℕ) (hP : 0 < P)
    (z : Fin (P ^ (n + 1)) → C) (hcard : Fintype.card C ≤ P) :
    ∃ c : C, ∃ e : Fin (P ^ n) ↪ Fin (P ^ (n + 1)), ∀ i, z (e i) = c := by
  letI : Nonempty C := ⟨z ⟨0, pow_pos hP (n + 1)⟩⟩
  apply monochromatic_embedding z (P ^ n)
  calc
    Fintype.card C * P ^ n ≤ P * P ^ n := Nat.mul_le_mul_right _ hcard
    _ = P ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
    _ = Fintype.card (Fin (P ^ (n + 1))) := by simp only [Fintype.card_fin]

/-- The product identity uses the concrete recurrence, including P₀=N₀=1. -/
theorem prod_growthN (m : ℕ) :
    (∏ k ∈ Finset.range m, growthN k) = growthP m := by
  induction m with
  | zero => simp only [Finset.range_zero, Finset.prod_empty, growthP_zero]
  | succ m ih => rw [Finset.prod_range_succ, ih, growthP_succ]

/-- A complete vector of possible values of the bounded name below m. -/
abbrev Color (m : ℕ) := ∀ k : Fin m, Fin (growthN k.val)

theorem card_color (m : ℕ) : Fintype.card (Color m) = growthP m := by
  calc
    Fintype.card (Color m) = ∏ k : Fin m, growthN k.val := by
      simp only [Color, Fintype.card_pi, Fintype.card_fin]
    _ = ∏ k ∈ Finset.range m, growthN k := Fin.prod_univ_eq_prod_range growthN m
    _ = growthP m := prod_growthN m

/-- Direct instantiation at the branching/color bound used in the JS stage. -/
theorem thin_growth (m n : ℕ)
    (z : Fin (growthP m ^ (n + 1)) → Color m) :
    ∃ c : Color m, ∃ e : Fin (growthP m ^ n) ↪ Fin (growthP m ^ (n + 1)),
      ∀ i, z (e i) = c :=
  thin_power (growthP m) n (growth_pos m).1 z (card_color m).le

/-- Coordinatewise form for use after the selected successor subtrees have
decided their respective finite vectors of name values. -/
theorem thin_growth_coordinates (m n : ℕ)
    (z : Fin (growthP m ^ (n + 1)) → Color m) :
    ∃ c : Color m, ∃ e : Fin (growthP m ^ n) ↪ Fin (growthP m ^ (n + 1)),
      ∀ i (k : Fin m), z (e i) k = c k := by
  obtain ⟨c, e, he⟩ := thin_growth m n z
  exact ⟨c, e, fun i k => congrFun (he i) k⟩

end Classicism.Meta.Research.MaxAtomicitySlalomThinning

#print axioms Classicism.Meta.Research.MaxAtomicitySlalomThinning.monochromatic_embedding
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomThinning.thin_power
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomThinning.prod_growthN
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomThinning.card_color
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomThinning.thin_growth
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomThinning.thin_growth_coordinates
