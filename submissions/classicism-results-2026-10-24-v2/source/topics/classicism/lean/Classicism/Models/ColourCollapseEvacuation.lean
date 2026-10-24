import Classicism.Models.ColourCollapseUnary

/-!
# Finite evacuation and return in the exact colour-collapse category

Original argument (misc), 23 October 2026. Direct source:
research/2026-10-23/colour-collapse-higher-power.md, section 5
(unpaginated). A finite support can be moved to fresh uncoloured points
outside a fixed smaller support, and returned by an allowed B-endomorphism.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

/-- Evacuate the part of a finite support outside `N` to uncoloured points,
then return the whole support by a colour-preserving endomorphism at B.
Both arrows are actual globally surjective arrows of the fixed category. -/
theorem evacuate_return {N S : Set Nat} (hS : S.Finite) (hNS : N ⊆ S) :
    ∃ (u : A ⟶ A) (v : B ⟶ B),
      (∀ n ∈ N, FunCat.fn u n = n) ∧
      (∀ s ∈ S, colored B (FunCat.fn u s) → FunCat.fn u s ∈ N) ∧
      (∀ s ∈ S, (FunCat.fn v : Nat → Nat) ((FunCat.fn u : Nat → Nat) s) = s) ∧
      (∀ n ∈ N, FunCat.fn v n = n) := by
  classical
  obtain ⟨b, hb⟩ := hS.bddAbove
  let f : Nat → Nat := fun s => if s ∈ N then s else 2 * (b + s + 1) + 1
  let q : Nat → Nat := fun y => if y ≤ b then y else (y - (2 * b + 3)) / 2
  have hqf : ∀ s ∈ S, q (f s) = s := by
    intro s hs
    by_cases hn : s ∈ N
    · have hsb : s ≤ b := hb hs
      simp only [f, if_pos hn, q, if_pos hsb]
    · have hlarge : ¬ 2 * (b + s + 1) + 1 ≤ b := by omega
      simp only [f, if_neg hn, q, if_neg hlarge]
      omega
  have hfc : ∀ s ∈ S, colored B (f s) → f s ∈ N := by
    intro s _ hc
    by_cases hn : s ∈ N
    · simpa only [f, if_pos hn] using hn
    · change (f s) % 2 = 0 at hc
      simp only [f, if_neg hn] at hc
      omega
  obtain ⟨u, hu⟩ := extend_finite (W := A) (V := A) (Nat.le_refl _) hS f
    (fun _ _ hc => hc.elim)
  have hufix : ∀ n ∈ N, FunCat.fn u n = n := by
    intro n hn
    rw [hu n (hNS hn)]
    exact if_pos hn
  have hqc : ∀ y ∈ (FunCat.fn u : Nat → Nat) '' S,
      colored B y → colored B (q y) := by
    rintro y ⟨s, hs, rfl⟩
    rw [hu s hs, hqf s hs]
    intro hc
    by_cases hn : s ∈ N
    · simpa only [f, if_pos hn] using hc
    · change (f s) % 2 = 0 at hc
      simp only [f, if_neg hn] at hc
      omega
  obtain ⟨v, hv⟩ := extend_finite (W := B) (V := B) (Nat.le_refl _)
    (hS.image (FunCat.fn u : Nat → Nat)) q hqc
  have hreturn : ∀ s ∈ S,
      (FunCat.fn v : Nat → Nat) ((FunCat.fn u : Nat → Nat) s) = s := by
    intro s hs
    rw [hv ((FunCat.fn u : Nat → Nat) s) ⟨s, hs, rfl⟩, hu s hs, hqf s hs]
  refine ⟨u, v, hufix, ?_, hreturn, ?_⟩
  · intro s hs hc
    rw [hu s hs]
    exact hfc s hs (by simpa only [hu s hs] using hc)
  · intro n hn
    simpa only [hufix n hn] using hreturn n (hNS hn)

end
end Classicism.Meta.Intensional.ColourCollapse
