import Classicism.Semantics.Research.CentralSupportedProduct
import Classicism.Semantics.FullModels

/-!
# Fresh-coordinate obstructions in the supported product

New research, `followup/central-map.md`, §3. A diagonal supplies a coordinate
outside every countable support. The killing arrow preserves an arbitrary
given actual truth while permanently falsifying another actual truth.
The final theorem concerns the library's quoted Actuality sentence itself.
Uncompiled author draft, 22 October 2026; no verification claim.
-/

namespace Classicism.Meta.Intensional.Central.Product
open CategoryTheory

variable (I L : Type)

noncomputable abbrev proposition := (domain I L Ty.t).obj (star I L)

def value (p : proposition I L) (h : Arrow I L) : Prop :=
  (⟨star I L, PUnit.unit, h⟩ :
    Σ V, (arguments I L .t).obj V × ((star I L) ⟶ V)) ∈ p.1

noncomputable def coordinateTruth (j : I) : proposition I L :=
  ⟨{z | z.2.2 j = 1}, by
    apply supported_of_profile I L (ρ := .t) (W := star I L) (Set.countable_singleton j)
    intro V a h k hk
    change h j = 1 ↔ k j = 1
    rw [hk j (by simp)]⟩

theorem coordinateTruth_actual (j : I) : value I L (coordinateTruth I L j) 1 := rfl

noncomputable def spike (j : I) (a : L) : Arrow I L := by
  classical
  exact fun i => if i = j then Word.of a else 1

theorem spike_at (j : I) (a : L) : spike I L j a j = Word.of a := by
  classical
  simp [spike]

theorem spike_away (j i : I) (a : L) (hi : i ≠ j) : spike I L j a i = 1 := by
  classical
  simp [spike, hi]

theorem spike_agrees {S : Set I} {j : I} (hj : j ∉ S) (a : L) :
    ∀ i ∈ S, spike I L j a i = (1 : Arrow I L) i := by
  intro i hi
  exact spike_away I L j i a (fun e => hj (e ▸ hi))

theorem coordinateTruth_killed (j : I) (a : L) (k : Arrow I L) :
    ¬ value I L (coordinateTruth I L j) (k * spike I L j a) := by
  intro h
  change k j * spike I L j a j = 1 at h
  rw [spike_at] at h
  have e := congrArg Word.length h
  simp only [Word.length_mul, Word.length_of, Word.length_one,
    Nat.add_one_ne_zero] at e

theorem fresh_coordinate (S : Set (Set Nat)) (hS : S.Countable) :
    ∃ j : Set Nat, j ∉ S := by
  classical
  let f := Set.enumerateCountable hS (∅ : Set Nat)
  let d : Set Nat := {n | n ∉ f n}
  refine ⟨d, fun hd => ?_⟩
  obtain ⟨n, hn⟩ := Set.subset_range_enumerate hS (∅ : Set Nat) hd
  change f n = d at hn
  have diag : n ∈ d ↔ n ∉ d := by
    change (n ∉ f n) ↔ (n ∉ d)
    rw [hn]
  by_cases h : n ∈ d
  · exact (diag.mp h) h
  · exact h (diag.mpr h)

/-- The stronger negative witness used for both Actuality and Vicinity. -/
theorem kill_another_truth (a : L) (p : proposition (Set Nat) L)
    (hp : value (Set Nat) L p 1) :
    ∃ (q : proposition (Set Nat) L) (h : Arrow (Set Nat) L),
      value (Set Nat) L q 1 ∧ value (Set Nat) L p h ∧
      ∀ k : Arrow (Set Nat) L, ¬ value (Set Nat) L q (k * h) := by
  obtain ⟨S, hS, hSup⟩ := profile_support (Set Nat) L p
  obtain ⟨j, hj⟩ := fresh_coordinate S hS
  refine ⟨coordinateTruth (Set Nat) L j, spike (Set Nat) L j a,
    coordinateTruth_actual (Set Nat) L j, ?_, coordinateTruth_killed (Set Nat) L j a⟩
  exact (hSup (star _ _) PUnit.unit (spike (Set Nat) L j a) (1 : Arrow (Set Nat) L)
    (spike_agrees (Set Nat) L hj a)).2 hp

theorem no_least_truth (a : L) :
    ¬ ∃ p : proposition (Set Nat) L, value (Set Nat) L p 1 ∧
      ∀ q : proposition (Set Nat) L, value (Set Nat) L q 1 → p.1 ⊆ q.1 := by
  rintro ⟨p, hp, hleast⟩
  obtain ⟨q, h, hq, hph, hkill⟩ := kill_another_truth L a p hp
  have hq' : value (Set Nat) L q h := hleast q hq hph
  exact hkill 1 (by simpa only [one_mul] using hq')

noncomputable abbrev pureModel : Premodel Signature.pure (World I L) :=
  model I L (fun c => nomatch c)

/-- The library's exact Actuality formula, not just an external order claim. -/
theorem not_holds_actuality (a : L) :
    ¬ (pureModel (Set Nat) L).HoldsSentence P.Actuality.quoted := by
  let B := pureModel (Set Nat) L
  have M : B.IsModel := model_isModel (Set Nat) L _
  change ¬ B.Holds (𝟙 B.W₀) P.Actuality.quoted .nil
  simp only [P.Actuality.quoted, B.holds_exists M,
    B.holds_conj M, B.holds_forall M, B.holds_imp M, Premodel.holds_var,
    B.holds_eq M, Premodel.sem_var, B.sem_disj M, IEnv.get]
  rintro ⟨p, hp, hleast⟩
  obtain ⟨q, h, hq, hph, hkill⟩ := kill_another_truth L a p hp
  have e := hleast q hq
  have hmem : (⟨star (Set Nat) L, PUnit.unit, h⟩ : Tuple B.inner .t B.W₀) ∈
      B.incl .t B.W₀ p ∪ B.incl .t B.W₀ q := Or.inl hph
  have hq' : value (Set Nat) L q h := by
    change (⟨star (Set Nat) L, PUnit.unit, h⟩ : Tuple B.inner .t B.W₀) ∈
      B.incl .t B.W₀ q
    rw [e]
    exact hmem
  exact hkill 1 (by simpa only [one_mul] using hq')

end Classicism.Meta.Intensional.Central.Product
