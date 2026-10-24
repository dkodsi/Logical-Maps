import Classicism.Results.Research.SectionsRetractionsStrong

/-!
# Two-slot masks detect Barcan

Direct source: `research/2026-10-22/notes/choice-uniformization.md`,
§§9,11–12; `reversible-comprehension-and-algebraic-laws.md`, the persistence
arguments (`misc`, original research, 22 October 2026; unpaginated).
This module states the precise truth-value instances; higher-output tuple
instances are separate and are not inferred from these low-type tests.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def slotsT (q s r : Prop) : Prop := (r = True ∧ s) ∨ (r ≠ True ∧ q)

theorem slotsT_false (q s : Prop) : slotsT q s False = q :=
  propext ⟨fun h => h.elim (fun h => (Eq.mpr h.1 trivial).elim) And.right,
    fun h => Or.inr ⟨fun e => Eq.mpr e trivial, h⟩⟩

theorem slotsT_true (q s : Prop) : slotsT q s True = s :=
  propext ⟨fun h => h.elim And.right (fun h => (h.1 rfl).elim),
    fun h => Or.inl ⟨rfl, h⟩⟩

def maskT (P : Prop → Prop) (H : Prop → Prop) (r : Prop) : Prop :=
  H r ∧ (r = True → P (H False))

theorem maskT_false (P H : Prop → Prop) : maskT P H False = H False :=
  propext ⟨And.left, fun h => ⟨h, fun he => (Eq.mpr he trivial).elim⟩⟩

theorem maskT_coext (P H : Prop → Prop) : P (H False) → maskT P H ≡ H :=
  fun hp r => ⟨And.left, fun h => ⟨h, fun _ => hp⟩⟩

theorem maskT_identity (P : Prop → Prop) (hp : ∀ q, □ (P q)) (H : Prop → Prop) :
    maskT P H = H :=
  intensionality _ _ (modal_K _ _ (nec% (maskT_coext P H)) (hp (H False)))

theorem maskT_surjective_all (P : Prop → Prop) : Surjective (maskT P) → ∀ q, P q := by
  intro hs q
  obtain ⟨H, he⟩ := hs (slotsT q True)
  have hb : H False = q := (maskT_false P H).symm.trans
    ((congrFun he False).trans (slotsT_false q True))
  have ht : maskT P H True := (congrFun he True).mpr (Or.inl ⟨rfl, trivial⟩)
  exact hb ▸ ht.2 rfl

theorem maskT_slots (P : Prop → Prop) (q s : Prop) :
    maskT P (slotsT q s) = slotsT q (s ∧ P q) :=
  funext fun r => propext (by
    change (slotsT q s r ∧ (r = True → P (slotsT q s False))) ↔
      ((r = True ∧ (s ∧ P q)) ∨ (r ≠ True ∧ q))
    rw [slotsT_false]
    exact ⟨fun h => h.1.elim (fun hs => Or.inl ⟨hs.1, hs.2, h.2 hs.1⟩)
        (fun hq => Or.inr hq),
      fun h => h.elim
        (fun hs => ⟨Or.inl ⟨hs.1, hs.2.1⟩, fun _ => hs.2.2⟩)
        (fun hq => ⟨Or.inr hq, fun he => (hq.1 he).elim⟩)⟩)

theorem maskT_collapses (P : Prop → Prop) (q : Prop) :
    maskT P (slotsT q (¬ P q)) = maskT P (slotsT q False) := by
  rw [maskT_slots, maskT_slots]
  exact congrArg (slotsT q)
    (propext ⟨fun h => (h.1 h.2).elim, fun h => h.1.elim⟩)

theorem maskT_injective_all (P : Prop → Prop) : Injective (maskT P) → ∀ q, P q := by
  intro hi q
  have he := congrFun (hi _ _ (maskT_collapses P q)) True
  have hn : (¬ P q) = False := (slotsT_true q (¬ P q)).symm.trans
    (he.trans (slotsT_true q False))
  exact (em (P q)).elim id (fun h => (Eq.mp hn h).elim)

theorem truth_surjectivity_persistence_barcan :
    SurjectivityPersists (Prop → Prop) (Prop → Prop) → Barcan Prop := by
  intro ps P hp
  have hs : Surjective (maskT P) := fun H => ⟨H, maskT_identity P hp H⟩
  exact modal_K _ _ (nec% (maskT_surjective_all P)) (ps (maskT P) hs)

theorem truth_injectivity_persistence_barcan :
    InjectivityPersists (Prop → Prop) (Prop → Prop) → Barcan Prop := by
  intro pi P hp
  have hi : Injective (maskT P) := fun H K he =>
    (maskT_identity P hp H).symm.trans (he.trans (maskT_identity P hp K))
  exact modal_K _ _ (nec% (maskT_injective_all P)) (pi (maskT P) hi)

theorem strong_truth_sections_barcan :
    StrongRightSplitting (Prop → Prop) (Prop → Prop) → Barcan Prop :=
  fun sr => truth_surjectivity_persistence_barcan (strong_sections_surjectivity sr)

theorem low_strong_retractions_c5 :
    StrongLeftSplitting Prop (Prop → Prop) →
    StrongLeftSplitting (Prop → Prop) (Prop → Prop) → NecNecessityOfDistinctness Prop :=
  fun sl₀ sl₁ => Proofs.nd_and_bf_imply_necessary_nd
    (truth_retractions_nd (strong_retractions_retractions sl₀))
    (truth_injectivity_persistence_barcan (strong_retractions_injectivity sl₁))

theorem low_persistent_injections_c5 :
    InjectivityPersists Prop (Prop → Prop) →
    InjectivityPersists (Prop → Prop) (Prop → Prop) → NecNecessityOfDistinctness Prop := by
  intro pi₀ pi₁
  have sl₀ : StrongLeftSplitting Prop (Prop → Prop) := fun f hi =>
    ⟨inverseKernelT f, necessary_injection_retraction_t f (pi₀ f hi)⟩
  exact Proofs.nd_and_bf_imply_necessary_nd
    (truth_retractions_nd (strong_retractions_retractions sl₀))
    (truth_injectivity_persistence_barcan pi₁)

end Classicism.Research.Splitting
