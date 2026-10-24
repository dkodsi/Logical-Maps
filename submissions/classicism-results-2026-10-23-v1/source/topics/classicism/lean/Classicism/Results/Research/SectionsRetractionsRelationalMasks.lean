import Classicism.Results.Research.SectionsRetractionsMasks

/-!
# Relational-output masks

Direct source: `research/2026-10-22/notes/choice-uniformization.md`, §11,
Theorem 17 (`misc`, original research, 22 October 2026; unpaginated).
Existence of the argument tuple is explicit. C proves it at every admitted
tuple; the shallow marker `Ty` alone must not be treated as inhabitation.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def slots {ν : Type} [Ty ν] (q s : ν → Prop) (r : Prop) : ν → Prop :=
  fun u => (r = True ∧ s u) ∨ (r ≠ True ∧ q u)

theorem slots_false {ν : Type} [Ty ν] (q s : ν → Prop) : slots q s False = q :=
  funext fun u => slotsT_false (q u) (s u)

theorem slots_true {ν : Type} [Ty ν] (q s : ν → Prop) : slots q s True = s :=
  funext fun u => slotsT_true (q u) (s u)

def mask {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (H : Prop → ν → Prop) (r : Prop) : ν → Prop :=
  fun u => H r u ∧ (r = True → P (H False))

theorem mask_false {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (H : Prop → ν → Prop) : mask P H False = H False :=
  funext fun u => propext
    ⟨And.left, fun h => ⟨h, fun he => (Eq.mpr he trivial).elim⟩⟩

theorem mask_coext {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (H : Prop → ν → Prop) : P (H False) → mask P H ≡ H :=
  fun hp r u => ⟨And.left, fun h => ⟨h, fun _ => hp⟩⟩

theorem mask_identity {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (hp : ∀ q, □ (P q)) (H : Prop → ν → Prop) : mask P H = H :=
  intensionality _ _ (modal_K _ _ (nec% (mask_coext P H)) (hp (H False)))

theorem mask_surjective_all {ν : Type} [Ty ν] (u : ν)
    (P : (ν → Prop) → Prop) : Surjective (mask P) → ∀ q, P q := by
  intro hs q
  obtain ⟨H, he⟩ := hs (slots q (fun _ => True))
  have hb : H False = q := (mask_false P H).symm.trans
    ((congrFun he False).trans (slots_false q (fun _ => True)))
  have ht : mask P H True u :=
    (congrFun (congrFun he True) u).mpr (Or.inl ⟨rfl, trivial⟩)
  exact hb ▸ ht.2 rfl

theorem relational_surjectivity_persistence_barcan {ν : Type} [Ty ν] :
    Existence ν → SurjectivityPersists (Prop → ν → Prop) (Prop → ν → Prop) →
      Barcan (ν → Prop) := by
  intro hex ps P hp
  obtain ⟨u, _⟩ := hex
  have hs : Surjective (mask P) := fun H => ⟨H, mask_identity P hp H⟩
  exact modal_K _ _ (nec% (mask_surjective_all u P)) (ps (mask P) hs)

theorem relational_strong_sections_barcan {ν : Type} [Ty ν] :
    Existence ν → StrongRightSplitting (Prop → ν → Prop) (Prop → ν → Prop) →
      Barcan (ν → Prop) := fun hex sr =>
  relational_surjectivity_persistence_barcan hex (strong_sections_surjectivity sr)

theorem mask_slots {ν : Type} [Ty ν] (P : (ν → Prop) → Prop) (q s : ν → Prop) :
    mask P (slots q s) = slots q (fun u => s u ∧ P q) :=
  funext fun r => funext fun u => propext (by
    change (slots q s r u ∧ (r = True → P (slots q s False))) ↔
      ((r = True ∧ (s u ∧ P q)) ∨ (r ≠ True ∧ q u))
    rw [slots_false]
    exact ⟨fun h => h.1.elim (fun hs => Or.inl ⟨hs.1, hs.2, h.2 hs.1⟩)
        (fun hq => Or.inr hq),
      fun h => h.elim
        (fun hs => ⟨Or.inl ⟨hs.1, hs.2.1⟩, fun _ => hs.2.2⟩)
        (fun hq => ⟨Or.inr hq, fun he => (hq.1 he).elim⟩)⟩)

theorem mask_collapses {ν : Type} [Ty ν] (P : (ν → Prop) → Prop) (q : ν → Prop) :
    mask P (slots q (fun _ => ¬ P q)) = mask P (slots q (fun _ => False)) := by
  rw [mask_slots, mask_slots]
  exact congrArg (slots q) (funext fun _ =>
    propext ⟨fun h => (h.1 h.2).elim, fun h => h.1.elim⟩)

theorem mask_injective_all {ν : Type} [Ty ν] (u : ν)
    (P : (ν → Prop) → Prop) : Injective (mask P) → ∀ q, P q := by
  intro hi q
  have he : (fun _ : ν => ¬ P q) = (fun _ : ν => False) :=
    (slots_true q (fun _ => ¬ P q)).symm.trans
      ((congrFun (hi _ _ (mask_collapses P q)) True).trans
        (slots_true q (fun _ => False)))
  have hn : (¬ P q) = False := congrFun he u
  exact (em (P q)).elim id (fun h => (Eq.mp hn h).elim)

theorem relational_injectivity_persistence_barcan {ν : Type} [Ty ν] :
    Existence ν → InjectivityPersists (Prop → ν → Prop) (Prop → ν → Prop) →
      Barcan (ν → Prop) := by
  intro hex pi P hp
  obtain ⟨u, _⟩ := hex
  have hi : Injective (mask P) := fun H K he =>
    (mask_identity P hp H).symm.trans (he.trans (mask_identity P hp K))
  exact modal_K _ _ (nec% (mask_injective_all u P)) (pi (mask P) hi)

end Classicism.Research.Splitting
