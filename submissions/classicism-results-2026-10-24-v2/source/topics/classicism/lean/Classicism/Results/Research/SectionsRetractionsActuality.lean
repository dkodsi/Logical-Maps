import Classicism.Results.Research.SectionsRetractionsMasks
import Classicism.Results.Research.CanonicalEvaluator

/-!
# Actuality and one section instance yield bivalent evaluation

Direct source: `research/2026-10-22/notes/functional-choice-by-sections.md`,
§2 (`misc`, original research, 22 October 2026; unpaginated).
Only sections of actual surjections `tt -> t` are used. No evaluator or
operation selecting the current truth value is assumed in proving surjectivity.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def escape (w R : Prop) (H : Prop → Prop) : Prop :=
  (w ∧ ◇ (R ∧ H True)) ∨ (¬ w ∧ H False)

theorem escape_slots_true (w R q : Prop) :
    escape w R (slotsT q True) = ((w ∧ ◇ R) ∨ (¬ w ∧ q)) := by
  unfold escape
  rw [slotsT_true, slotsT_false, and_true_eq]

theorem escape_slots_false (w R q : Prop) :
    escape w R (slotsT q False) = (¬ w ∧ q) := by
  have hd : (◇ False) = False := propext ⟨fun h => h rfl, fun h => h.elim⟩
  unfold escape
  rw [slotsT_true, slotsT_false, and_false_eq, hd, and_false_eq, false_or_eq]

theorem escape_true_coext (w d q : Prop) : (w → q) → (w → d) →
    ((w ∧ d) ∨ (¬ w ∧ q)) ≡ q := fun hwq hwd =>
  ⟨fun h => h.elim (fun h => hwq h.1) And.right,
   fun hq => (em w).elim (fun hw => Or.inl ⟨hw, hwd hw⟩)
     (fun hn => Or.inr ⟨hn, hq⟩)⟩

theorem escape_false_coext (w q : Prop) : (w → ¬ q) → (¬ w ∧ q) ≡ q :=
  fun hn => ⟨And.right, fun hq => ⟨fun hw => hn hw hq, hq⟩⟩

theorem escape_surjective (w R : Prop) (hw : ActualWorld w) (hd : ◇ R) :
    Surjective (escape w R) := by
  intro q
  exact (em q).elim
    (fun hq => ⟨slotsT q True, (escape_slots_true w R q).trans
      (intensionality _ _ (modal_K _ _
        (modal_K _ _ (nec% (escape_true_coext w (◇ R) q))
          ((le_iff_prop w q).mp (hw.2 q hq)))
        ((le_iff_prop w (◇ R)).mp (hw.2 (◇ R) hd))))⟩)
    (fun hn => ⟨slotsT q False, (escape_slots_false w R q).trans
      (intensionality _ _ (modal_K _ _ (nec% (escape_false_coext w q))
        ((le_iff_prop w (¬ q)).mp (hw.2 (¬ q) hn))))⟩)

theorem not_possible_eq_false (w : Prop) : ¬ ◇ w → w = False :=
  fun hn => (em (w = False)).elim id (fun he => (hn he).elim)

theorem escape_guard_identity (w : Prop) (g : Prop → Prop → Prop) :
    ((¬ ◇ w) ∧ g w True) = ((¬ ◇ w) ∧ g False True) :=
  propext ⟨fun h => ⟨h.1, (not_possible_eq_false w h.1) ▸ h.2⟩,
    fun h => ⟨h.1, (not_possible_eq_false w h.1).symm ▸ h.2⟩⟩

theorem escape_section_impossible (w : Prop) (hw : w)
    (g : Prop → Prop → Prop) :
    RightInverse (escape w (¬ ◇ w)) g → False := by
  intro hg
  have ht : escape w (¬ ◇ w) (g w) := (hg w).mpr hw
  have hd : ◇ ((¬ ◇ w) ∧ g w True) := ht.elim And.right
    (fun h => (h.1 hw).elim)
  have he : (◇ ((¬ ◇ w) ∧ g w True)) = (◇ ((¬ ◇ w) ∧ g False True)) :=
    congrArg (fun p : Prop => ◇ p) (escape_guard_identity w g)
  exact (hg False).mp (Or.inl ⟨hw, he.mp hd⟩)

theorem section_stabilizes_actual_world (w : Prop) (hw : ActualWorld w)
    (sr : RightSplitting (Prop → Prop) Prop) : □ (◇ w) :=
  (em (□ (◇ w))).elim id fun hn =>
    (sr (escape w (¬ ◇ w))
      (escape_surjective w (¬ ◇ w) hw (dia_not_of_not_box (◇ w) hn))).elim
      fun g hg => (escape_section_impossible w hw.1 g hg).elim

def HasActualEvaluator : Prop := ∃ E : Prop → Prop, ActualEvaluator E

theorem actuality_sections_evaluator :
    Actuality → RightSplitting (Prop → Prop) Prop → HasActualEvaluator := by
  intro act sr
  obtain ⟨w, hw⟩ := act
  exact ⟨worldEvaluator w,
    worldEvaluator_actual w hw (section_stabilizes_actual_world w hw sr)⟩

end Classicism.Research.Splitting
