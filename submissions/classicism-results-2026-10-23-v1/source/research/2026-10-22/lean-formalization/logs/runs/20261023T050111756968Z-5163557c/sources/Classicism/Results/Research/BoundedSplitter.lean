import Classicism.Results.Records.Lattice
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

/-!
# The bounded splitter obstruction

Direct source: `research/2026-10-22/followup/max-atomicity-rigid-selector.md`, §1.
This module proves only the elementary obstruction, not the proposed model/coding
argument or the claimed incompatibility with pure Maximalism. All premises are
unboxed. In particular no necessity of Atomicity is used.
-/

namespace Classicism.Research.BoundedSplitter
open Classicism.P Classicism.Paper

/-- A specified operation splits every nonzero proposition below `b`. -/
def Split (b : Prop) (F : Prop → Prop) : Prop :=
  ∀ p : Prop, (p ≠ False ∧ p ≤ b) →
    ((p ∧ F p) ≠ False ∧ (p ∧ ¬ F p) ≠ False)

/-- A current true proposition is nonzero, so the splitting assertion applies. -/
theorem split_at_true (b : Prop) (F : Prop → Prop) (p : Prop) :
    p ≤ b → (p → Split b F) →
      p → ((p ∧ F p) ≠ False ∧ (p ∧ ¬ F p) ≠ False) :=
  fun hpb hs hp => hs hp p ⟨dia_intro p hp, hpb⟩

/-- Positive containment kills the negative part, by a closed tautology under `K`. -/
theorem negative_part_zero (p q : Prop) (h : p ≤ q) : (p ∧ ¬ q) = False :=
  modalized_fregean _ _ (modal_K _ _
    (nec% (fun (hpq : p → q) =>
      (show (p ∧ ¬ q) ↔ False from
        ⟨fun hp => hp.2 (hpq hp.1), fun hf => hf.elim⟩)))
    ((le_iff_prop p q).1 h))

/-- Negative containment kills the positive part. -/
theorem positive_part_zero (p q : Prop) (h : p ≤ ¬ q) : (p ∧ q) = False :=
  modalized_fregean _ _ (modal_K _ _
    (nec% (fun (hpq : p → ¬ q) =>
      (show (p ∧ q) ↔ False from
        ⟨fun hp => hpq hp.1 hp.2, fun hf => hf.elim⟩)))
    ((le_iff_prop p (¬ q)).1 h))

/-- The region in which the bound and its splitting assertion hold is itself split.
This is a theorem of bare C; neither BF nor Atomicity occurs in the proof. -/
theorem split_guard (b : Prop) (F : Prop → Prop) : Split (b ∧ Split b F) F := by
  intro p hp
  have hpb : p ≤ b := le_trans_prop _ _ _ hp.2 (and_le_left_prop b (Split b F))
  have hps : p ≤ Split b F :=
    le_trans_prop _ _ _ hp.2 (and_le_right_prop b (Split b F))
  have hparts : □ (p → ((p ∧ F p) ≠ False ∧ (p ∧ ¬ F p) ≠ False)) :=
    modal_K _ _ (modal_K _ _ (nec% (split_at_true b F p))
      (box_le_prop p b hpb)) ((le_iff_prop _ _).1 hps)
  have hpossible : ◇ ((p ∧ F p) ≠ False ∧ (p ∧ ¬ F p) ≠ False) :=
    dia_mono _ _ hparts hp.1
  exact ⟨ne_of_dia_ne _ _ (dia_mono _ _
      (nec% (fun (h : (p ∧ F p) ≠ False ∧ (p ∧ ¬ F p) ≠ False) => h.1)) hpossible),
    ne_of_dia_ne _ _ (dia_mono _ _
      (nec% (fun (h : (p ∧ F p) ≠ False ∧ (p ∧ ¬ F p) ≠ False) => h.2)) hpossible)⟩

/-- No current atom lies below a bound split by a specified operation. -/
theorem split_excludes_atom (b : Prop) (F : Prop → Prop) (w : Prop)
    (hs : Split b F) (hw : Atom w) : ¬ w ≤ b := fun hwb =>
  have hparts := hs w ⟨fun e => not_le_neg_of_atom hw (le_neg_of_eq_false w e), hwb⟩
  (atom_le_or_le_neg w (F w) hw).elim
    (fun h => hparts.2 (negative_part_zero w (F w) h))
    (fun h => hparts.1 (positive_part_zero w (F w) h))

/-- Atomicity makes every currently split bound zero. -/
theorem atomicity_split_bound_zero (at_ : AtomicityT) (b : Prop) (F : Prop → Prop)
    (hs : Split b F) : b = False :=
  (at_ b).elim (eq_false_of_le_neg b)
    (fun h => h.elim fun w hw => (split_excludes_atom b F w hs hw.1 hw.2).elim)

/-- The stronger zero identity: Atomicity kills the entire guarded region. -/
theorem atomicity_guard_zero (at_ : AtomicityT) (b : Prop) (F : Prop → Prop) :
    (b ∧ Split b F) = False :=
  atomicity_split_bound_zero at_ (b ∧ Split b F) F (split_guard b F)

/-- A nonzero guarded region is an explicit obstruction to unboxed Atomicity. -/
theorem nonzero_guard_excludes_atomicity (b : Prop) (F : Prop → Prop)
    (h : (b ∧ Split b F) ≠ False) : ¬ AtomicityT :=
  fun at_ => h (atomicity_guard_zero at_ b F)

end Classicism.Research.BoundedSplitter

-- Gates and object-language derivations are deliberately kept local to this new
-- module. Their successful execution, not the presence of these commands, is the
-- certification criterion. No generated database statements are changed here.
#classicism_check Classicism.Research.BoundedSplitter.split_at_true
  Classicism.Research.BoundedSplitter.negative_part_zero
  Classicism.Research.BoundedSplitter.positive_part_zero
  Classicism.Research.BoundedSplitter.split_guard
  Classicism.Research.BoundedSplitter.split_excludes_atom
  Classicism.Research.BoundedSplitter.atomicity_split_bound_zero
  Classicism.Research.BoundedSplitter.atomicity_guard_zero
  Classicism.Research.BoundedSplitter.nonzero_guard_excludes_atomicity
#classicism_types Classicism.Research.BoundedSplitter.split_at_true
  Classicism.Research.BoundedSplitter.negative_part_zero
  Classicism.Research.BoundedSplitter.positive_part_zero
  Classicism.Research.BoundedSplitter.split_guard
  Classicism.Research.BoundedSplitter.split_excludes_atom
  Classicism.Research.BoundedSplitter.atomicity_split_bound_zero
  Classicism.Research.BoundedSplitter.atomicity_guard_zero
  Classicism.Research.BoundedSplitter.nonzero_guard_excludes_atomicity
#classicism_derive Classicism.Research.BoundedSplitter.split_guard
  Classicism.Research.BoundedSplitter.split_excludes_atom
  Classicism.Research.BoundedSplitter.atomicity_split_bound_zero
  Classicism.Research.BoundedSplitter.atomicity_guard_zero
  Classicism.Research.BoundedSplitter.nonzero_guard_excludes_atomicity
