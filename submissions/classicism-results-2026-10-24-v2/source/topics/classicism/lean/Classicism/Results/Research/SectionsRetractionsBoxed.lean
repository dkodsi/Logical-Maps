import Classicism.Results.Research.SectionsRetractionsCharacterizations

/-!
# Boxed splitting decompositions

Direct source: `research/2026-10-22/notes/functional-choice-by-sections.md`,
§§1,4, and `notes/choice-uniformization.md`, §12 (misc; unpaginated).
Every necessitation below is of a closed implication with its premises
discharged. No unboxed optional assumption is necessitated.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def NecRightSplitting (A B : Type) [Rel A] [Rel B] : Prop := □ (RightSplitting A B)
def NecLeftSplitting (A B : Type) [Rel A] [Rel B] : Prop := □ (LeftSplitting A B)

theorem necessary_choice_actuality : NecFunctionalChoice Prop Prop → NecActuality :=
  modal_K _ _ (nec% functional_choice_actuality)

theorem necessary_plenitude_actuality : NecPlenitude Prop Prop → NecActuality :=
  modal_K _ _ (nec% plenitude_actuality)

theorem necessary_choice_sections {A B : Type} [Rel A] [Rel B] :
    NecFunctionalChoice B A → NecRightSplitting A B :=
  modal_K _ _ (nec% (functional_choice_sections (A := A) (B := B)))

theorem necessary_plenitude_retractions {A B : Type} [Rel A] [Rel B] :
    NecPlenitude B A → NecLeftSplitting A B :=
  modal_K _ _ (nec% (plenitude_retractions (A := A) (B := B)))

theorem necessary_actuality_sections_choice {ν σ : Type} [Ty ν] [Ty σ] :
    NecActuality → NecRightSplitting (Prop → Prop) Prop →
    NecRightSplitting (Prop → σ → (ν → Prop) → Prop) (σ → (ν → Prop) → Prop) →
    NecFunctionalChoice σ (ν → Prop) := fun ha hs₀ hs =>
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (actuality_sections_choice (ν := ν) (σ := σ))) ha) hs₀) hs

theorem necessary_actuality_retractions_plenitude {ν σ : Type} [Ty ν] [Ty σ] :
    NecActuality → NecLeftSplitting Prop (Prop → Prop) →
    NecLeftSplitting (σ → (ν → Prop) → Prop) (Prop → σ → (ν → Prop) → Prop) →
    NecPlenitude σ (ν → Prop) := fun ha hs₀ hs =>
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (actuality_retractions_plenitude (ν := ν) (σ := σ))) ha) hs₀) hs

theorem choice_distinctness {σ : Type} [Ty σ] :
    FunctionalChoice σ Prop → NecessityOfDistinctness σ := fun fc =>
  Proofs.plenitude_r_implies_distinctness_necessary_r
    (Proofs.functional_choice_r_implies_plenitude_r fc)

theorem necessary_choice_c5 :
    NecFunctionalChoice Prop Prop → NecNecessityOfDistinctness Prop :=
  modal_K _ _ (nec% (choice_distinctness (σ := Prop)))

theorem necessary_choice_strong_sections {A B : Type} [Rel A] [Rel B] :
    NecFunctionalChoice Prop Prop → NecFunctionalChoice B A → StrongRightSplitting A B :=
  fun fc₀ fc => sections_strong_of_barcan (functional_choice_sections (box_elim fc))
    (Proofs.necessary_nd_implies_bf (necessary_choice_c5 fc₀))

theorem c5_necessary_retractions {ν B : Type} [Ty ν] [Rel B] :
    NecNecessityOfDistinctness Prop → NecLeftSplitting (ν → Prop) B := fun c5 =>
  modal_K _ _
    (nec% (fun (h : NecNecessityOfDistinctness Prop) =>
      strong_retractions_retractions (c5_strong_retractions (ν := ν) (B := B) h)))
    (modal_four _ c5)

theorem c5_necessary_retractions_t {B : Type} [Rel B] :
    NecNecessityOfDistinctness Prop → NecLeftSplitting Prop B := fun c5 =>
  modal_K _ _
    (nec% (fun (h : NecNecessityOfDistinctness Prop) =>
      strong_retractions_retractions (c5_strong_retractions_t (B := B) h)))
    (modal_four _ c5)

theorem necessary_truth_retractions_c5 :
    NecLeftSplitting Prop (Prop → Prop) → NecNecessityOfDistinctness Prop :=
  modal_K _ _ (nec% (truth_retractions_nd (A := Prop)))

end Classicism.Research.Splitting
