import Classicism.Results.Research.SectionsRetractionsBoxed
import Classicism.Results.Research.SectionsRetractionsMasks

/-!
# Local C implications for the strong-section NPC consumer

Direct source: `research/2026-10-22/notes/functional-choice-by-sections.md`,
section 4 (misc, unpaginated), and the existing splitting proof contributions.
This is the formal assembly of that argument, 23 October 2026.

StrongRightSplitting has an unboxed actual-surjectivity antecedent and a boxed
universal right-inverse equation. No categorical epimorphism is substituted.
The FC/Plenitude input type remains arbitrary, including e.
-/

namespace Classicism.Research.Splitting
open Classicism.P

theorem npc_necessary_actuality_actuality : NecActuality → Actuality := box_elim

theorem npc_strong_sections_sections {A B : Type} [Rel A] [Rel B] :
    StrongRightSplitting A B → RightSplitting A B := strong_sections_sections

theorem npc_choice_strong_sections_c5 {σ : Type} [Ty σ] :
    FunctionalChoice Prop Prop →
    StrongRightSplitting (Prop → Prop) (Prop → Prop) →
    NecNecessityOfDistinctness σ := fun fc hs =>
  Proofs.necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r
    (Proofs.nd_and_bf_imply_necessary_nd (choice_distinctness fc)
      (strong_truth_sections_barcan hs))

theorem npc_c5_necessary_actuality_atomicity :
    NecActuality → NecNecessityOfDistinctness Prop → AtomicityT := fun ha hc =>
  Proofs.atomicity_r_implies_atomicity_t
    (Proofs.c5_and_necessary_actuality_imply_atomicity_at_t ha hc)

theorem npc_c5_necessary_retractions {ν B : Type} [Ty ν] [Rel B] :
    NecNecessityOfDistinctness Prop → NecLeftSplitting (ν → Prop) B :=
  c5_necessary_retractions

end Classicism.Research.Splitting
