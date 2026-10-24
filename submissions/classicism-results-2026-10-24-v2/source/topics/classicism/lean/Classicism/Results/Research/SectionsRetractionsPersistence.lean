import Classicism.Results.Research.SectionsRetractionsRelationalMasks

/-!
# Persistence and strong sections at relational types

Direct source: `research/2026-10-22/notes/choice-uniformization.md`, §§11,18,
Theorems 17 and 26 (misc; unpaginated). These wrappers retain relational
Barcan as such, so the full-schema assembly does not accidentally assume BF_e.
The tuple-existence premise is discharged from C in the schema assembly.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

theorem surjectivity_of_relational_barcan {A B : Type} [Ty A] [Rel B] :
    BarcanRelational B → SurjectivityPersists A B := surjectivity_of_barcan

theorem relational_barcan_of_surjectivity {ν : Type} [Ty ν] :
    Existence ν → SurjectivityPersists (Prop → ν → Prop) (Prop → ν → Prop) →
      BarcanRelational (ν → Prop) := relational_surjectivity_persistence_barcan

theorem relational_barcan_of_strong_sections {ν : Type} [Ty ν] :
    Existence ν → StrongRightSplitting (Prop → ν → Prop) (Prop → ν → Prop) →
      BarcanRelational (ν → Prop) := relational_strong_sections_barcan

theorem strong_sections_of_sections_relational_barcan {A B : Type} [Rel A] [Rel B] :
    RightSplitting A B → BarcanRelational B → StrongRightSplitting A B :=
  sections_strong_of_barcan

end Classicism.Research.Splitting
