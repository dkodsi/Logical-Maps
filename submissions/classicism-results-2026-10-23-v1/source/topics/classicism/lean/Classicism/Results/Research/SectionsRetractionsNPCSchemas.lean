import Classicism.Results.Research.SectionsRetractionsNPCCertificates
import Classicism.Results.Research.SectionsRetractionsSchemas
import Classicism.Results.Research.SectionsRetractionsBoxedSchemas
import Classicism.Results.Research.NPCC5Atomicity

/-!
# Necessary Functional Choice and unboxed strong sections

Direct source: `research/2026-10-22/notes/functional-choice-by-sections.md`,
section 4 (misc, unpaginated), with the checked NPC theorem of Goodsell and
Yli-Vakkuri following Dorr's 23 September 2026 proof sketch. Formal assembly:
23 October 2026. The completed NPC proof and human source are not modified.

The right-hand splitting schema is UNBOXED: an actually surjective f between
relational types has a g satisfying the necessary universal inverse equation.
It is not categorical-epimorphism splitting. FC retains every admitted input
type, including e, and every relational output, including the empty argument
list (type t). Necessitation is used only via already checked C implications
or NPC at a closed pure FC sentence.
-/

namespace Classicism.Meta.Research.Splitting
open AxiomSet Classicism.Research.Splitting

abbrev NecessaryActualityStrongSections :=
  P.NecActuality.schema ∪ StrongRightSplitting.schema

theorem necessary_actuality_strong_sections_imply_choice :
    NecessaryActualityStrongSections ⟹ P.FunctionalChoice.schema :=
  Entails.trans
    (Entails.union
      (Entails.trans (Entails.union_left _ _) npc_necessary_actuality_actuality.entails)
      (Entails.trans (Entails.union_right _ _) npc_strong_sections_sections.entails))
    actuality_sections_imply_functional_choice

theorem necessary_actuality_strong_sections_imply_c5 :
    NecessaryActualityStrongSections ⟹ P.NecNecessityOfDistinctness.schema :=
  Entails.trans
    (Entails.union necessary_actuality_strong_sections_imply_choice
      (Entails.union_right _ _)) npc_choice_strong_sections_c5.entails

theorem necessary_actuality_strong_sections_imply_atomicity_t :
    NecessaryActualityStrongSections ⟹ P.AtomicityT.schema :=
  Entails.trans
    (Entails.union (Entails.union_left _ _)
      necessary_actuality_strong_sections_imply_c5)
    npc_c5_necessary_actuality_atomicity.entails

private theorem npc_retraction_args (q : RTy → RTy → Sentence Signature.pure) :
    (fun a => ∃ ρ τ : RTy, ρ.Closed ∧ τ.Closed ∧ a = q ρ τ) ⊆
    (fun a => ∃ νs : List Ty, ∃ τ : RTy,
      Ty.AllClosed νs ∧ τ.Closed ∧ a = q (νs ⇒* .t) τ) :=
  fun _ ⟨ρ, τ, hρ, hτ, he⟩ =>
    ⟨ρ.args, τ, RTy.closed_args hρ, hτ,
      he.trans (congrArg (fun r => q r τ) (RTy.ofArgs_args ρ).symm)⟩

theorem npc_c5_implies_necessary_retractions :
    P.NecNecessityOfDistinctness.schema ⟹ NecLeftSplitting.schema :=
  Entails.mono_right (npc_retraction_args NecLeftSplitting.quoted)
    npc_c5_necessary_retractions.listEntails

theorem necessary_actuality_strong_sections_imply_necessary_plenitude :
    NecessaryActualityStrongSections ⟹ P.NecPlenitude.schema :=
  Entails.trans
    (Entails.union (Entails.union_left _ _)
      (Entails.trans necessary_actuality_strong_sections_imply_c5
        npc_c5_implies_necessary_retractions))
    necessary_actuality_retractions_imply_necessary_plenitude

theorem necessary_choice_implies_strong_sections :
    P.NecFunctionalChoice.schema ⟹ StrongRightSplitting.schema :=
  Entails.trans (Entails.union (Entails.refl _) (Entails.refl _))
    necessary_choice_strong_sections.entails

private theorem npc_transport {Sig : Signature} {A B : AxiomSet Signature.pure}
    (h : A ⟹ B) : AxiomSet.ofPure (Sig := Sig) A ⟹ AxiomSet.ofPure B := by
  rintro a ⟨p, hp, rfl⟩
  exact Derivable.mono (ofPure_union_subset A) (Theorem.ofPure (h p hp))

private theorem npc_union_ofPure {Sig : Signature} {Ax : AxiomSet Sig}
    {A B : AxiomSet Signature.pure}
    (ha : Ax ⟹ AxiomSet.ofPure A) (hb : Ax ⟹ AxiomSet.ofPure B) :
    Ax ⟹ AxiomSet.ofPure (A ∪ B) := by
  rintro a ⟨p, hp | hp, rfl⟩
  · exact ha _ ⟨p, hp, rfl⟩
  · exact hb _ ⟨p, hp, rfl⟩

/-- The unboxed, actually-surjective strong-section schema in any signature. -/
abbrev StrongRightSplittingIn {Sig : Signature} : AxiomSet Sig :=
  AxiomSet.ofPure StrongRightSplitting.schema

/-- Apply NPC separately to each closed pure FC instance. -/
theorem npc_boxes_functional_choice {Sig : Signature} {Ax : AxiomSet Sig}
    (hnpc : Ax ⟹ pureVersion noContingency)
    (hfc : Ax ⟹ P.FunctionalChoice.schemaIn) :
    Ax ⟹ P.NecFunctionalChoice.schemaIn := by
  rintro a ⟨q, ⟨σ, ρ, hσ, hρ, rfl⟩, rfl⟩
  have hp : P.FunctionalChoice.schema (P.FunctionalChoice.quoted σ ρ) :=
    ⟨σ, ρ, hσ, hρ, rfl⟩
  have hc := P.FunctionalChoice.schema_closedTypes _ hp
  have hn := hnpc _ ⟨Term.imp (P.FunctionalChoice.quoted σ ρ)
    (Term.box (P.FunctionalChoice.quoted σ ρ)), noContingency_mem hc, rfl⟩
  exact Theorem.mp hn (hfc _ ⟨_, hp, rfl⟩)

/-- The full benchmark at exactly the signature scope of the generated NPC
theorem. Neither conjunct on the right is strengthened. -/
theorem necessary_choice_iff_necessary_actuality_strong_sections
    {Sig : Signature} (hSig : Sig.Admitted) (Ax : AxiomSet Sig) :
    (Ax ⟹ P.NecFunctionalChoice.schemaIn) ↔
      ((Ax ⟹ P.NecActuality.schemaIn) ∧ (Ax ⟹ StrongRightSplittingIn)) := by
  constructor
  · intro hfc
    exact ⟨Entails.trans hfc (npc_transport necessary_choice_actuality.entails),
      Entails.trans hfc (npc_transport necessary_choice_implies_strong_sections)⟩
  · rintro ⟨ha, hs⟩
    have hh := npc_union_ofPure ha hs
    have hfc := Entails.trans hh
      (npc_transport necessary_actuality_strong_sections_imply_choice)
    have hc5 := Entails.trans hh
      (npc_transport necessary_actuality_strong_sections_imply_c5)
    have hat := Entails.trans hh
      (npc_transport necessary_actuality_strong_sections_imply_atomicity_t)
    have hnpc := Classicism.Meta.Research.NPC.c5_and_atomicity_t_imply_no_pure_contingency
      hSig Ax hc5 hat
    exact npc_boxes_functional_choice hnpc hfc

end Classicism.Meta.Research.Splitting

#print axioms Classicism.Meta.Research.Splitting.necessary_actuality_strong_sections_imply_necessary_plenitude
#print axioms Classicism.Meta.Research.Splitting.npc_boxes_functional_choice
#print axioms Classicism.Meta.Research.Splitting.necessary_choice_iff_necessary_actuality_strong_sections
