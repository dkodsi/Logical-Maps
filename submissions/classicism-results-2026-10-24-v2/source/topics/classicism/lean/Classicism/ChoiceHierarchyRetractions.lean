import Classicism.Results.ChoiceHierarchyRealization

/-!
# Actual retraction and haecceity-decoder realization

The inverse at the recursive budget is supplied by Plenitude; it is not
claimed to be a pure inverse term. In contrast, the haecceity decoder is
proved in C itself at every closed relational type by vectorizing its pure
predicate-type construction. Boxes retain their existential witnesses inside.
-/

namespace Classicism.ChoiceHierarchyRetractions

def Retraction (α β : Type) [Rel α] [Rel β] : Prop :=
  ∃ i : α → β, ∃ r : β → α, ∀ x, r (i x) = x

def NecRetraction (α β : Type) [Rel α] [Rel β] : Prop := □ (Retraction α β)

def HaecceityDecoder (τ : Type) [Rel τ] : Prop :=
  ∃ r : (τ → Prop) → τ, ∀ x, r (fun z => z = x) = x

def NecHaecceityDecoder (τ : Type) [Rel τ] : Prop := □ (HaecceityDecoder τ)

theorem retraction_of_embedding_plenitude {α β : Type} [Rel α] [Rel β] :
    ChoiceHierarchyRealizationSteps.Embedding α β → P.Plenitude β α → Retraction α β := by
  rintro ⟨i, hi⟩ hp
  obtain ⟨r, hr⟩ := ChoiceHierarchyEncoding.retraction_of_injection_plenitude i hi hp
  exact ⟨i, r, hr⟩

theorem necRetraction_of_embedding_plenitude {α β : Type} [Rel α] [Rel β] :
    ChoiceHierarchyRealizationSteps.NecEmbedding α β →
    P.NecPlenitude β α → NecRetraction α β := fun hi hp =>
  modal_K _ _
    (modal_K _ _ (nec% (retraction_of_embedding_plenitude (α := α) (β := β))) hi) hp

theorem decoder_predicate {σ : Type} [Ty σ] : HaecceityDecoder (σ → Prop) :=
  ⟨fun Q x => ∃ f : σ → Prop, Q f ∧ f x, ChoiceHierarchy.decode_haecceity_predicate⟩

theorem necDecoder_predicate {σ : Type} [Ty σ] : NecHaecceityDecoder (σ → Prop) :=
  nec% (decoder_predicate (σ := σ))

theorem retraction_of_decoder {τ : Type} [Rel τ] :
    HaecceityDecoder τ → Retraction τ (τ → Prop) := by
  rintro ⟨r, hr⟩
  exact ⟨fun x z => z = x, r, hr⟩

theorem necRetraction_of_decoder {τ : Type} [Rel τ] :
    NecHaecceityDecoder τ → NecRetraction τ (τ → Prop) :=
  fun h => modal_K _ _ (nec% (retraction_of_decoder (τ := τ))) h

theorem selector_of_decoder_diagonal {τ : Type} [Rel τ] :
    HaecceityDecoder τ → P.FunctionalChoice (τ → Prop) (τ → Prop) →
    ChoiceHierarchy.Selector τ := by
  rintro ⟨r, hr⟩ hf
  exact ChoiceHierarchy.diagonal_selector_with_decoder r hr hf

theorem necSelector_of_decoder_diagonal {τ : Type} [Rel τ] :
    NecHaecceityDecoder τ → P.NecFunctionalChoice (τ → Prop) (τ → Prop) →
    ChoiceHierarchy.NecSelector τ := fun hd hf =>
  modal_K _ _
    (modal_K _ _ (nec% (selector_of_decoder_diagonal (τ := τ))) hd) hf

end Classicism.ChoiceHierarchyRetractions

#classicism_schema
  Classicism.ChoiceHierarchyRetractions.Retraction
  Classicism.ChoiceHierarchyRetractions.NecRetraction
  Classicism.ChoiceHierarchyRetractions.HaecceityDecoder
  Classicism.ChoiceHierarchyRetractions.NecHaecceityDecoder

#classicism_check
  Classicism.ChoiceHierarchyRetractions.retraction_of_embedding_plenitude
  Classicism.ChoiceHierarchyRetractions.necRetraction_of_embedding_plenitude
  Classicism.ChoiceHierarchyRetractions.decoder_predicate
  Classicism.ChoiceHierarchyRetractions.necDecoder_predicate
  Classicism.ChoiceHierarchyRetractions.retraction_of_decoder
  Classicism.ChoiceHierarchyRetractions.necRetraction_of_decoder
  Classicism.ChoiceHierarchyRetractions.selector_of_decoder_diagonal
  Classicism.ChoiceHierarchyRetractions.necSelector_of_decoder_diagonal

#classicism_types
  Classicism.ChoiceHierarchyRetractions.retraction_of_embedding_plenitude
  Classicism.ChoiceHierarchyRetractions.necRetraction_of_embedding_plenitude
  Classicism.ChoiceHierarchyRetractions.decoder_predicate
  Classicism.ChoiceHierarchyRetractions.necDecoder_predicate
  Classicism.ChoiceHierarchyRetractions.retraction_of_decoder
  Classicism.ChoiceHierarchyRetractions.necRetraction_of_decoder
  Classicism.ChoiceHierarchyRetractions.selector_of_decoder_diagonal
  Classicism.ChoiceHierarchyRetractions.necSelector_of_decoder_diagonal

#classicism_certify
  Classicism.ChoiceHierarchyRetractions.retraction_of_embedding_plenitude
  Classicism.ChoiceHierarchyRetractions.necRetraction_of_embedding_plenitude
  Classicism.ChoiceHierarchyRetractions.decoder_predicate
  Classicism.ChoiceHierarchyRetractions.necDecoder_predicate
  Classicism.ChoiceHierarchyRetractions.retraction_of_decoder
  Classicism.ChoiceHierarchyRetractions.necRetraction_of_decoder
  Classicism.ChoiceHierarchyRetractions.selector_of_decoder_diagonal
  Classicism.ChoiceHierarchyRetractions.necSelector_of_decoder_diagonal

namespace Classicism.Meta.ChoiceHierarchy

open AxiomSet Classicism.ChoiceHierarchyRetractions

/-- Actual retraction at the computed budget, under the exact boxed base. -/
theorem realizedRetraction (ρ : RTy) (hρ : ρ.Closed) :
    Theorem (C.axioms ∪ plenitudeBase)
      (NecRetraction.quoted ρ (tower (relEmbeddingBudget ρ))) :=
  (Theorem.ofC (necRetraction_of_embedding_plenitude.rule ρ
    (tower (relEmbeddingBudget ρ)))).mp₂
    (relationalEmbedding ρ hρ)
    (plenitudeBase_plenitude (.rel (tower (relEmbeddingBudget ρ))) ρ
      (tower_closed (relEmbeddingBudget ρ)) hρ)

/-- The empty argument list supplies the propositional case automatically. -/
theorem closedType_haecceityDecoder (ρ : RTy) (_hρ : ρ.Closed) :
    C.Theorem (NecHaecceityDecoder.quoted ρ) := by
  have h : C.Theorem (NecHaecceityDecoder.quoted (RTy.ofArgs ρ.args)) :=
    necDecoder_predicate.listRule ρ.args
  exact h.cast (by rw [RTy.ofArgs_args])

theorem closedType_haecceityRetraction (ρ : RTy) (hρ : ρ.Closed) :
    C.Theorem (NecRetraction.quoted ρ (.arr (.rel ρ) .t)) :=
  (necRetraction_of_decoder.rule ρ).mp (closedType_haecceityDecoder ρ hρ)

/-- The exact diagonal-to-selector reduction at every closed relational type,
not merely the predicate-type representatives of tower stages. -/
theorem diagonal_property_entails_selector (ρ : RTy) (hρ : ρ.Closed) :
    single (P.NecFunctionalChoice.quoted (.rel (.arr (.rel ρ) .t)) (.arr (.rel ρ) .t)) ⟹
    single (Classicism.ChoiceHierarchy.NecSelector.quoted ρ) := by
  intro a ha
  change a = Classicism.ChoiceHierarchy.NecSelector.quoted ρ at ha
  subst a
  exact ((Theorem.ofC (necSelector_of_decoder_diagonal.rule ρ)).mp
    (Theorem.ofC (closedType_haecceityDecoder ρ hρ))).mp (Theorem.ax rfl)

end Classicism.Meta.ChoiceHierarchy
