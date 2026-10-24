import Classicism.ChoiceHierarchyEncoding
import Classicism.ChoiceHierarchyPlenitude

/-!
# Constructive steps used by the recursive type embedding

Each witness below is an operation of the original relational language.
The quantified injection assertion is at fixed source/target types, and
`NecEmbedding` puts the existential inside the box. No uniform choice of
witnesses across types or worlds is asserted. The following module performs
the actual structural recursion using the generated C rules.
-/

namespace Classicism.ChoiceHierarchyRealizationSteps

def Embedding (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∃ i : σ → τ, ∀ x y, i x = i y → x = y

def NecEmbedding (σ τ : Type) [Ty σ] [Rel τ] : Prop := □ (Embedding σ τ)

theorem embedding_e : Embedding e (e → Prop) :=
  ⟨fun x z => z = x, fun x y h => ChoiceHierarchy.haecceity_injective x y h⟩

theorem embedding_t : Embedding Prop (e → Prop) :=
  ⟨fun p (_ : e) => p, fun p q h => e_exists.elim fun x _ => congrFun h x⟩

theorem embedding_lift {σ α : Type} [Ty σ] [Rel α] :
    Embedding σ α → Embedding σ (α → Prop) := by
  rintro ⟨i, hi⟩
  exact ⟨fun x z => z = i x,
    fun x y h => hi x y (ChoiceHierarchy.haecceity_injective (i x) (i y) h)⟩

theorem embedding_graph {σ τ α : Type} [Ty σ] [Rel τ] [Rel α] :
    Embedding σ α → Embedding τ α → P.Functionality σ τ →
    Embedding (σ → τ) (((α → Prop) → Prop) → Prop) := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hf
  exact ⟨ChoiceHierarchyEncoding.graphCode i j,
    ChoiceHierarchyEncoding.graphCode_injective i j hi hj hf⟩

theorem selector_of_embedding_plenitude {α β : Type} [Rel α] [Rel β] :
    Embedding α β → P.Plenitude β α →
    ChoiceHierarchy.Selector β → ChoiceHierarchy.Selector α := by
  rintro ⟨i, hi⟩ hp hs
  exact ChoiceHierarchyEncoding.selector_of_injection_plenitude i hi hp hs

theorem necEmbedding_e : NecEmbedding e (e → Prop) := nec% embedding_e
theorem necEmbedding_t : NecEmbedding Prop (e → Prop) := nec% embedding_t

theorem necEmbedding_lift {σ α : Type} [Ty σ] [Rel α] :
    NecEmbedding σ α → NecEmbedding σ (α → Prop) :=
  fun h => modal_K _ _ (nec% (embedding_lift (σ := σ) (α := α))) h

theorem necEmbedding_graph {σ τ α : Type} [Ty σ] [Rel τ] [Rel α] :
    NecEmbedding σ α → NecEmbedding τ α → P.NecFunctionality σ τ →
    NecEmbedding (σ → τ) (((α → Prop) → Prop) → Prop) := fun hi hj hf =>
  modal_K _ _
    (modal_K _ _
      (modal_K _ _ (nec% (embedding_graph (σ := σ) (τ := τ) (α := α))) hi) hj) hf

theorem necSelector_of_necEmbedding_plenitude {α β : Type} [Rel α] [Rel β] :
    NecEmbedding α β → P.NecPlenitude β α →
    ChoiceHierarchy.NecSelector β → ChoiceHierarchy.NecSelector α := fun hi hp hs =>
  modal_K _ _
    (modal_K _ _
      (modal_K _ _ (nec% (selector_of_embedding_plenitude (α := α) (β := β))) hi) hp) hs

end Classicism.ChoiceHierarchyRealizationSteps

#classicism_schema Classicism.ChoiceHierarchyRealizationSteps.Embedding
  Classicism.ChoiceHierarchyRealizationSteps.NecEmbedding

#classicism_check
  Classicism.ChoiceHierarchyRealizationSteps.embedding_e
  Classicism.ChoiceHierarchyRealizationSteps.embedding_t
  Classicism.ChoiceHierarchyRealizationSteps.embedding_lift
  Classicism.ChoiceHierarchyRealizationSteps.embedding_graph
  Classicism.ChoiceHierarchyRealizationSteps.selector_of_embedding_plenitude
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_e
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_t
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_lift
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_graph
  Classicism.ChoiceHierarchyRealizationSteps.necSelector_of_necEmbedding_plenitude

#classicism_types
  Classicism.ChoiceHierarchyRealizationSteps.embedding_e
  Classicism.ChoiceHierarchyRealizationSteps.embedding_t
  Classicism.ChoiceHierarchyRealizationSteps.embedding_lift
  Classicism.ChoiceHierarchyRealizationSteps.embedding_graph
  Classicism.ChoiceHierarchyRealizationSteps.selector_of_embedding_plenitude
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_e
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_t
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_lift
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_graph
  Classicism.ChoiceHierarchyRealizationSteps.necSelector_of_necEmbedding_plenitude

#classicism_certify
  Classicism.ChoiceHierarchyRealizationSteps.embedding_e
  Classicism.ChoiceHierarchyRealizationSteps.embedding_t
  Classicism.ChoiceHierarchyRealizationSteps.embedding_lift
  Classicism.ChoiceHierarchyRealizationSteps.embedding_graph
  Classicism.ChoiceHierarchyRealizationSteps.selector_of_embedding_plenitude
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_e
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_t
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_lift
  Classicism.ChoiceHierarchyRealizationSteps.necEmbedding_graph
  Classicism.ChoiceHierarchyRealizationSteps.necSelector_of_necEmbedding_plenitude
