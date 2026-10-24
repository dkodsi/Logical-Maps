import ClassicismZFC.CHTranslation

/-!
# Preserving explicit field witnesses when taking ordinary models

Original adapter, misc, 23 October 2026. Boolean soundness and actual
first-order completeness transfer a whole existential witness sentence at
once. In particular, field existence is not inferred merely from the
existence of a model of ZFC with the desired CH verdict. The concrete
Boolean-valued constructions must prove the requested sentence first.

This source uses the pinned Flypitch and Erdos501 translations. It is
uncompiled. These are ambient classical-metatheory existence statements,
not a finitistic relative-consistency interpretation or object-C proofs.
-/

open Fol
open scoped FirstOrder

namespace ClassicismZFC.BooleanWitnesses

universe u v

/-- A nontrivial Boolean model transfers the requested sentence, including
all existential witness data, to an actual ordinary model of the same theory. -/
theorem ordinary_model_of_forced_sentence {L : Fol.Language.{u}}
    {β : Type v} [CompleteBooleanAlgebra β] [Nontrivial β]
    (S : Fol.bStructure L β) [Nonempty S]
    {T : Fol.SentTheory L} (hT : ⊤ ⊩ₜ[S] T)
    (φ : Fol.sentence L) (hφ : ⊤ ⊩[S] φ) :
    ∃ M : Fol.Structure L,
      Nonempty M.carrier ∧ (M ⊨ₜ T) ∧ (M ⊨ₘ φ) := by
  have hn : ¬ (T ⊢ₛ' (bd_not φ : Fol.sentence L)) := by
    apply Fol.unprovable_of_model_neg S hT bot_lt_top
    rw [Fol.forced_in_not]
    exact hφ
  obtain ⟨M, hne, hM, hnot⟩ := OppositeCH.exists_model_of_not_sprovable hn
  refine ⟨M, hne, hM, ?_⟩
  simpa only [Fol.realize_sentence_not, not_not] using hnot

/-- Transfer the exact Mathlib sentence through the proved source-language
translation, while retaining all ZFC axioms and explicit witnesses. -/
theorem small_model_satisfiable {β : Type v}
    [CompleteBooleanAlgebra β] [Nontrivial β]
    (S : Fol.bStructure L_ZFC β) [Nonempty S]
    (hZFC : ⊤ ⊩ₜ[S] _root_.ZFC)
    (φ : Erdos501.FOL.L.Sentence)
    (hφ : ⊤ ⊩[S] Erdos501.FOL.tr φ) :
    (Erdos501.FOL.ZFC ∪ {φ}).IsSatisfiable := by
  obtain ⟨M, hne, hM, hφM⟩ := ordinary_model_of_forced_sentence S hZFC _ hφ
  letI : Nonempty M.carrier := hne
  letI : Erdos501.FOL.L.Structure M.carrier := Erdos501.FOL.toM M
  have hφ' : M.carrier ⊨ φ :=
    (Erdos501.FOL.realize_sentence_tr M φ).mpr hφM
  letI : M.carrier ⊨ Erdos501.FOL.ZFC ∪ {φ} :=
    FirstOrder.Language.Theory.model_union_iff.mpr
      ⟨Erdos501.FOL.toM_models_ZFC M hM,
        FirstOrder.Language.Theory.model_singleton_iff.mpr hφ'⟩
  exact FirstOrder.Language.Theory.Model.isSatisfiable M.carrier

/-- The small model is chosen only after its existence has been proved. -/
noncomputable def smallModel {β : Type v}
    [CompleteBooleanAlgebra β] [Nontrivial β]
    (S : Fol.bStructure L_ZFC β) [Nonempty S]
    (hZFC : ⊤ ⊩ₜ[S] _root_.ZFC)
    (φ : Erdos501.FOL.L.Sentence)
    (hφ : ⊤ ⊩[S] Erdos501.FOL.tr φ) :
    FirstOrder.Language.Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {φ}) :=
  Classical.choice (small_model_satisfiable S hZFC φ hφ)

#print axioms ordinary_model_of_forced_sentence
#print axioms small_model_satisfiable

end ClassicismZFC.BooleanWitnesses
