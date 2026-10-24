import Flypitch4.Zfc
import Flypitch4.Completeness

/-!
# Ordinary ZFC models with opposite CH verdicts

This is an external metatheoretic adapter, not a derivation in Classicism.
It uses the pinned Flypitch development in
`external/erdos501-218d1c1`: the two unprovability theorems in
`Flypitch4/Zfc.lean` and the actual model-existence/completeness proof in
`Flypitch4/Completeness.lean`.

The short contrapositive-completeness argument below is adapted, with its
theory and language generalized, from Elliot Glazer's
`Erdos501/FOL/Independence.lean`, `exists_model_of_not_sprovable` (Apache 2.0):
https://github.com/elliotglazer/erdos501/blob/218d1c1/Erdos501/FOL/Independence.lean
The imported independence and completeness proofs are the Flypitch Project's
development, ported to Lean 4; their attribution and license are retained in
the external source directory.

## Exact scope

* `ZFC` and `CH_f` are Flypitch's expanded-signature first-order theory and
  sentence. No equivalence with the Classicism real-field CH formula is
  asserted here.
* These are ordinary two-valued models, with no well-foundedness,
  transitivity, standardness, or external countability assertion.
* `L_ZFC : Fol.Language.{1}` and `Fol.Structure L` has its carrier in the
  language's universe. Thus the models below have carrier `Type 1`.
  This adapter does not claim a `Type 0` or countable witness.
* The imported unprovability theorems hold in Lean's ambient universe
  metatheory, with no explicit consistency premise. Accordingly the theorem
  here is stronger than an implication with a `Con(ZFC)` premise in that
  ambient metatheory. Adding an unused consistency premise would not supply
  a finitistic relative-consistency reduction.

No object-language choice or extensionality assumption is added to C by this
external metatheoretic use of Lean's classical logic.
-/

open Fol

namespace ClassicismZFC.OppositeCH

universe u

/-- Contrapositive completeness produces an actual nonempty countermodel. -/
theorem exists_model_of_not_sprovable {L : Language.{u}}
    {T : SentTheory L} {φ : sentence L} (h : ¬ (T ⊢ₛ' φ)) :
    ∃ S : Fol.Structure L,
      Nonempty S.carrier ∧ (S ⊨ₜ T) ∧ ¬ (S ⊨ₘ φ) := by
  classical
  rw [Fol.completeness] at h
  by_contra hcon
  apply h
  intro S hne hT
  by_contra hφ
  exact hcon ⟨S, hne, hT, hφ⟩

/-- A nonempty ordinary model of Flypitch's ZFC in which its CH sentence fails. -/
theorem exists_model_not_CH :
    ∃ S : Fol.Structure L_ZFC,
      Nonempty S.carrier ∧ (S ⊨ₜ _root_.ZFC) ∧ ¬ (S ⊨ₘ CH_f) :=
  exists_model_of_not_sprovable CH_f_unprovable

/-- A nonempty ordinary model of Flypitch's ZFC in which its CH sentence holds. -/
theorem exists_model_CH :
    ∃ S : Fol.Structure L_ZFC,
      Nonempty S.carrier ∧ (S ⊨ₜ _root_.ZFC) ∧ (S ⊨ₘ CH_f) := by
  classical
  obtain ⟨S, hne, hZFC, hnot⟩ :=
    exists_model_of_not_sprovable neg_CH_f_unprovable
  refine ⟨S, hne, hZFC, ?_⟩
  simpa only [realize_sentence_not, not_not] using hnot

/-- Both two-valued models exist in the ambient Lean metatheory. -/
theorem exists_opposite_models :
    ∃ Spos Sneg : Fol.Structure L_ZFC,
      (Nonempty Spos.carrier ∧ (Spos ⊨ₜ _root_.ZFC) ∧ (Spos ⊨ₘ CH_f)) ∧
      (Nonempty Sneg.carrier ∧ (Sneg ⊨ₜ _root_.ZFC) ∧ ¬ (Sneg ⊨ₘ CH_f)) := by
  obtain ⟨Spos, hpos⟩ := exists_model_CH
  obtain ⟨Sneg, hneg⟩ := exists_model_not_CH
  exact ⟨Spos, Sneg, hpos, hneg⟩

/-- A chosen CH model, obtained from the proved existence theorem. -/
noncomputable def positiveModel : Fol.Structure L_ZFC :=
  Classical.choose exists_model_CH

theorem positive_nonempty : Nonempty positiveModel.carrier :=
  (Classical.choose_spec exists_model_CH).1

theorem positive_modelsZFC : positiveModel ⊨ₜ _root_.ZFC :=
  (Classical.choose_spec exists_model_CH).2.1

theorem positive_CH : positiveModel ⊨ₘ CH_f :=
  (Classical.choose_spec exists_model_CH).2.2

/-- A chosen not-CH model, obtained from the proved existence theorem. -/
noncomputable def negativeModel : Fol.Structure L_ZFC :=
  Classical.choose exists_model_not_CH

theorem negative_nonempty : Nonempty negativeModel.carrier :=
  (Classical.choose_spec exists_model_not_CH).1

theorem negative_modelsZFC : negativeModel ⊨ₜ _root_.ZFC :=
  (Classical.choose_spec exists_model_not_CH).2.1

theorem negative_not_CH : ¬ (negativeModel ⊨ₘ CH_f) :=
  (Classical.choose_spec exists_model_not_CH).2.2

#print axioms exists_model_of_not_sprovable
#print axioms exists_model_CH
#print axioms exists_model_not_CH
#print axioms exists_opposite_models
#print axioms positive_nonempty
#print axioms positive_modelsZFC
#print axioms positive_CH
#print axioms negative_nonempty
#print axioms negative_modelsZFC
#print axioms negative_not_CH

end ClassicismZFC.OppositeCH
