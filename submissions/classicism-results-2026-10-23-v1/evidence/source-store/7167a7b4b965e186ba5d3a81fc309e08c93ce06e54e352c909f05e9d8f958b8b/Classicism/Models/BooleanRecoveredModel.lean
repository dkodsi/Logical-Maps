import Classicism.Models.BooleanAxiomTheory

/-!
# The recovered ordinary typed model of the Boolean hierarchy

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md` section 8 and
`research/2026-10-23/boolean-valued-model-extraction.md` sections 4--6
(unpaginated). The countable witness-chain quotient satisfies the actual
first-order theory, so typed recovery produces a genuine project model.
Every closed small formula of Boolean value one transfers to that same
model, and every formula of value zero fails there. Original project
sentences transfer through their explicit small-formula translation.

No ordinary-model existence, comprehension, or Choice verdict is an input.
Specific Choice values are proved in the separate construction modules.
-/

noncomputable section

namespace Classicism.Meta.ChoiceBoolean.RecoveredModel

open ChoiceFirstOrder ChoiceFirstOrder.MathlibBridge
open ChoiceFirstOrder.MathlibBridge.AxiomTheory
open SmallFormulaSemantics

variable {B : Type} [CompleteBooleanAlgebra B] {K : Type}
variable (a : BooleanAction K B) (E : Type) (hE : Nonempty E)

local instance : Countable language.Symbols := language_countable

local instance language_relational : language.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- The concrete tagged Boolean structure used by the witness chain. -/
abbrev booleanStructure := TaggedFirstOrder.booleanStructure a E hE

variable (p₀ : B) (hp₀ : p₀ ≠ ⊥)

/-- The ordinary carrier is the actual countable quotient of names. -/
abbrev Carrier := ModelExtraction.Carrier (booleanStructure a E hE) p₀ hp₀

theorem satisfies_theory :
    FirstOrder.Language.Theory.Model (Carrier a E hE p₀ hp₀) theory :=
  BooleanAxiomTheory.extracted_theory a E hE p₀ hp₀

/-- Typed domains and application are recovered from the quotient's sorts
and profile relation, with their structural laws supplied by the theory. -/
def typedStructure : ChoiceFirstOrder.Structure :=
  recoveredStructure (Carrier a E hE p₀ hp₀) (satisfies_theory a E hE p₀ hp₀)

theorem small_comprehension : SmallComprehension (typedStructure a E hE p₀ hp₀) :=
  recovered_smallComprehension (Carrier a E hE p₀ hp₀)
    (satisfies_theory a E hE p₀ hp₀)

theorem isModel : (typedStructure a E hE p₀ hp₀).model.IsModel :=
  recovered_isModel (Carrier a E hE p₀ hp₀) (satisfies_theory a E hE p₀ hp₀)

theorem small_sentence_correct (φ : SmallFormula []) :
    FirstOrder.Language.Sentence.Realize (Carrier a E hE p₀ hp₀) (translate φ) ↔
      φ.Realize (typedStructure a E hE p₀ hp₀) .nil := by
  exact (Recovery.raw_sentence_correct (Carrier a E hE p₀ hp₀) φ).trans
    (Recovery.rawRealize_recoverStructure (Carrier a E hE p₀ hp₀)
      (model_nonempty _ (satisfies_theory a E hE p₀ hp₀))
      (model_extensional _ (satisfies_theory a E hE p₀ hp₀)) φ .nil)

/-- Truth above the chosen initial condition transfers to the one model. -/
theorem small_transfer (φ : SmallFormula [])
    (hφ : p₀ ≤ smallValue a E φ .nil) :
    φ.Realize (typedStructure a E hE p₀ hp₀) .nil := by
  apply (small_sentence_correct a E hE p₀ hp₀ φ).mp
  apply ModelExtraction.sentence_transfer (booleanStructure a E hE) p₀ hp₀
  simpa only [booleanStructure, TaggedFirstOrder.sentence_value] using hφ

theorem small_transfer_one (φ : SmallFormula [])
    (hφ : smallValue a E φ .nil = ⊤) :
    φ.Realize (typedStructure a E hE p₀ hp₀) .nil :=
  small_transfer a E hE p₀ hp₀ φ (hφ.symm ▸ le_top)

theorem small_failure_zero (φ : SmallFormula [])
    (hφ : smallValue a E φ .nil = ⊥) :
    ¬ φ.Realize (typedStructure a E hE p₀ hp₀) .nil := by
  apply small_transfer_one a E hE p₀ hp₀ (.neg φ)
  change (smallValue a E φ .nil)ᶜ = ⊤
  rw [hφ, compl_bot]

/-- The unchanged original pure sentence is what the recovered model
satisfies; the Boolean hypothesis is its concrete syntactic translation. -/
theorem sentence_transfer (p : Sentence Signature.pure)
    (hp : p₀ ≤ smallValue a E (smallSentenceTranslation p) .nil) :
    (typedStructure a E hE p₀ hp₀).model.HoldsSentence p :=
  (smallSentenceTranslation_correct (typedStructure a E hE p₀ hp₀) p).mp
    (small_transfer a E hE p₀ hp₀ _ hp)

theorem sentence_transfer_one (p : Sentence Signature.pure)
    (hp : smallValue a E (smallSentenceTranslation p) .nil = ⊤) :
    (typedStructure a E hE p₀ hp₀).model.HoldsSentence p :=
  sentence_transfer a E hE p₀ hp₀ p (hp.symm ▸ le_top)

theorem sentence_failure_zero (p : Sentence Signature.pure)
    (hp : smallValue a E (smallSentenceTranslation p) .nil = ⊥) :
    ¬ (typedStructure a E hE p₀ hp₀).model.HoldsSentence p := by
  intro h
  exact small_failure_zero a E hE p₀ hp₀ _ hp
    ((smallSentenceTranslation_correct (typedStructure a E hE p₀ hp₀) p).mpr h)

end Classicism.Meta.ChoiceBoolean.RecoveredModel
