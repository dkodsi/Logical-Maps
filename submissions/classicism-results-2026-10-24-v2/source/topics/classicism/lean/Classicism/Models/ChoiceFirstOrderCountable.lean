import Classicism.Models.ChoiceFirstOrderSmall
import Mathlib.Tactic.DeriveCountable
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List

/-!
# Countability of the actual finite first-order syntax

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/finite-choice-forcing-extraction-review.md` sections 2--4
(unpaginated). The finite contexts, sorted variables, and `SmallFormula`
constructors are the actual syntax used by the interpretation bridge.
Their countability is proved here, including the collection of all small
comprehension instances. No structure, model-existence premise, or assumed
extraction theorem is used.

The natural-number encoding is noncomputable: it chooses an `Encodable`
structure from the proved countability result. Its round-trip and
injectivity laws are proved. This does not yet connect the syntax to a
complete proof calculus or formalize forcing-to-ground extraction.
-/

namespace Classicism.Meta.ChoiceFirstOrder

deriving instance Countable for Ty, RTy
deriving instance Countable for Var

/-- A finite relational tuple of countable variable sorts is countable. -/
instance argsCountable (D : Ty → Type) [∀ σ, Countable (D σ)] (ρ : RTy) :
    Countable (Args D ρ) := by
  induction ρ using RTy.induction with
  | t =>
    change Countable PUnit
    infer_instance
  | arr σ ρ ih =>
    change Countable (D σ × Args D ρ)
    letI : Countable (Args D ρ) := ih
    infer_instance

deriving instance Countable for SmallFormula

/-- Countability holds for each actual finite typed context. -/
theorem smallFormula_countable (Γ : Ctx) : Countable (SmallFormula Γ) :=
  inferInstance

/-- The union over all finite contexts is still a countable syntactic type. -/
theorem contextFormula_countable : Countable (Σ Γ : Ctx, SmallFormula Γ) :=
  inferInstance

/-- Exactly the syntactic indices of `SmallComprehension`; environments are
semantically universally quantified, not additional syntactic parameters. -/
abbrev SmallComprehensionIndex :=
  Σ Γ : Ctx, Σ ρ : RTy, SmallFormula (ρ.args ++ Γ)

theorem smallComprehensionIndex_countable : Countable SmallComprehensionIndex :=
  inferInstance

noncomputable instance smallFormulaEncodable (Γ : Ctx) : Encodable (SmallFormula Γ) :=
  Encodable.ofCountable _

/-- A natural-number code for an actual small formula in a fixed context. -/
noncomputable def SmallFormula.code {Γ : Ctx} (φ : SmallFormula Γ) : Nat :=
  Encodable.encode φ

/-- Partial decoding for the same fixed context. -/
noncomputable def SmallFormula.decode (Γ : Ctx) (n : Nat) : Option (SmallFormula Γ) :=
  Encodable.decode n

theorem SmallFormula.decode_code {Γ : Ctx} (φ : SmallFormula Γ) :
    SmallFormula.decode Γ φ.code = some φ :=
  Encodable.encodek φ

theorem SmallFormula.code_injective (Γ : Ctx) :
    Function.Injective (@SmallFormula.code Γ) :=
  Encodable.encode_injective

/-- Closed sentences have a genuine natural-number injection. -/
noncomputable def smallSentenceEmbedding : SmallFormula [] ↪ Nat where
  toFun := SmallFormula.code
  inj' := SmallFormula.code_injective []

/-- The existing translation now has an actual natural-number code. -/
noncomputable def smallSentenceCode (p : Sentence Signature.pure) : Nat :=
  (smallSentenceTranslation p).code

/-- Interpret a number only when it decodes to a closed small formula. -/
def realizeSmallSentenceCode (S : Structure) (n : Nat) : Prop :=
  ∃ φ : SmallFormula [], SmallFormula.decode [] n = some φ ∧ φ.Realize S .nil

/-- Encoding the actual translator preserves precisely its established
truth clause; no injectivity of the original sentence translation is assumed. -/
theorem smallSentenceCode_correct (S : Structure) (p : Sentence Signature.pure) :
    realizeSmallSentenceCode S (smallSentenceCode p) ↔ S.model.HoldsSentence p := by
  constructor
  · rintro ⟨φ, hφ, hφS⟩
    have heq : smallSentenceTranslation p = φ := by
      apply Option.some.inj
      exact (SmallFormula.decode_code (smallSentenceTranslation p)).symm.trans hφ
    subst φ
    exact (smallSentenceTranslation_correct S p).mp hφS
  · intro hp
    refine ⟨smallSentenceTranslation p, ?_, (smallSentenceTranslation_correct S p).mpr hp⟩
    exact SmallFormula.decode_code (smallSentenceTranslation p)

end Classicism.Meta.ChoiceFirstOrder
