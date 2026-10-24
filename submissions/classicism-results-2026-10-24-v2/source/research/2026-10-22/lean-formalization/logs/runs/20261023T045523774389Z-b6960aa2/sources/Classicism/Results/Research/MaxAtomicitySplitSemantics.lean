import Classicism.Semantics.BooleanValuedSoundness
import Classicism.Results.Research.MaxAtomicitySplitCertificate
import Classicism.Results.Research.MaxAtomicityWellOrder
import Classicism.Results.Research.MaxAtomicityEvalTools

/-!
# Boolean-valued evaluation of the splitter sentence

External classical metatheory. Direct source: the original argument in
`research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md`,
sections 6-7 (unpaginated; source category `misc`).

This file proves the actual supremum calculation used by the proposed selector
and evaluates the actual finite splitter syntax. It does not postulate C
soundness. The non-theorem conclusion uses `BooleanValued.C_sound` through its
proved unequal-values corollary.

There is deliberately no claim that a closed pure term denoting a splitter has
been constructed. In particular an arbitrary external splitting function is
not silently made into an object-language constant. No rigid algebra or
constructible-universe existence theorem is asserted here.

Source submission: compilation and axiom inspection belong to the designated
serial compiler. This header is not a successful check report.
-/

namespace Classicism.Meta.Research.MaxAtomicitySplitSemantics

open BooleanValued
open MaxAtomicityEvalTools

noncomputable section

variable {B : Type} [CompleteBooleanAlgebra B]

/-- A metatheoretic predicate interpreted as an exact bottom/top truth value. -/
def truthValue (P : Prop) : B := by
  classical
  exact if P then ⊤ else ⊥

/-- The existential selector has this value when its selecting predicate is
crisp. This definition uses the actual Boolean supremum, not a chosen witness. -/
def guardedSup (P : B → Prop) : B :=
  ⨆ q : B, truthValue (P q) ⊓ q

/-- A unique crisp witness makes the Boolean existential equal that witness.
The result does not assume that an arbitrary top-valued join has a witness. -/
theorem guardedSup_eq_unique (P : B → Prop) (q : B)
    (hq : P q) (hunique : ∀ r, P r → r = q) : guardedSup P = q := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro r
    by_cases hr : P r
    · simpa only [truthValue, if_pos hr, top_inf_eq] using
        (le_of_eq (hunique r hr))
    · simp only [truthValue, if_neg hr, bot_inf_eq, bot_le]
  · calc
      q = truthValue (P q) ⊓ q := by simp [truthValue, hq]
      _ ≤ guardedSup P := le_iSup (fun r : B => truthValue (P r) ⊓ r) q

/-- The value of the exact splitter formula, including material implication
and crisp equality. -/
def splitValue (f : B → B) : B :=
  ⨅ p : B, crisp p (⊥ : B) ⊔
    ((crisp (p ⊓ f p) (⊥ : B))ᶜ ⊓
      (crisp (p ⊓ (f p)ᶜ) (⊥ : B))ᶜ)

/-- A genuine external splitter makes the formula's value top. -/
theorem splitValue_eq_top (f : B → B)
    (hsplit : ∀ p : B, p ≠ ⊥ → p ⊓ f p ≠ ⊥ ∧ p ⊓ (f p)ᶜ ≠ ⊥) :
    splitValue f = ⊤ := by
  classical
  apply le_antisymm le_top
  apply le_iInf
  intro p
  by_cases hp : p = ⊥
  · simp [crisp, hp]
  · obtain ⟨hleft, hright⟩ := hsplit p hp
    simp [crisp, hp, hleft, hright]

/-- The supremum expression used by the finite selector really selects the
least proper part. Uniqueness is proved from the supplied order, rather than
assumed separately for this existential. -/
theorem guardedLeastPart_eq_selector {r : B → B → Prop} (wf : WellFounded r)
    (total : ∀ x y : B, r x y ∨ x = y ∨ r y x)
    (atomless : MaxAtomicityWellOrder.AtomlessParts B)
    {p : B} (hp : p ≠ ⊥) :
    guardedSup (MaxAtomicityWellOrder.LeastPart r p) =
      MaxAtomicityWellOrder.selector wf atomless p := by
  apply guardedSup_eq_unique
  · exact MaxAtomicityWellOrder.selector_spec wf atomless hp
  · intro q hq
    exact MaxAtomicityWellOrder.leastPart_unique total hq
      (MaxAtomicityWellOrder.selector_spec wf atomless hp)

/-- The Boolean existential itself splits every nonzero p. This proves the
semantic selection step without assuming a splitting function as an input. -/
theorem guardedLeastPart_splits {r : B → B → Prop} (wf : WellFounded r)
    (total : ∀ x y : B, r x y ∨ x = y ∨ r y x)
    (atomless : MaxAtomicityWellOrder.AtomlessParts B)
    {p : B} (hp : p ≠ ⊥) :
    p ⊓ guardedSup (MaxAtomicityWellOrder.LeastPart r p) ≠ ⊥ ∧
      p ⊓ (guardedSup (MaxAtomicityWellOrder.LeastPart r p))ᶜ ≠ ⊥ := by
  rw [guardedLeastPart_eq_selector wf total atomless hp]
  exact MaxAtomicityWellOrder.selector_splits wf atomless hp

theorem guardedLeastPart_splitValue {r : B → B → Prop} (wf : WellFounded r)
    (total : ∀ x y : B, r x y ∨ x = y ∨ r y x)
    (atomless : MaxAtomicityWellOrder.AtomlessParts B) :
    splitValue (fun p => guardedSup (MaxAtomicityWellOrder.LeastPart r p)) = ⊤ :=
  splitValue_eq_top _ (fun _ hp => guardedLeastPart_splits wf total atomless hp)

/-- Evaluation of the actual closed syntax agrees with the Boolean expression.
The term F is required to belong to the pure signature; no new constant is used. -/
theorem eval_split (I : Interpretation Signature.pure B)
    (F : Term Signature.pure [] MaxAtomicitySplitCertificate.SplitterTy) :
    eval I (MaxAtomicitySplitCertificate.split F) .nil = splitValue (eval I F .nil) := by
  simp only [MaxAtomicitySplitCertificate.split,
    MaxAtomicitySplitCertificate.splitParts, eval_forall, eval_imp,
    eval_neg, eval_eq, eval_conj]
  simp only [eval_app, eval_weaken, eval_v0, eval_bot, compl_compl]
  rfl

/-- An evaluated closed term that actually splits yields a non-theorem
certificate for the exact identity used by Max. The missing work in the full
proof is the construction and interpretation of such an F. -/
theorem split_identity_not_C_theorem (I : Interpretation Signature.pure B)
    [Nonempty I.E] [Nontrivial B]
    (F : Term Signature.pure [] MaxAtomicitySplitCertificate.SplitterTy)
    (hsplit : ∀ p : B, p ≠ ⊥ →
      p ⊓ eval I F .nil p ≠ ⊥ ∧ p ⊓ (eval I F .nil p)ᶜ ≠ ⊥) :
    ¬ C.Theorem (Term.eq' (MaxAtomicitySplitCertificate.split F) Term.bot) := by
  apply unequal_values_not_identity I
  rw [eval_split, splitValue_eq_top _ hsplit, eval_bot]
  exact top_ne_bot

end
end Classicism.Meta.Research.MaxAtomicitySplitSemantics

#print axioms Classicism.Meta.Research.MaxAtomicitySplitSemantics.guardedSup_eq_unique
#print axioms Classicism.Meta.Research.MaxAtomicitySplitSemantics.splitValue_eq_top
#print axioms Classicism.Meta.Research.MaxAtomicitySplitSemantics.guardedLeastPart_eq_selector
#print axioms Classicism.Meta.Research.MaxAtomicitySplitSemantics.guardedLeastPart_splits
#print axioms Classicism.Meta.Research.MaxAtomicitySplitSemantics.guardedLeastPart_splitValue
#print axioms Classicism.Meta.Research.MaxAtomicitySplitSemantics.eval_split
#print axioms Classicism.Meta.Research.MaxAtomicitySplitSemantics.split_identity_not_C_theorem
