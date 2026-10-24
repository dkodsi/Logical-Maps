import Classicism.Results.Research.MaxAtomicityJechShelahCylinders
import Classicism.Results.Research.MaxAtomicityHCodeExistence
import Classicism.Semantics.BooleanValuedSoundness
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# The concrete full Boolean-valued interpretation and its universe code

Direct source: the present original formalization (misc, 23 October 2026),
assembling the Jech--Shelah tree completion with the proved HCode construction.

Infinitude is proved by constructing a strictly decreasing sequence of nonzero
Boolean elements. Thus the concrete model's HCode witness does not depend on an
assumed infinite-carrier instance. Soundness is instantiated from the actual C
derivation theorem. Rigidity and the pure selector are not asserted here.
Source awaits the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityConcreteModel

open BooleanValued MaxAtomicityWellOrder
open MaxAtomicityJechShelahTrees MaxAtomicityJechShelahCylinders
open MaxAtomicityHCodeExistence

noncomputable section

private def nextNonzero (b : {b : B // b ≠ ⊥}) : {b : B // b ≠ ⊥} :=
  ⟨Classical.choose (forcing_completion_atomless b.2),
    (Classical.choose_spec (forcing_completion_atomless b.2)).1⟩

private theorem nextNonzero_lt (b : {b : B // b ≠ ⊥}) : (nextNonzero b).1 < b.1 := by
  have h := Classical.choose_spec (forcing_completion_atomless b.2)
  exact lt_of_le_of_ne h.2.1 h.2.2

private def nonzeroChain : ℕ → {b : B // b ≠ ⊥}
  | 0 => ⟨⊤, top_ne_bot⟩
  | n + 1 => nextNonzero (nonzeroChain n)

private theorem chain_strictAnti : StrictAnti (fun n => (nonzeroChain n).1) :=
  strictAnti_nat_of_succ_lt (fun n => nextNonzero_lt (nonzeroChain n))

instance completionInfinite : Infinite B :=
  Infinite.of_injective (fun n => (nonzeroChain n).1) chain_strictAnti.injective

/-- The individual sort is a singleton; all relational arrow domains are full. -/
def interpretation : Interpretation Signature.pure B :=
  Interpretation.ofDomain Unit B

instance : Nonempty interpretation.E := inferInstanceAs (Nonempty Unit)

theorem interpretation_C_sound {p : Sentence Signature.pure} (h : C.Theorem p) :
    eval interpretation p .nil = ⊤ := C_sound interpretation h

/-- The literal finite pure HCode-existence sentence has top value in this
specific full interpretation. Every existence premise has been discharged. -/
theorem interpretation_hasHCode : eval interpretation hasHCode .nil = ⊤ :=
  eval_hasHCode interpretation

/-- The external branch-index selector splits every nonzero proposition.
Identification with a concrete pure term is still a separate obligation. -/
theorem interpretation_external_splitter {b : B} (hb : b ≠ ⊥) :
    b ⊓ branchSplitter b ≠ ⊥ ∧ b ⊓ (branchSplitter b)ᶜ ≠ ⊥ :=
  branchSplitter_splits hb

end

end Classicism.Meta.Research.MaxAtomicityConcreteModel

#print axioms Classicism.Meta.Research.MaxAtomicityConcreteModel.completionInfinite
#print axioms Classicism.Meta.Research.MaxAtomicityConcreteModel.interpretation_C_sound
#print axioms Classicism.Meta.Research.MaxAtomicityConcreteModel.interpretation_hasHCode
#print axioms Classicism.Meta.Research.MaxAtomicityConcreteModel.interpretation_external_splitter
