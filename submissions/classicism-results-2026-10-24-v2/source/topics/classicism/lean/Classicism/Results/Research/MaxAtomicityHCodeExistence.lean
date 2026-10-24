import Classicism.Results.Research.MaxAtomicityHereditaryUniverse
import Classicism.Results.Research.MaxAtomicityHCodeSemantics

/-!
# Existence of the actual finite universe code

Direct source: the original universe-code proof, section 3 of
`max-atomicity-inconsistency-proof.md` (misc, unpaginated).

The witness is constructed from the W-type presentation and its proved
cardinality. This module connects that witness to the exact existing HCode
syntax. It does not assume a good membership relation or a semantic adequacy
axiom. All relations quantified over are in the full higher-type domain.

The conclusion here is only that the finite existential HCode sentence has
value top. No rigid algebra or pure selector has yet been constructed here.
Source awaits checking by the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityHCodeExistence

open BooleanValued MaxAtomicitySyntax MaxAtomicitySetSemantics
open MaxAtomicityHCodeSyntax MaxAtomicityHCodeSemantics
open MaxAtomicityHereditaryUniverse

noncomputable section

variable {B : Type} [CompleteBooleanAlgebra B] [Nontrivial B] [Infinite B]

theorem codeRelation_good : GoodRelation (B := B) (codeRelation B) := by
  refine ⟨⟨codeRelation_extensional B, codeRelation_wellFounded B, ?_⟩, ?_⟩
  · intro P hP
    exact codeRelation_fills B {x | P x} ((small_iff_embedding P).1 hP)
  · intro u
    exact (small_iff_embedding (fun v => codeRelation B v u)).2 (codeRelation_rows B u)

/-- A literal closed pure sentence; the witness is not added as a constant. -/
def hasHCode : Formula Signature.pure [] :=
  Term.exists' (σ := ER) (hCode Term.v0)

theorem hasHCode_pure : hasHCode.pure = true := hasHCode.pure_of_pureSig

theorem hasHCode_closedTypes : hasHCode.closedTypes = true := rfl

/-- The concrete crisp membership relation belongs to the quantified domain. -/
def witness : (B → B) → (B → B) → B :=
  fun x y => truth (codeRelation B x y)

theorem eval_witness_hCode (I : Interpretation Signature.pure B) :
    eval I (hCode (Term.v0 : PT [(ER : Ty)] ER))
      (.cons (witness (B := B)) .nil) = ⊤ := by
  rw [eval_hCode I Term.v0 (.cons (witness (B := B)) .nil)
    (codeRelation B) (fun _ _ => rfl)]
  exact (truth_eq_top_iff _).2 codeRelation_good

/-- Existence is proved for every infinite nontrivial complete Boolean algebra,
not assumed for the later specific model. -/
theorem eval_hasHCode (I : Interpretation Signature.pure B) :
    eval I hasHCode .nil = ⊤ := by
  apply top_le_iff.mp
  change ⊤ ≤ ⨆ E : Dom I.E B ER,
    eval I (hCode (Term.v0 : PT [(ER : Ty)] ER)) (.cons E .nil)
  calc
    ⊤ = eval I (hCode (Term.v0 : PT [(ER : Ty)] ER))
        (.cons (witness (B := B)) .nil) := (eval_witness_hCode I).symm
    _ ≤ ⨆ E : Dom I.E B ER,
        eval I (hCode (Term.v0 : PT [(ER : Ty)] ER)) (.cons E .nil) :=
      le_iSup (fun E : Dom I.E B ER =>
        eval I (hCode (Term.v0 : PT [(ER : Ty)] ER)) (.cons E .nil))
        (witness (B := B))

end

end Classicism.Meta.Research.MaxAtomicityHCodeExistence

#print axioms Classicism.Meta.Research.MaxAtomicityHCodeExistence.codeRelation_good
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeExistence.hasHCode_pure
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeExistence.hasHCode_closedTypes
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeExistence.eval_witness_hCode
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeExistence.eval_hasHCode
