import Classicism.Results.Research.ModalOldLanguageRoundTrip
import Classicism.Results.Research.ModalReconstructionNameAdapter
import Classicism.Results.Research.ModalFiniteNameErasure
import Classicism.Results.Research.ModalConcreteToCClassical

/-!
# Open local consequence equivalence of the lambda-free base and C

Original research, misc, 23 October 2026. This assembles actual proof
translations, object-identity round trips, finite proof-support restriction,
construction of a finite strong-comprehension definition tower, and its
conservative elimination. None of those steps is a hypothesis of the final
theorem. The only source theory is the explicitly defined classical
lambda-free calculus, with K, theorem-only Nec, all-type Intensionality and
finite-body strong comprehension. No Choice, Barcan or Infinity is added.

Object quantifier binders remain in the base. This is neither a claim of
minimality nor a transfer theorem for signature-sensitive optional schemas.
-/

namespace Classicism.Research.ModalLambdaFreeEquivalence
open Classicism.Meta (Ty Ctx)
open ModalComprehensionConcreteSyntax (Term Formula Derives ClassicalAxioms)
open ModalConcreteToC (signature toC)
open ModalFiniteNameSupport (NamedConst mapTerm)

variable {Const : Ty → Type}

theorem split_old {Γ σ} (p : Term Const Γ σ) :
    mapTerm ModalReconstructionNames.split (ModalOldLanguageRoundTrip.old p) =
      mapTerm NamedConst.old p := by
  induction p <;>
    simp_all only [ModalOldLanguageRoundTrip.old, mapTerm,
      ModalOldLanguageRoundTrip.oldConst, ModalReconstructionNames.split] <;> rfl

/-- All introduced combinator and logical names disappear from the final
old-language proof, even when its context and local premises are open. -/
theorem from_C {Γ} {Δ : List (Formula Const Γ)} {p : Formula Const Γ}
    (h : Classicism.Meta.C.Derivable (Δ.map toC) (toC p)) :
    Derives Const (ClassicalAxioms Const) Γ Δ p := by
  have named := ModalOldLanguageRoundTrip.old_sequent_in_named_extension h
  have independent := ModalReconstructionNames.split_derives named
  apply ModalFiniteNameSupport.independent_names_conservative
    (ModalReconstructionNames.closedBody Const)
  simpa only [List.map_map, Function.comp_def, split_old] using independent

/-- Exact consequence equivalence for each old-language formula and every
finite list of old local premises. All proof relations are concrete. -/
theorem classical_lambda_free_iff_C {Γ}
    (Δ : List (Formula Const Γ)) (p : Formula Const Γ) :
    Derives Const (ClassicalAxioms Const) Γ Δ p ↔
      Classicism.Meta.C.Derivable (Δ.map toC) (toC p) :=
  ⟨ModalConcreteToC.classical_derives_toC, from_C⟩

theorem classical_lambda_free_theorem_iff_C (p : Formula Const []) :
    Derives Const (ClassicalAxioms Const) [] [] p ↔
      Classicism.Meta.C.Derivable [] (toC p) :=
  classical_lambda_free_iff_C [] p

#print axioms from_C
#print axioms classical_lambda_free_iff_C
#print axioms classical_lambda_free_theorem_iff_C

end Classicism.Research.ModalLambdaFreeEquivalence
