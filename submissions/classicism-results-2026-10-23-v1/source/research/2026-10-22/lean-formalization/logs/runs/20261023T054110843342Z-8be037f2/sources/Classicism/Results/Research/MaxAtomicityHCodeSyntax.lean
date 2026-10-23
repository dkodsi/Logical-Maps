import Classicism.Results.Research.MaxAtomicitySyntax

/-!
# Finite syntax of the hereditary-size universe code

Direct source: max-atomicity-inconsistency-proof.md, section 3 (misc,
22 October 2026, unpaginated local proof). This adds the row-size condition
needed by the constructible-order route to the previously checked Cover term.

These are concrete terms of the original pure language, with fixed closed types.
This module proves syntactic purity and closed types only. The interpretation
of this term as H_(kappa+) and the existence of a code are not assumed or proved.
-/

namespace Classicism.Meta.Research.MaxAtomicityHCodeSyntax

open MaxAtomicitySyntax

/-- Every predecessor row injects into the proposition domain. The injection
in `small` is arbitrary proposition-valued, rather than restricted to crisp maps. -/
def rows {Γ : Ctx} (E : PT Γ ER) : Formula Signature.pure Γ :=
  Term.forall' (σ := U)
    (small (.lam (member E.weaken.weaken Term.v0 Term.v1)))

/-- Well-founded extensional membership, small rows, and filling of small sets. -/
def hCode {Γ : Ctx} (E : PT Γ ER) : Formula Signature.pure Γ :=
  Term.conj (cover E) (rows E)

/-- The literal closed pure lambda term, with no additional logical constant. -/
def hCodeTerm : Term Signature.pure [] ((ER : Ty) ⇒ RTy.t) :=
  .lam (hCode Term.v0)

theorem hCodeTerm_closedTypes : hCodeTerm.closedTypes = true := rfl

theorem hCodeTerm_pure : hCodeTerm.pure = true :=
  hCodeTerm.pure_of_pureSig

end Classicism.Meta.Research.MaxAtomicityHCodeSyntax

#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSyntax.hCodeTerm_closedTypes
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeSyntax.hCodeTerm_pure
