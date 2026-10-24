import Classicism.Results.Research.FregeNoncollapse
import Classicism.Certified.Arithmetic
import Classicism.Syntax.Normalize
import Classicism.Tools.QuoteTerm

/-!
# Exact syntax bridge for the arithmetic noncollapse condition

Direct source: research/2026-10-22/notes/frege-infinity-20261022-1726.md §26;
relational-coding-recursion-20261022.md §34.2, unpaginated original research, misc.
This is a metalinguistic quotation/conversion certificate. It relates the exact
shallow ArithmeticI used in the new proofs to the existing Meta.arithI sentence,
not merely to an equivalent informal Peano description. The conversion proof
uses the kernel-checked normalizer; it introduces no mathematical axiom.
-/
namespace Classicism.Research.FregeArithmeticQuotation

def ArithmeticCondition (σ : Type) [Ty σ] : Prop :=
  FregeNoncollapse.ArithmeticI σ

end Classicism.Research.FregeArithmeticQuotation

#classicism_quote_term Classicism.Research.FregeArithmeticQuotation.ArithmeticCondition

namespace Classicism.Meta.Research.FregeArithmeticQuotation

/-- The two definitions may differ by beta-redexes, so the exact relation is
object-language conversion rather than an asserted literal syntax identity. -/
theorem arithmeticI_conversion (σ : Ty) :
    Conv (Classicism.Research.FregeArithmeticQuotation.ArithmeticCondition.term σ)
      (Classicism.Meta.arithI σ) :=
  Conv.of_nf 32 _ _ rfl

end Classicism.Meta.Research.FregeArithmeticQuotation

#print axioms Classicism.Research.FregeArithmeticQuotation.ArithmeticCondition.reflect
#print axioms Classicism.Meta.Research.FregeArithmeticQuotation.arithmeticI_conversion
