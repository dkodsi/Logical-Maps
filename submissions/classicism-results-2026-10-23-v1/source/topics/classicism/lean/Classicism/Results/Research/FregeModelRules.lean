import Classicism.Results.Research.FregeNoncollapseCertificates
import Classicism.Certified.Schemas
import Classicism.Tools.Schema

/-!
# Quoted arithmetic rules for semantic countermodels

Direct source: finite-type-propagation.md, section 9, and the existing
FregeNoncollapse proofs; unpaginated original research (misc), 23 October 2026.
These wrappers expose already proved C implications at arbitrary type codes.
-/

namespace Classicism.Research.FregeModelRules
open FregeNoncollapse FregeFiniteSets

def ActualInfinity (σ : Type) [Ty σ] : Prop := Classicism.P.AxiomOfInfinity σ
def Peano (σ : Type) [Ty σ] : Prop := IStar σ
def Arithmetic (σ : Type) [Ty σ] : Prop := ArithmeticI σ
def NumbersInfinite (σ : Type) [Ty σ] : Prop := ¬ Finite (FiniteCardinality (σ := σ))

theorem infinity_implies_peano {σ : Type} [Ty σ] : ActualInfinity σ → Peano σ :=
  fun h => istar_iff_noncollapse.2 (infinity_implies_noncollapse h)

theorem peano_implies_arithmetic {σ : Type} [Ty σ] : Peano σ → Arithmetic σ :=
  arithmeticI_iff_istar.2

theorem arithmetic_implies_infinite_numbers {σ : Type} [Ty σ] :
    Arithmetic σ → NumbersInfinite σ :=
  fun h => infinite_numbers_iff_noncollapse.2
    (istar_iff_noncollapse.1 (arithmeticI_iff_istar.1 h))

end Classicism.Research.FregeModelRules

#classicism_check Classicism.Research.FregeModelRules.infinity_implies_peano
  Classicism.Research.FregeModelRules.peano_implies_arithmetic
  Classicism.Research.FregeModelRules.arithmetic_implies_infinite_numbers
#classicism_types Classicism.Research.FregeModelRules.infinity_implies_peano
  Classicism.Research.FregeModelRules.peano_implies_arithmetic
  Classicism.Research.FregeModelRules.arithmetic_implies_infinite_numbers
#classicism_schema Classicism.Research.FregeModelRules.ActualInfinity
  Classicism.Research.FregeModelRules.Peano
  Classicism.Research.FregeModelRules.Arithmetic
  Classicism.Research.FregeModelRules.NumbersInfinite
#classicism_certify Classicism.Research.FregeModelRules.infinity_implies_peano
  Classicism.Research.FregeModelRules.peano_implies_arithmetic
  Classicism.Research.FregeModelRules.arithmetic_implies_infinite_numbers

#print axioms Classicism.Research.FregeModelRules.infinity_implies_peano.rule
#print axioms Classicism.Research.FregeModelRules.arithmetic_implies_infinite_numbers.rule
