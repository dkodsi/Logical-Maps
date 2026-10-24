import Classicism.Results.Research.InfinitaryComprehensionActionConsequences
import Classicism.Semantics.FullModels

/-!
# Full action models validate the actual infinitary language and schema

Direct source: `research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md`, section 6, and the observer companion,
section 4; misc, 23 October 2026, unpaginated.

This uses the original intensional categorical models, with possibly
changing domains and noninvertible arrows. No C5, constant domains, or
world separation is imposed. Fullness is the existing construction's
surjectivity onto all tuple intensions. It supplies witnesses for the
recursively interpreted terms and for the concrete Comprehension formula.
Thus an existing full action countermodel extends to the new language;
its old finite-sentence failures are not removed by adding that syntax.
-/

namespace Classicism.Research.InfinitaryComprehension.Canonical
open Classicism.Meta
open Classicism.Meta.Intensional
open CategoryTheory

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C)

/-- At relational types, fullness contains every outer denotation. At
individual and auxiliary variable types, the grammar has only variables
and parameters, whose interpretations are admitted by definition. -/
theorem full_closed (hF : A.Full) : Closed A := by
  intro Param η Γ σ W h p g
  cases σ with
  | e =>
      cases p with
      | var v => exact ⟨g.get v, rfl⟩
      | param a => exact ⟨(A.inner Ty.e).map h (η a), rfl⟩
  | rel ρ =>
      exact hF ρ W (sem A η h p g)
  | var n =>
      cases p with
      | var v => exact ⟨g.get v, rfl⟩
      | param a => exact ⟨(A.inner (Ty.var n)).map h (η a), rfl⟩

/-- Fullness provides the intension of the actual matrix throughout the
future diagram; the general syntax/profile theorem then gives boxed Comp. -/
theorem full_comprehension (hF : A.Full) : Comprehension A := by
  intro Param η Γ p
  apply (comprehension_profile_iff A η (full_closed A hF) p).2
  exact hF (RTy.ofArgs Γ) A.W₀ (formulaProfile A η p)

/-- A finite failure in a specified full model survives its infinitary
expansion. This does not replace construction of the finite countermodel. -/
theorem full_countermodel_expands (hF : A.Full)
    (p : Classicism.Meta.Sentence Sig) (hp : ¬ A.HoldsSentence p) :
    Closed A ∧ Comprehension A ∧ ¬ A.HoldsSentence p :=
  ⟨full_closed A hF, full_comprehension A hF, hp⟩

#print axioms full_closed
#print axioms full_comprehension
#print axioms full_countermodel_expands

end Classicism.Research.InfinitaryComprehension.Canonical
