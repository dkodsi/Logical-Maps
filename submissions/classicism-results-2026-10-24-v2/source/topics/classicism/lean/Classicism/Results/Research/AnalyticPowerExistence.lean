import Classicism.Results.Research.AnalyticRepresentedPowers

namespace Classicism.Research.Analytic

/-- The explicit internal family is hidden by ordinary existential introduction.
This form is convenient for assembling a finite simultaneous witness block. -/
theorem exists_represented_power {ρ : Type} [Rel ρ] [Pointwise ρ]
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (P.RigidComprehension ρ)) (D : ρ) (hD : Persistent D) :
    ∃ P, RepresentedPower D P :=
  ⟨PowerFamily D, represented_power c5 nrc D hD⟩

end Classicism.Research.Analytic
