import Classicism.Results.Research.FullLogicalObserversFiniteSchemasConsRule

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.RuleSubstitution

/- These identities expose only the outer constructors of a substitution.
   Arbitrary qualification terms remain opaque; fixed logical constants are
   reduced definitionally after these rewrites. -/
theorem instantiate_app {Γ : Ctx} {τ σ : Ty} {ρ : RTy}
    (f : Term Signature.pure (τ :: Γ) (σ ⇒ ρ))
    (x : Term Signature.pure (τ :: Γ) σ) (a : Term Signature.pure Γ τ) :
    (Term.app f x).instantiate a =
      Term.app (f.instantiate a) (x.instantiate a) := rfl

theorem instantiate_var {Γ : Ctx} {τ : Ty}
    (a : Term Signature.pure Γ τ) :
    (Term.var (.zero : Var (τ :: Γ) τ)).instantiate a = a := rfl

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.RuleSubstitution
