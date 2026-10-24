import Classicism.Results.Research.AnalyticReuseQuotation
import Classicism.Syntax.Blocks

/-!
# Deep vocabulary for the finite analytic schema

The object language has only the original simple types. Arity and the finite
list of power witnesses are indices of syntax in the metatheory.
-/

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

noncomputable section

namespace Classicism.Meta.Analytic

/-- Persistence at an arbitrary relational type, retaining the primitive
relational operations until its particular curried type is instantiated. -/
def persist (ρ : RTy) {Γ : Ctx}
    (D : Term Signature.pure Γ ρ) : Formula Signature.pure Γ :=
  Term.box (Term.app (Term.app (.inclR ρ) D) (Term.app (.boxR ρ) D))

/-- Read a quoted lambda's body. The fallback is its eta-expanded application,
so this operation never supplies an unproved mathematical assertion. -/
def lambdaBody {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (f : Term Signature.pure Γ (σ ⇒ ρ)) : Term Signature.pure (σ :: Γ) ρ :=
  match f with
  | .lam b => b
  | f => .app f.weaken Term.v0

def structureTypes (σ : Ty) : List Ty :=
  [σ ⇒ RTy.t, σ ⇒ σ ⇒ RTy.t, σ ⇒ σ ⇒ σ ⇒ RTy.t,
   σ ⇒ σ ⇒ σ ⇒ RTy.t, σ, σ, σ ⇒ RTy.t]

def realCore (σ : Ty) : Formula Signature.pure (Ctx.block (structureTypes σ) []) :=
  lambdaBody (lambdaBody (lambdaBody (lambdaBody (lambdaBody (lambdaBody
    (lambdaBody (Classicism.Research.Analytic.RealCore.term σ)))))))

theorem rigid_real_matrix (σ : Ty) :
    Classicism.Research.Analytic.HasRigidReal.term σ =
      Term.existsBlock (structureTypes σ) (realCore σ) := rfl

end Classicism.Meta.Analytic
