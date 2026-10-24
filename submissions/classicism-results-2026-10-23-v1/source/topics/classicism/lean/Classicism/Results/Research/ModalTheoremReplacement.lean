import Classicism.Results.Research.ModalComprehensionConcreteCalculus

/-!
# Theorem-level replacement in the lambda-free calculus

Original research, misc, 23 October 2026. Intensionality and theorem-only
Nec recover literal identity from logical interderivability. Equality then
permits replacement in any admitted formula matrix, including matrices with
quantifier binders. These are actual source derivations.

This does not by itself translate a C hole lying under a lambda: such a
translation also needs coherence between the names of the two abstractions.
The base theorem deliberately has no proper global axioms. A separate
conditional rule consumes an explicitly boxed guard rather than
necessitating a local assumption.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax.Derives
open Classicism.Meta

variable {Const : Ty → Type}

/-- Logical interderivability supplies a theorem of literal propositional
identity. No rule for replacing material equivalents is assumed. -/
theorem interderivable_identity {Γ} {p q : Formula Const Γ}
    (hpq : Derives Const (noAdditionalAxioms Const) Γ [p] q)
    (hqp : Derives Const (noAdditionalAxioms Const) Γ [q] p) :
    Derives Const (noAdditionalAxioms Const) Γ [] (.eq p q) :=
  .intensionality .t p q (.nec (.iffI (.impI hpq) (.impI hqp)))

/-- The premises witnessing interderivability are logical theorems after
discharge; the context to which replacement is applied can have arbitrary
local assumptions. -/
theorem theorem_replacement {Γ Δ} {p q : Formula Const Γ}
    (hpq : Derives Const (noAdditionalAxioms Const) Γ [p] q)
    (hqp : Derives Const (noAdditionalAxioms Const) Γ [q] p)
    (R : Formula Const (Ty.t :: Γ))
    (hR : Derives Const (noAdditionalAxioms Const) Γ Δ (R.inst p)) :
    Derives Const (noAdditionalAxioms Const) Γ Δ (R.inst q) :=
  .eqSubst R p q (.lift (interderivable_identity hpq hqp)) hR

/-- A necessary guard licenses an instance of Intensionality through K.
The unboxed guard is never treated as a theorem. -/
theorem guarded_intensionality {Ax : Axioms Const} {Γ Δ}
    (ρ : RTy) (a b : Term Const Γ ρ) (g : Formula Const Γ)
    (conditional : Derives Const Ax Γ [] (.imp g (Term.coext ρ a b)))
    (guard : Derives Const Ax Γ Δ g.box) :
    Derives Const Ax Γ Δ (.eq a b) :=
  .intensionality ρ a b (.K (.lift (.nec conditional)) guard)

#print axioms interderivable_identity
#print axioms theorem_replacement
#print axioms guarded_intensionality

end Classicism.Research.ModalComprehensionConcreteSyntax.Derives
