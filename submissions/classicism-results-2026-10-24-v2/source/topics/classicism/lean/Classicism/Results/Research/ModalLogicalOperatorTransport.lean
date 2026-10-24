import Classicism.Results.Research.ModalLogicalOperatorBodies
import Classicism.Results.Research.ModalConcreteProofTransport

/-!
# Logical definition bodies are independent of every signature interpretation

Original research, misc, 23 October 2026. This is the concrete missing
syntax bridge for transporting finite logical-definition names: arbitrary
interpretation of old constants and substitution of old parameters leaves
each logical operator's finite body unchanged. No statement about arbitrary
proof transport or simultaneous representative choice is assumed.
-/

namespace Classicism.Research.ModalLogicalOperators
open Classicism.Meta (Ty RTy)
open ModalComprehensionConcreteSyntax
open ModalFreshConstantSyntax (ConstImage translate translateBody)

variable {C D : Ty → Type}

theorem Unary.translate_apply {Γ Θ} (u : Unary)
    (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) (p : Formula C Γ) :
    translate cs vs (u.apply p) = u.apply (translate cs vs p) := by
  cases u <;> rfl

theorem Binary.translate_apply {Γ Θ} (b : Binary)
    (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) (p q : Formula C Γ) :
    translate cs vs (b.apply p q) = b.apply (translate cs vs p) (translate cs vs q) := by
  cases b <;> rfl

theorem constantBody_translate (ρ : RTy) : ∀ {Γ Θ}
    (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) (p : Formula C Γ),
    translateBody cs vs (constantBody ρ p) = constantBody ρ (translate cs vs p) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [constantBody, translateBody, ih, ModalFreshConstantSyntax.translate_wk]

theorem unaryBody_translate (u : Unary) (ρ : RTy) : ∀ {Γ Θ}
    (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) (X : Term C Γ ρ),
    translateBody cs vs (unaryBody u ρ X) = unaryBody u ρ (translate cs vs X) := by
  induction ρ using RTy.induction with
  | t => intros; simp only [unaryBody, translateBody, Unary.translate_apply]
  | arr σ ρ ih =>
      intros
      simp only [unaryBody, translateBody, ih, translate,
        ModalFreshConstantSyntax.translate_wk, Sub.lift]

theorem binaryBody_translate (b : Binary) (ρ : RTy) : ∀ {Γ Θ}
    (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) (X Y : Term C Γ ρ),
    translateBody cs vs (binaryBody b ρ X Y) =
      binaryBody b ρ (translate cs vs X) (translate cs vs Y) := by
  induction ρ using RTy.induction with
  | t => intros; simp only [binaryBody, translateBody, Binary.translate_apply]
  | arr σ ρ ih =>
      intros
      simp only [binaryBody, translateBody, ih, translate,
        ModalFreshConstantSyntax.translate_wk, Sub.lift]

theorem inclusion_translate (ρ : RTy) : ∀ {Γ Θ}
    (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) (X Y : Term C Γ ρ),
    translate cs vs (inclusion ρ X Y) =
      inclusion ρ (translate cs vs X) (translate cs vs Y) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [inclusion, translate, ih, ModalFreshConstantSyntax.translate_wk, Sub.lift]

/-- Every old constant map is allowed: no operator body uses any constant.
Every old parameter substitution is allowed: all its inputs are bound. -/
theorem LogicalOperator.body_translate {Γ Θ} {ρ : RTy} (o : LogicalOperator ρ)
    (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) :
    translateBody cs vs (o.body (Const := C) Γ) = o.body (Const := D) Θ := by
  cases o <;>
    simp only [LogicalOperator.body, translateBody, constantBody_translate,
      unaryBody_translate, binaryBody_translate, inclusion_translate,
      ModalFreshConstantSyntax.translate_coext, conjunction, disjunction,
      neg, bottom, translate, Sub.lift] <;> rfl

#print axioms LogicalOperator.body_translate

end Classicism.Research.ModalLogicalOperators
