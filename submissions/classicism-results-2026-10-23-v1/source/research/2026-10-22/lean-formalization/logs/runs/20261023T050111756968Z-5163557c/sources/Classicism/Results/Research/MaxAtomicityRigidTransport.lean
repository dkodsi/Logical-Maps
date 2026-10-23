import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.WellFounded

/-!
# Rigidity and presentation-independent order transport

Direct source: `research/2026-10-22/lean-formalization/
max-atomicity-inconsistency-proof.md`, §5 (unpaginated local proof).

These are external mathematical lemmas about Mathlib Boolean algebras and actual
`OrderIso` maps. An order isomorphism of Boolean algebras preserves their Boolean
operations: Mathlib supplies `map_bot`, `map_top`, `map_inf`, and `map_sup`; the
complement case is given below. Thus `Rigid` is the usual Boolean-algebra
rigidity condition, stated through the order that determines those operations.

Rigidity is an explicit PREMISE. This module does not prove the existence of a
rigid complete atomless Boolean algebra, a definable well-order, a coded copy,
or a pure C term. In particular the well-order relation being transported is
separate from the Boolean algebra's partial order. Presentation invariance
requires that the presentation change preserve that additional relation.

No builds were run by the author; compilation and axiom inspection are pending
the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityRigidTransport

universe u v w

/-- Every Boolean order automorphism is the identity. No existence assertion
or custom axiom is attached to this definition. -/
def Rigid (A : Type u) [BooleanAlgebra A] : Prop :=
  ∀ e : A ≃o A, e = OrderIso.refl A

variable {A : Type u} {B : Type v} {C : Type w}
variable [BooleanAlgebra A] [BooleanAlgebra B] [BooleanAlgebra C]

/-- Order isomorphisms also preserve complement, so using `OrderIso` does not
silently enlarge the automorphism group beyond Boolean-algebra automorphisms. -/
theorem map_compl (f : A ≃o B) (x : A) : f xᶜ = (f x)ᶜ := by
  have h : IsCompl (f x) (f xᶜ) :=
    f.isCompl (isCompl_compl : IsCompl x xᶜ)
  exact h.compl_eq.symm

/-- Rigidity proves, rather than assumes, uniqueness of isomorphisms from A
onto any fixed Boolean-algebra copy. -/
theorem iso_unique (hA : Rigid A) (f g : A ≃o B) : f = g := by
  apply OrderIso.ext
  funext x
  have h : g.symm (f x) = x := by
    simpa only [OrderIso.trans_apply, OrderIso.refl_apply] using
      congrArg (fun e : A ≃o A => e x) (hA (f.trans g.symm))
  calc
    f x = g (g.symm (f x)) := (g.apply_symm_apply (f x)).symm
    _ = g x := congrArg g h

/-- A copy of a rigid Boolean algebra is rigid. -/
theorem rigid_copy (hA : Rigid A) (f : A ≃o B) : Rigid B := by
  intro e
  apply OrderIso.ext
  funext y
  have h := congrArg (fun g : A ≃o B => g (f.symm y))
    (iso_unique hA (f.trans e) f)
  simpa only [OrderIso.trans_apply, OrderIso.apply_symm_apply,
    OrderIso.refl_apply] using h

/-- The unique maps into two copies commute with a change of presentation. -/
theorem presentation_change (hA : Rigid A) (f : A ≃o B)
    (g : A ≃o C) (k : B ≃o C) : f.trans k = g :=
  iso_unique hA (f.trans k) g

/-- Pull back an additional relation on a coded copy. This relation is not
the Boolean order used in the type of `f`. -/
def pullbackRel (f : A ≃o B) (r : B → B → Prop) : A → A → Prop :=
  fun x y => r (f x) (f y)

/-- A well-order on the copy is a well-order after pullback. The required
injectivity comes from the actual isomorphism. -/
theorem pullback_isWellOrder (f : A ≃o B) (r : B → B → Prop)
    [IsWellOrder B r] : IsWellOrder A (pullbackRel f r) := by
  exact f.injective.isWellOrder r

/-- The relation on A is independent of the chosen isomorphism onto a fixed
copy, with no uniqueness premise beyond Boolean-algebra rigidity. -/
theorem pullback_independent (hA : Rigid A) (f g : A ≃o B)
    (r : B → B → Prop) : pullbackRel f r = pullbackRel g r := by
  rw [iso_unique hA f g]

/-- If a presentation change preserves the additional relation, the two
pulled-back relations agree. In the intended application the additional
relations are both presentations of the same canonical coded well-order. -/
theorem pullback_presentation_invariant (hA : Rigid A)
    (f : A ≃o B) (g : A ≃o C) (k : B ≃o C)
    (rB : B → B → Prop) (rC : C → C → Prop)
    (hk : ∀ b₁ b₂, rC (k b₁) (k b₂) ↔ rB b₁ b₂) :
    pullbackRel f rB = pullbackRel g rC := by
  have hfg := presentation_change hA f g k
  funext x y
  apply propext
  have hx : k (f x) = g x := congrArg (fun h : A ≃o C => h x) hfg
  have hy : k (f y) = g y := congrArg (fun h : A ≃o C => h y) hfg
  change rB (f x) (f y) ↔ rC (g x) (g y)
  rw [← hx, ← hy]
  exact (hk (f x) (f y)).symm

end Classicism.Meta.Research.MaxAtomicityRigidTransport

#print axioms Classicism.Meta.Research.MaxAtomicityRigidTransport.map_compl
#print axioms Classicism.Meta.Research.MaxAtomicityRigidTransport.iso_unique
#print axioms Classicism.Meta.Research.MaxAtomicityRigidTransport.rigid_copy
#print axioms Classicism.Meta.Research.MaxAtomicityRigidTransport.presentation_change
#print axioms Classicism.Meta.Research.MaxAtomicityRigidTransport.pullback_isWellOrder
#print axioms Classicism.Meta.Research.MaxAtomicityRigidTransport.pullback_independent
#print axioms Classicism.Meta.Research.MaxAtomicityRigidTransport.pullback_presentation_invariant
