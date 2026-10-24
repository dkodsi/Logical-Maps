import Classicism.Models.BooleanConditionCompletion
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Hom.CompleteLattice

/-!
# Automorphisms of the concrete condition completion

Original formalization (misc), 23 October 2026, supporting section 2 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
Every actual order isomorphism of condition preorders induces an actual
complete Boolean algebra isomorphism, carrying each condition cone to
the corresponding cone. The permutation action on the particular column
conditions is a separate instantiation; no action or model verdict is
assumed into existence by this module.
-/

namespace Classicism.Meta.ChoiceBoolean.ConditionCompletion

universe u v w

/-- Regular elements are preserved by order isomorphisms of frames. -/
def regularMap {A : Type u} {C : Type v} [Order.Frame A] [Order.Frame C]
    (f : A ≃o C) : Heyting.Regular A ≃o Heyting.Regular C where
  toFun a := ⟨f a, by
    change (f (a : A))ᶜᶜ = f (a : A)
    rw [← map_compl, ← map_compl, a.prop.eq]⟩
  invFun b := ⟨f.symm b, by
    change (f.symm (b : C))ᶜᶜ = f.symm (b : C)
    rw [← map_compl, ← map_compl, b.prop.eq]⟩
  left_inv a := by
    apply Heyting.Regular.coe_injective
    exact f.symm_apply_apply (a : A)
  right_inv b := by
    apply Heyting.Regular.coe_injective
    exact f.apply_symm_apply (b : C)
  map_rel_iff' := f.map_rel_iff

@[simp] theorem regularMap_coe {A : Type u} {C : Type v}
    [Order.Frame A] [Order.Frame C] (f : A ≃o C) (a : Heyting.Regular A) :
    (regularMap f a : C) = f (a : A) := rfl

theorem regularMap_toRegular {A : Type u} {C : Type v}
    [Order.Frame A] [Order.Frame C] (f : A ≃o C) (a : A) :
    regularMap f (Heyting.Regular.toRegular a) = Heyting.Regular.toRegular (f a) := by
  apply Heyting.Regular.coe_injective
  simp only [regularMap_coe, Heyting.Regular.coe_toRegular, map_compl]

variable {P : Type u} {Q : Type v} {R : Type w}
variable [Preorder P] [Preorder Q] [Preorder R]

def map (f : P ≃o Q) : Algebra P ≃o Algebra Q := regularMap (LowerSet.map f)

theorem lowerMap_principal (f : P ≃o Q) (p : P) :
    LowerSet.map f (principal P p) = principal Q (f p) := by
  apply SetLike.ext
  intro q
  simp only [LowerSet.mem_map, mem_principal]
  exact f.symm_apply_le

@[simp] theorem map_cone (f : P ≃o Q) (p : P) : map f (cone P p) = cone Q (f p) := by
  change regularMap (LowerSet.map f) (Heyting.Regular.toRegular (principal P p)) = _
  rw [regularMap_toRegular, lowerMap_principal] <;> rfl

@[simp] theorem map_refl (b : Algebra P) : map (OrderIso.refl P) b = b := by
  apply Heyting.Regular.coe_injective
  change LowerSet.map (OrderIso.refl P) (b : LowerSet P) = (b : LowerSet P)
  rw [LowerSet.map_refl] <;> rfl

theorem map_comp (f : P ≃o Q) (g : Q ≃o R) (b : Algebra P) :
    map g (map f b) = map (f.trans g) b := by
  apply Heyting.Regular.coe_injective
  exact LowerSet.map_map g f

/-- Infinite truth operations are preserved, not merely finite lattice
operations. This is what quantified formula equivariance uses. -/
theorem map_join (f : P ≃o Q) {I : Type*} (a : I → Algebra P) :
    map f (⨆ i, a i) = ⨆ i, map f (a i) := map_iSup (map f) a

theorem map_meet (f : P ≃o Q) {I : Type*} (a : I → Algebra P) :
    map f (⨅ i, a i) = ⨅ i, map f (a i) := map_iInf (map f) a

theorem map_complement (f : P ≃o Q) (a : Algebra P) :
    map f aᶜ = (map f a)ᶜ := map_compl (map f) a

end Classicism.Meta.ChoiceBoolean.ConditionCompletion
