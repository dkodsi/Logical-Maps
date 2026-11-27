import Classicism.Completeness.TypeVariables
import Classicism.Coalesced.DistinguishedDefinable
import Classicism.StrongPossibility.TypedSignature

/-! Existence at the variable sorts, evaluated at the actual root or at a
specified history. In the distinguished definable construction the root
elements of a variable sort are exactly the typed names of that sort. -/

namespace Classicism.Meta.Intensional.Premodel

open CategoryTheory

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-- One native existence instance at an arbitrary history. -/
theorem holds_exists_self_iff (M : A.IsModel) {W : C} (h : A.W₀ ⟶ W)
    (σ : Ty) :
    A.Holds h (Term.exists' (σ := σ) (Term.eq' (Term.var .zero) (Term.var .zero))) .nil ↔
      Nonempty (A.Dom W σ) := by
  rw [A.holds_exists M]
  exact ⟨fun ⟨x, _⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨x, (A.holds_eq M _ _ _ _).2 rfl⟩⟩

/-- The variable-existence schema quantifies over the variable sorts at the
designated point. -/
theorem holdsAx_varExistence_iff (M : A.IsModel) :
    A.HoldsAx AxiomSet.varExistence ↔ ∀ i, Nonempty (A.Dom A.W₀ (.var i)) := by
  constructor
  · intro H i
    exact (A.holds_exists_self_iff M (𝟙 _) (.var i)).1 (H _ ⟨i, rfl⟩)
  · rintro H _ ⟨i, rfl⟩
    exact (A.holds_exists_self_iff M (𝟙 _) (.var i)).2 (H i)

/-- Existing variable witnesses transport to the distinguished point at the
end of any specified history. -/
theorem holdsAx_varExistence_truncate (M : A.IsModel) (H : A.HoldsAx AxiomSet.varExistence)
    {W : C} (h : A.W₀ ⟶ W) : (A.truncate h).HoldsAx AxiomSet.varExistence := by
  apply ((A.truncate h).holdsAx_varExistence_iff (A.isModel_truncate h M)).2
  intro i
  obtain ⟨x⟩ := (A.holdsAx_varExistence_iff M).1 H i
  exact ⟨(A.inner (.var i)).map h x⟩

end Classicism.Meta.Intensional.Premodel

namespace Classicism.Meta.Coalesced.DistinguishedDefinable

open CategoryTheory Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
variable (A : ∀ k, Premodel Sig (C k)) (ne : Nonempty (names (Sig := Sig) .e))

/-- This new point has exactly one variable-sort element per typed name.
Component witnesses alone do not supply elements of its variable domains. -/
theorem holdsAx_varExistence_iff_names (M : ∀ k, (A k).IsModel) :
    (model A ne).HoldsAx AxiomSet.varExistence ↔
      ∀ i, Nonempty (names (Sig := Sig) (.var i)) :=
  (model A ne).holdsAx_varExistence_iff (isModel A ne M)

end Classicism.Meta.Coalesced.DistinguishedDefinable

namespace Classicism.Meta.TypedSignature

open CategoryTheory Intensional

variable {Sig Extra : Signature} {C : Type} [SmallCategory C]

/-- Forgetting a family of auxiliary constants preserves variable existence,
even when none of those variable sorts has a name in the old signature. -/
theorem holdsAx_varExistence_restrict_iff (B : Premodel (sum Sig Extra) C) (M : B.IsModel) :
    (restrict B).HoldsAx AxiomSet.varExistence ↔ B.HoldsAx AxiomSet.varExistence :=
  ((restrict B).holdsAx_varExistence_iff (restrict_isModel B M)).trans
    (B.holdsAx_varExistence_iff M).symm

end Classicism.Meta.TypedSignature

namespace Classicism.Meta.Coalesced.DistinguishedDefinable

open CategoryTheory Intensional TypedSignature

variable {Sig Extra : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]

/-- A fresh name in each variable sort suffices at the enlarged distinguished
root. After forgetting them, the witnesses remain in its inner carriers. -/
theorem restricted_model_holdsAx_varExistence
    (A : ∀ k, Premodel (sum Sig Extra) (C k))
    (ne : Nonempty (names (Sig := sum Sig Extra) .e)) (M : ∀ k, (A k).IsModel)
    (v : ∀ i, ∃ c : Extra.Const, Extra.typeOf c = .var i) :
    (restrict (model A ne)).HoldsAx AxiomSet.varExistence := by
  apply (holdsAx_varExistence_restrict_iff _ (isModel A ne M)).2
  apply (holdsAx_varExistence_iff_names A ne M).2
  intro i
  obtain ⟨c, hc⟩ := v i
  exact ⟨⟨.inr c, hc⟩⟩

end Classicism.Meta.Coalesced.DistinguishedDefinable
