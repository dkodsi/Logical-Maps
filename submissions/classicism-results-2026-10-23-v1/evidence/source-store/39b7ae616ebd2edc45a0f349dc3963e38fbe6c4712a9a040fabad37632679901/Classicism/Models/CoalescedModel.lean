import Classicism.Models.CoalescedLeaf
import Classicism.Semantics.IntensionalFacts

/-!
# Term closure of the coalesced Henkin construction

The terminal evaluations transfer to the given one-world models. At the root,
the root extension of a term can be chosen freely, and its two future extensions
are admitted by the component model conditions. Thus coalescence preserves the
actual `Premodel.IsModel` condition, without an external fullness hypothesis.

This is a generic implementation of the construction in the local record
`models/coalesced-two-extensional-arithmetics-root.yaml`, "definition"
(unpaginated). Component existence and any set-theoretic interpretation of those
components remain separate premises.
-/

namespace Classicism.Meta.Intensional.Coalesced

open CategoryTheory

variable (L R : Premodel Signature.pure One)

theorem left_isInner (hL : L.IsModel) {Γ : Ctx} {σ : Ty}
    (t : Term Signature.pure Γ σ)
    (g : IEnv ((model L R).Dom .left) Γ) :
    (model L R).sem toLeft t g ∈ Set.range ((model L R).Incl σ .left) := by
  obtain ⟨x, hx⟩ := hL (PUnit.unit : L.W₀ ⟶ One.point) t g
  refine ⟨x, ?_⟩
  apply (leftOuter L R σ).injective
  rw [leftOuter_Incl, left_sem]
  exact hx

theorem right_isInner (hR : R.IsModel) {Γ : Ctx} {σ : Ty}
    (t : Term Signature.pure Γ σ)
    (g : IEnv ((model L R).Dom .right) Γ) :
    (model L R).sem toRight t g ∈ Set.range ((model L R).Incl σ .right) := by
  obtain ⟨x, hx⟩ := hR (PUnit.unit : R.W₀ ⟶ One.point) t g
  refine ⟨x, ?_⟩
  apply (rightOuter L R σ).injective
  rw [rightOuter_Incl, right_sem]
  exact hx

/-- A root intension is admitted exactly when its two leaf restrictions are.
The root extension itself is unrestricted. -/
theorem root_isInner_of_leaf_restrictions (ρ : RTy)
    (F : Intension (inner L R) ρ .root)
    (hl : Intension.map (inner L R) toLeft F ∈
      Set.range ((model L R).incl ρ .left))
    (hr : Intension.map (inner L R) toRight F ∈
      Set.range ((model L R).incl ρ .right)) :
    F ∈ Set.range ((model L R).incl ρ .root) := by
  obtain ⟨l, hl⟩ := hl
  obtain ⟨r, hr⟩ := hr
  let E : Set (RootArgs L R ρ) :=
    fun a => F ⟨.root, (rootArgsEquiv L R ρ).symm a, Hom.rootId⟩
  refine ⟨(E, l, r), ?_⟩
  funext p
  rcases p with ⟨V, a, h⟩
  cases h with
  | rootId =>
    change F ⟨.root, (rootArgsEquiv L R ρ).symm (rootArgsEquiv L R ρ a),
      Hom.rootId⟩ = F ⟨.root, a, Hom.rootId⟩
    rw [Equiv.symm_apply_apply]
  | toLeft =>
    exact congrFun hl ⟨.left, a, Hom.leftId⟩
  | toRight =>
    exact congrFun hr ⟨.right, a, Hom.rightId⟩

theorem root_isInner (hL : L.IsModel) (hR : R.IsModel)
    {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ)
    (g : IEnv ((model L R).Dom .root) Γ) :
    (model L R).sem Hom.rootId t g ∈ Set.range ((model L R).Incl σ .root) := by
  cases σ with
  | e => exact ⟨(model L R).sem Hom.rootId t g, rfl⟩
  | var i => exact ⟨(model L R).sem Hom.rootId t g, rfl⟩
  | rel ρ =>
    apply root_isInner_of_leaf_restrictions L R ρ
    · have h := left_isInner L R hL t ((model L R).push toLeft g)
      have e := (model L R).sem_push Hom.rootId t g toLeft
      change (model L R).sem toLeft t ((model L R).push toLeft g) =
        Intension.map (inner L R) toLeft ((model L R).sem Hom.rootId t g) at e
      rw [← e]
      exact h
    · have h := right_isInner L R hR t ((model L R).push toRight g)
      have e := (model L R).sem_push Hom.rootId t g toRight
      change (model L R).sem toRight t ((model L R).push toRight g) =
        Intension.map (inner L R) toRight ((model L R).sem Hom.rootId t g) at e
      rw [← e]
      exact h

/-- Two actual one-world Henkin models yield an actual three-world model of C. -/
theorem isModel (hL : L.IsModel) (hR : R.IsModel) : (model L R).IsModel := by
  intro Γ σ W h t g
  cases h with
  | rootId => exact root_isInner L R hL hR t g
  | toLeft => exact left_isInner L R hL t g
  | toRight => exact right_isInner L R hR t g

/-- The Barcan instance holds at every world when all component domains are
inhabited, since every transition map is surjective. -/
theorem holds_bf (hL : L.IsModel) (hR : R.IsModel)
    (hneL : ∀ σ, Nonempty (L.Dom .point σ))
    (hneR : ∀ σ, Nonempty (R.Dom .point σ))
    (σ : Ty) {W : World} (h : (model L R).W₀ ⟶ W) :
    (model L R).Holds h (Sentence.bf σ) .nil :=
  (model L R).holds_bf_of_surjective (isModel L R hL hR) σ h
    (fun k => map_surjective L R hneL hneR σ k)

theorem holds_box_bf (hL : L.IsModel) (hR : R.IsModel)
    (hneL : ∀ σ, Nonempty (L.Dom .point σ))
    (hneR : ∀ σ, Nonempty (R.Dom .point σ))
    (σ : Ty) {W : World} (h : (model L R).W₀ ⟶ W) :
    (model L R).Holds h (Term.box (Sentence.bf σ)) .nil := by
  rw [(model L R).holds_box (isModel L R hL hR)]
  intro V k
  exact holds_bf L R hL hR hneL hneR σ (h ≫ k)

#print axioms isModel
#print axioms holds_bf
#print axioms holds_box_bf

end Classicism.Meta.Intensional.Coalesced
