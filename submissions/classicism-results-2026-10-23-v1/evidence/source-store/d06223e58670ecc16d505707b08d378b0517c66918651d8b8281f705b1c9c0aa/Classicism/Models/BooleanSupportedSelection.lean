import Classicism.Models.BooleanSelectingWeights
import Classicism.Models.BooleanGroundCoverage

/-!
# An actual supported selecting profile for covered relational outputs

Original supporting formalization (misc), 23 October 2026, of section 6
of `research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
The output space is the actual space of supported coherent predicates.
Given its canonical fixed ground names and their coverage, a supported
binary relation yields an actual supported selecting profile. Its support
is the same finite support as the relation. Slicing at a supported input
gives an admitted output and attains the exact existential row value.

Coverage is an explicit interface supplied for the concrete protected
hierarchy by `BooleanProtectedCoverage`; no seriality-at-top assumption,
unrestricted mixing constructor, or typed Choice verdict is postulated.
The final translation to the original quoted Choice sentence is separate.
-/

namespace Classicism.Meta.ChoiceBoolean.SupportedSelection

open GroundChecks

variable {K B : Type} [CompleteBooleanAlgebra B] {a : BooleanAction K B}

noncomputable section

private def meet {Z : EqualitySpace B} (f g : Predicate Z) : Predicate Z where
  toFun x := f x ⊓ g x
  coherent x y :=
    le_inf
      ((inf_le_inf_left _ inf_le_left).trans (f.coherent x y))
      ((inf_le_inf_left _ inf_le_right).trans (g.coherent x y))

private def join {Z : EqualitySpace B} (f g : Predicate Z) : Predicate Z where
  toFun x := f x ⊔ g x
  coherent x y := by
    rw [inf_sup_left]
    exact sup_le ((f.coherent x y).trans le_sup_left)
      ((g.coherent x y).trans le_sup_right)

private def onLeft {X Y : EqualitySpace B} (f : Predicate X) : Predicate (prod X Y) where
  toFun p := f p.1
  coherent p q := (inf_le_inf_right _ inf_le_left).trans (f.coherent p.1 q.1)

private def onRight {X Y : EqualitySpace B} (f : Predicate Y) : Predicate (prod X Y) where
  toFun p := f p.2
  coherent p q := (inf_le_inf_right _ inf_le_right).trans (f.coherent p.2 q.2)

variable {X A : ActionSpace a} {G : Type} [LinearOrder G]
variable (c : GroundMap (supportedPredicateSpace A) G)
variable (R : SupportedPredicate (ActionSpace.product X (supportedPredicateSpace A)))

def row (g : G) : Predicate X.space := Predicate.sectionRight R.val (c.check g)

private def earlierRow (g : G) : Predicate X.space :=
  Predicate.ex (fun j : {j : G // j < g} => row c R j.val)

private theorem earlierRow_apply (g : G) (x : X.space.Carrier) :
    earlierRow c R g x = SelectingWeights.earlier (fun j => row c R j x) g := by
  change (⨆ j : {j : G // j < g}, row c R j.val x) =
    ⨆ j : G, ⨆ (_ : j < g), row c R j x
  exact iSup_subtype

def rowWeight (g : G) : Predicate X.space :=
  meet (row c R g) (Predicate.neg (earlierRow c R g))

theorem rowWeight_apply (g : G) (x : X.space.Carrier) :
    rowWeight c R g x = SelectingWeights.weight (fun j => row c R j x) g := by
  exact congrArg (fun b => row c R g x ⊓ bᶜ) (earlierRow_apply c R g x)

def defaultRow : Predicate X.space := Predicate.neg (Predicate.ex (row c R))

/-- The whole output is a single coherent predicate on input and remaining
output arguments. Coherence is proved by the predicate constructors. -/
def profile (g₀ : G) : Predicate (prod X.space A.space) :=
  join
    (meet (onLeft (defaultRow c R)) (onRight (c.check g₀).val))
    (Predicate.ex (fun g =>
      meet (onLeft (rowWeight c R g)) (onRight (c.check g).val)))

theorem profile_apply (g₀ : G) (x : X.space.Carrier) (z : A.space.Carrier) :
    profile c R g₀ (x, z) =
      SelectingWeights.mix
        (fun g => Predicate.toFun
          (X := (ActionSpace.product X (supportedPredicateSpace A)).space) R.val (x, c.check g))
        (Predicate.toFun (X := A.space) (c.check g₀).val z)
        (fun g => Predicate.toFun (X := A.space) (c.check g).val z) := by
  change (defaultRow c R x ⊓ Predicate.toFun (X := A.space) (c.check g₀).val z ⊔
    ⨆ g, rowWeight c R g x ⊓ Predicate.toFun (X := A.space) (c.check g).val z) = _
  simp only [rowWeight_apply, defaultRow, Predicate.neg, Predicate.ex,
    row, Predicate.sectionRight, SelectingWeights.mix,
    SelectingWeights.defaultWeight, SelectingWeights.rowValue]

/-- One common support, inherited from R, supports the full weighted
profile. Ground indices and all checked output profiles remain fixed. -/
theorem profile_supports (g₀ : G) {S : Set K}
    (hR : (predicateAction (ActionSpace.product X (supportedPredicateSpace A))).Supports S R.val) :
    (predicateAction (ActionSpace.product X A)).Supports S (profile c R g₀) := by
  intro π hπ
  apply Predicate.ext
  intro p
  change X.space.Carrier × A.space.Carrier at p
  rcases p with ⟨x, z⟩
  have hRπ := hR π hπ
  change actPredicate (ActionSpace.product X (supportedPredicateSpace A)) π R.val = R.val at hRπ
  have hr (g : G) :
      a.map π (Predicate.toFun
        (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
        R.val (X.action.act π⁻¹ x, c.check g)) =
      Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
        R.val (x, c.check g) := by
    have h := congrArg
      (fun F : Predicate (prod X.space (supportedPredicateSpace A).space) =>
        F (x, c.check g)) hRπ
    change a.map π (Predicate.toFun
      (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
      R.val (X.action.act π⁻¹ x, (supportedPredicateSpace A).action.act π⁻¹ (c.check g))) =
      Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
        R.val (x, c.check g) at h
    simpa only [c.fixed] using h
  have hg (g : G) :
      a.map π (Predicate.toFun (X := A.space) (c.check g).val (A.action.act π⁻¹ z)) =
        Predicate.toFun (X := A.space) (c.check g).val z := by
    have h := congrArg
      (fun F : SupportedPredicate A => Predicate.toFun (X := A.space) F.val z) (c.fixed π g)
    exact h
  change a.map π (profile c R g₀
    (X.action.act π⁻¹ x, A.action.act π⁻¹ z)) = profile c R g₀ (x, z)
  simp only [profile_apply, SelectingWeights.map_mix]
  change SelectingWeights.mix
    (fun g => a.map π (Predicate.toFun
      (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
      R.val (X.action.act π⁻¹ x, c.check g)))
    (a.map π (Predicate.toFun (X := A.space) (c.check g₀).val (A.action.act π⁻¹ z)))
    (fun g => a.map π (Predicate.toFun (X := A.space) (c.check g).val (A.action.act π⁻¹ z))) =
      SelectingWeights.mix
        (fun g => Predicate.toFun
          (X := (ActionSpace.product X (supportedPredicateSpace A)).space) R.val (x, c.check g))
        (Predicate.toFun (X := A.space) (c.check g₀).val z)
        (fun g => Predicate.toFun (X := A.space) (c.check g).val z)
  rw [funext hr, hg g₀, funext hg]

/-- The selecting profile is an actual admitted entity. -/
def selector (g₀ : G) : SupportedPredicate (ActionSpace.product X A) := by
  refine ⟨profile c R g₀, ?_⟩
  obtain ⟨S, hS, hR⟩ := R.property
  exact ⟨S, hS, profile_supports c R g₀ hR⟩

def output (g₀ : G) (x : X.space.Carrier) (hx : X.action.FinitelySupported x) :
    SupportedPredicate A :=
  supportedSectionLeft X A (selector c R g₀) x hx

theorem weight_le_output_eqv (g₀ : G) (x : X.space.Carrier)
    (hx : X.action.FinitelySupported x) (g : G) :
    SelectingWeights.weight
      (fun j => Predicate.toFun
        (X := (ActionSpace.product X (supportedPredicateSpace A)).space) R.val (x, c.check j)) g ≤
      (supportedPredicateSpace A).space.eqv (output c R g₀ x hx) (c.check g) := by
  change SelectingWeights.weight
    (fun j => Predicate.toFun
      (X := (ActionSpace.product X (supportedPredicateSpace A)).space) R.val (x, c.check j)) g ≤
    ⨅ z, iffValue (profile c R g₀ (x, z)) (Predicate.toFun (X := A.space) (c.check g).val z)
  apply le_iInf
  intro z
  rw [profile_apply]
  exact SelectingWeights.weight_le_mix_iff _ _ _ g

/-- Coverage identifies an arbitrary coherent existential row with the
join of its values at canonical ground names. -/
theorem iSup_eq_checks {Y : ActionSpace a} {H : Type}
    (d : GroundMap Y H) (hd : Covers d) (f : Predicate Y.space) :
    (⨆ y, f y) = ⨆ g : H, f (d.check g) := by
  apply le_antisymm
  · apply iSup_le
    intro y
    calc
      f y = f y ⊓ (⨆ g : H, Y.space.eqv y (d.check g)) := by rw [hd, inf_top_eq]
      _ = ⨆ g : H, f y ⊓ Y.space.eqv y (d.check g) :=
        inf_iSup_eq (f y) (fun g : H => Y.space.eqv y (d.check g))
      _ ≤ ⨆ g : H, f (d.check g) := by
        apply iSup_le
        intro g
        apply le_trans ?_ (le_iSup (fun h => f (d.check h)) g)
        simpa only [inf_comm] using f.coherent y (d.check g)
  · apply iSup_le
    intro g
    exact le_iSup f.toFun (d.check g)

/-- The selected output attains the exact existential row value. There is
no assumption that this row, or global seriality, has Boolean value top. -/
theorem row_equation [WellFoundedLT G] (hc : Covers c) (g₀ : G)
    (x : X.space.Carrier) (hx : X.action.FinitelySupported x) :
    Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
      R.val (x, output c R g₀ x hx) =
      ⨆ y : SupportedPredicate A,
        Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
          R.val (x, y) := by
  apply le_antisymm
  · exact le_iSup
      (fun y : SupportedPredicate A => Predicate.toFun
        (X := (ActionSpace.product X (supportedPredicateSpace A)).space) R.val (x, y))
      (output c R g₀ x hx)
  · have hchecks :
        (⨆ y : SupportedPredicate A,
          Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
            R.val (x, y)) =
        ⨆ g : G,
          Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
            R.val (x, c.check g) :=
      iSup_eq_checks c hc (Predicate.sectionLeft R.val x)
    apply le_trans hchecks.le
    change SelectingWeights.rowValue
      (fun g => Predicate.toFun
        (X := (ActionSpace.product X (supportedPredicateSpace A)).space) R.val (x, c.check g)) ≤ _
    rw [← SelectingWeights.iSup_weight]
    apply iSup_le
    intro g
    have he : SelectingWeights.weight
        (fun j => Predicate.toFun
          (X := (ActionSpace.product X (supportedPredicateSpace A)).space) R.val (x, c.check j)) g ≤
        (supportedPredicateSpace A).space.eqv (c.check g) (output c R g₀ x hx) := by
      rw [(supportedPredicateSpace A).space.symm]
      exact weight_le_output_eqv c R g₀ x hx g
    have hsub : (supportedPredicateSpace A).space.eqv (c.check g) (output c R g₀ x hx) ⊓
        Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
          R.val (x, c.check g) ≤
        Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
          R.val (x, output c R g₀ x hx) := by
      simpa only [prod, X.space.refl, top_inf_eq] using
        Predicate.coherent (X := prod X.space (supportedPredicateSpace A).space)
          R.val (x, c.check g) (x, output c R g₀ x hx)
    exact (le_inf he (SelectingWeights.weight_le _ g)).trans hsub

/-- Taking the meet of the exact row equations retains every Boolean
degree of global seriality. -/
theorem seriality_equation [WellFoundedLT G] (hc : Covers c) (g₀ : G)
    (hx : ∀ x : X.space.Carrier, X.action.FinitelySupported x) :
    (⨅ x : X.space.Carrier,
      Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
        R.val (x, output c R g₀ x (hx x))) =
      ⨅ x : X.space.Carrier, ⨆ y : SupportedPredicate A,
        Predicate.toFun (X := (ActionSpace.product X (supportedPredicateSpace A)).space)
          R.val (x, y) := by
  apply iInf_congr
  intro x
  exact row_equation c R hc g₀ x (hx x)

end

end Classicism.Meta.ChoiceBoolean.SupportedSelection
