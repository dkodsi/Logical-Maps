import Classicism.Models.BooleanTypedHierarchy
import Classicism.Models.ChoiceFirstOrderFull

/-!
# Canonical ground checks in the actual supported hierarchy

Original formalization (misc), 23 October 2026, of section 5 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
The check of a ground predicate is its equality-weighted extension to all
Boolean arguments. These checks are fixed by every permutation and preserve
crisp ground equality. No coverage, elementarity, or assertion that a
checked universal predicate is globally universal is assumed or claimed.
-/

namespace Classicism.Meta.ChoiceBoolean.GroundChecks

open TypedHierarchy

variable {K B : Type} [CompleteBooleanAlgebra B] {a : BooleanAction K B}

noncomputable section

open scoped Classical

/-- An actual map of ground entities, with its proved invariance/isometry. -/
structure GroundMap (X : ActionSpace a) (G : Type) where
  check : G → X.space.Carrier
  eqv : ∀ x y, X.space.eqv (check x) (check y) = (crispSpace G).eqv x y
  fixed : ∀ π x, X.action.act π (check x) = check x

def crisp (a : BooleanAction K B) (G : Type) : GroundMap (ActionSpace.crisp a G) G where
  check := id
  eqv _ _ := rfl
  fixed _ _ := rfl

def product {X Y : ActionSpace a} {G H : Type}
    (c : GroundMap X G) (d : GroundMap Y H) :
    GroundMap (ActionSpace.product X Y) (G × H) where
  check p := (c.check p.1, d.check p.2)
  eqv p q := by
    classical
    change X.space.eqv (c.check p.1) (c.check q.1) ⊓
      Y.space.eqv (d.check p.2) (d.check q.2) = (crispSpace (G × H)).eqv p q
    rw [c.eqv, d.eqv]
    by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2 <;>
      simp [crispSpace, Prod.ext_iff, h₁, h₂]
  fixed π p := Prod.ext (c.fixed π p.1) (d.fixed π p.2)

variable {X : ActionSpace a} {G : Type} (c : GroundMap X G)

/-- Equality-weighted extension of a literal ground subset. -/
def checkedPredicate (g : Set G) : Predicate X.space where
  toFun x := ⨆ z : G, if z ∈ g then X.space.eqv x (c.check z) else ⊥
  coherent x y := by
    classical
    rw [inf_iSup_eq]
    apply iSup_le
    intro z
    by_cases hz : z ∈ g
    · simp only [if_pos hz]
      have ht : X.space.eqv x y ⊓ X.space.eqv x (c.check z) ≤
          X.space.eqv y (c.check z) := by
        rw [X.space.symm x y]
        exact X.space.trans y x (c.check z)
      exact ht.trans (le_iSup_of_le z (by simp only [if_pos hz, le_refl]))
    · simp only [if_neg hz, inf_bot_eq]
      exact bot_le

theorem checkedPredicate_apply_check (g : Set G) (z : G) :
    checkedPredicate c g (c.check z) = if z ∈ g then ⊤ else ⊥ := by
  classical
  change (⨆ w : G, if w ∈ g then X.space.eqv (c.check z) (c.check w) else ⊥) = _
  by_cases hz : z ∈ g
  · rw [if_pos hz]
    apply top_le_iff.mp
    exact le_iSup_of_le z (by rw [if_pos hz, X.space.refl])
  · rw [if_neg hz]
    apply bot_unique
    apply iSup_le
    intro w
    by_cases hw : w = z
    · subst w
      simp only [if_neg hz, le_refl]
    · rw [c.eqv]
      simp [crispSpace, Ne.symm hw]

theorem checkedPredicate_fixed (g : Set G) (π : Equiv.Perm K) :
    actPredicate X π (checkedPredicate c g) = checkedPredicate c g := by
  classical
  apply Predicate.ext
  intro x
  change a.map π (⨆ z : G,
    if z ∈ g then X.space.eqv (X.action.act π⁻¹ x) (c.check z) else ⊥) =
      ⨆ z : G, if z ∈ g then X.space.eqv x (c.check z) else ⊥
  rw [(a.map π).map_iSup]
  apply iSup_congr
  intro z
  by_cases hz : z ∈ g
  · simp only [if_pos hz]
    rw [← X.semilinear, X.action.act_inv_act, c.fixed]
  · simp only [if_neg hz, (a.map π).map_bot]

def supportedCheck (g : Set G) : SupportedPredicate X :=
  ⟨checkedPredicate c g,
    ∅, Set.finite_empty, fun π _ => checkedPredicate_fixed c g π⟩

theorem supportedCheck_eqv (g h : Set G) :
    (supportedPredicateSpace X).space.eqv (supportedCheck c g) (supportedCheck c h) =
      (crispSpace (Set G)).eqv g h := by
  classical
  by_cases he : g = h
  · subst h
    exact ((supportedPredicateSpace X).space.refl (supportedCheck c g)).trans
      ((crispSpace (B := B) (Set G)).refl g).symm
  · change (⨅ x, iffValue (checkedPredicate c g x) (checkedPredicate c h x)) =
      if g = h then ⊤ else ⊥
    rw [if_neg he]
    have hd : ∃ z, ¬ (z ∈ g ↔ z ∈ h) := by
      by_contra hn
      apply he
      ext z
      by_contra hz
      exact hn ⟨z, hz⟩
    obtain ⟨z, hz⟩ := hd
    apply bot_unique
    apply (iInf_le _ (c.check z)).trans
    rw [checkedPredicate_apply_check, checkedPredicate_apply_check]
    by_cases hg : z ∈ g <;> by_cases hh : z ∈ h <;>
      simp_all [iffValue]

def predicate : GroundMap (supportedPredicateSpace X) (Set G) where
  check := supportedCheck c
  eqv := supportedCheck_eqv c
  fixed π g := by
    apply Subtype.ext
    exact checkedPredicate_fixed c g π

variable (a : BooleanAction K B) (E : Type)

/-- Canonical checks at every actual project type, by its mutual recursor. -/
abbrev domMap (σ : Ty) :
    GroundMap (DomSpace a E σ) (ChoiceFirstOrder.Full.Dom E σ) :=
  @Ty.rec
    (fun σ => GroundMap (DomSpace a E σ) (ChoiceFirstOrder.Full.Dom E σ))
    (fun ρ => GroundMap (TupleSpace a E ρ) (ChoiceFirstOrder.Full.Tuple E ρ))
    (crisp a E) (fun _ c => predicate c) (fun _ => crisp a E)
    (crisp a PUnit) (fun _ _ c d => product c d) σ

abbrev tupleMap (ρ : RTy) :
    GroundMap (TupleSpace a E ρ) (ChoiceFirstOrder.Full.Tuple E ρ) :=
  @RTy.rec
    (fun σ => GroundMap (DomSpace a E σ) (ChoiceFirstOrder.Full.Dom E σ))
    (fun ρ => GroundMap (TupleSpace a E ρ) (ChoiceFirstOrder.Full.Tuple E ρ))
    (crisp a E) (fun _ c => predicate c) (fun _ => crisp a E)
    (crisp a PUnit) (fun _ _ c d => product c d) ρ

def check (σ : Ty) : ChoiceFirstOrder.Full.Dom E σ → Dom a E σ := (domMap a E σ).check

theorem check_eqv (σ : Ty) (x y : ChoiceFirstOrder.Full.Dom E σ) :
    (DomSpace a E σ).space.eqv (check a E σ x) (check a E σ y) =
      (crispSpace (ChoiceFirstOrder.Full.Dom E σ)).eqv x y :=
  (domMap a E σ).eqv x y

theorem check_fixed (σ : Ty) (π : Equiv.Perm K) (x : ChoiceFirstOrder.Full.Dom E σ) :
    (DomSpace a E σ).action.act π (check a E σ x) = check a E σ x :=
  (domMap a E σ).fixed π x

end

end Classicism.Meta.ChoiceBoolean.GroundChecks
