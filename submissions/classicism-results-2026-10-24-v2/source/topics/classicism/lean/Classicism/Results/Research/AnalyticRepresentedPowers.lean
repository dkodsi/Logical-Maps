import Classicism.Results.Research.AnalyticRigidification

/-!
# Internal represented powers on a persistent tuple domain

The represented-powers step of the Goodsell / Claude Fable 5.1 argument of
23 October 2026, after Bacon, Corollary 5.1 (9 October 2025 draft).
`D` is a curried relation describing the allowed tuples. `AgreeOn` is the
pointwise agreement restricted to those tuples. `PowerFamily` contains exactly
the rigid relations supported on `D`; it is a definable internal property.
This generic theorem does not assume an external powerset or Atomicity.
-/

namespace Classicism.Research.Analytic
open Classicism.Paper Classicism.P

variable {ρ : Type} [Rel ρ] [Pointwise ρ]

def AgreeOn (D S R : ρ) : Prop := Rel.and S D ≡ Rel.and R D

def PowerFamily (D : ρ) (S : ρ) : Prop := Rigid S ∧ S ⊆ D

def RepresentedPower (D : ρ) (P : ρ → Prop) : Prop :=
  Rigid P ∧ (∀ S, P S → Rigid S ∧ S ⊆ D) ∧
    □ (∀ R, ∃ S, P S ∧ AgreeOn D S R)

theorem supported_rigid_necessary (D S : ρ) (hD : Persistent D)
    (hS : Rigid S) (hs : S ⊆ D) : □ (S ⊆ D) :=
  weaklyInextensible_of_inextensible hS.2 D
    (incl_trans S D (boxAt D) hs (weaklyPersistent_of_persistent hD))

theorem power_family_weakly_persistent (D : ρ) (hD : Persistent D) :
    WeaklyPersistent (PowerFamily D) := fun S hs =>
  modal_K _ _ (modal_K _ _
    (nec% (fun (hr : Rigid S) (hi : S ⊆ D) =>
      (show PowerFamily D S from ⟨hr, hi⟩))) (rigid_necessary S hs.1))
    (supported_rigid_necessary D S hD hs.1 hs.2)

theorem power_family_persistent (D : ρ) (hD : Persistent D) :
    Persistent (PowerFamily D) :=
  modal_K _ _ (nec% (power_family_weakly_persistent D)) (modal_four _ hD)

theorem power_family_rigid
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) (D : ρ) (hD : Persistent D) :
    Rigid (PowerFamily D) :=
  ⟨power_family_persistent D hD,
    Proofs.inextensible_of_persistent_c5 c5 (PowerFamily D) (power_family_persistent D hD)⟩

theorem restricted_coext_agrees (D R S : ρ) (hc : Rel.and R D ≡ S) :
    S ⊆ D ∧ AgreeOn D S R := by
  have hs : S ⊆ Rel.and R D := incl_of_coext' _ _ hc
  have ht : Rel.and R D ⊆ S := incl_of_coext _ _ hc
  exact ⟨incl_trans _ _ _ hs (incl_and_right R D),
    coext_of_incl _ _
      (incl_trans _ _ _ (incl_and_left S D) hs)
      (incl_and S D (Rel.and R D) ht (incl_and_right R D))⟩

theorem power_family_represents (D : ρ) (rc : RigidComprehension ρ) :
    ∀ R, ∃ S, PowerFamily D S ∧ AgreeOn D S R := by
  intro R
  obtain ⟨S, hS, hc⟩ := rc (Rel.and R D)
  have ha := restricted_coext_agrees D R S hc
  exact ⟨S, ⟨hS, ha.1⟩, ha.2⟩

/-- Every finite-arity instance is available by substituting its curried tuple
domain. Persistence of that domain is the only domain hypothesis. -/
theorem represented_power
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension ρ)) (D : ρ) (hD : Persistent D) :
    RepresentedPower D (PowerFamily D) :=
  ⟨power_family_rigid c5 D hD, fun _ hs => hs,
    modal_K _ _ (nec% (power_family_represents D)) nrc⟩

section explicitTupleDomains
variable {σ : Type} [Ty σ]

def Domain2 (X : σ → Prop) : σ → σ → Prop := fun x y => X x ∧ X y
def Domain3 (X : σ → Prop) : σ → σ → σ → Prop := fun x y z => X x ∧ X y ∧ X z

/-- The masked-coextension notation is exactly agreement on domain instances. -/
theorem agree_on_one_iff (X S R : σ → Prop) :
    AgreeOn X S R ↔ ∀ x, X x → (S x ↔ R x) :=
  ⟨fun h x hx => ⟨fun hs => ((h x).1 ⟨hs, hx⟩).1,
                     fun hr => ((h x).2 ⟨hr, hx⟩).1⟩,
   fun h x => ⟨fun hs => ⟨(h x hs.2).1 hs.1, hs.2⟩,
                fun hr => ⟨(h x hr.2).2 hr.1, hr.2⟩⟩⟩

theorem agree_on_two_iff (X : σ → Prop) (S R : σ → σ → Prop) :
    AgreeOn (Domain2 X) S R ↔ ∀ x y, X x → X y → (S x y ↔ R x y) :=
  ⟨fun h x y hx hy => ⟨fun hs => ((h x y).1 ⟨hs, hx, hy⟩).1,
                          fun hr => ((h x y).2 ⟨hr, hx, hy⟩).1⟩,
   fun h x y => ⟨fun hs => ⟨(h x y hs.2.1 hs.2.2).1 hs.1, hs.2⟩,
                  fun hr => ⟨(h x y hr.2.1 hr.2.2).2 hr.1, hr.2⟩⟩⟩

theorem agree_on_three_iff (X : σ → Prop) (S R : σ → σ → σ → Prop) :
    AgreeOn (Domain3 X) S R ↔
      ∀ x y z, X x → X y → X z → (S x y z ↔ R x y z) :=
  ⟨fun h x y z hx hy hz => ⟨fun hs => ((h x y z).1 ⟨hs, hx, hy, hz⟩).1,
                               fun hr => ((h x y z).2 ⟨hr, hx, hy, hz⟩).1⟩,
   fun h x y z => ⟨fun hs => ⟨(h x y z hs.2.1 hs.2.2.1 hs.2.2.2).1 hs.1, hs.2⟩,
                    fun hr => ⟨(h x y z hr.2.1 hr.2.2.1 hr.2.2.2).2 hr.1, hr.2⟩⟩⟩

theorem domain2_weakly_persistent (X : σ → Prop) (hX : WeaklyPersistent X) :
    WeaklyPersistent (Domain2 X) := fun x y h =>
  modal_K _ _ (modal_K _ _ (nec% (fun (hx : X x) (hy : X y) => And.intro hx hy))
    (hX x h.1)) (hX y h.2)

theorem domain2_persistent (X : σ → Prop) (hX : Persistent X) :
    Persistent (Domain2 X) :=
  modal_K _ _ (nec% (domain2_weakly_persistent X)) hX

theorem domain3_weakly_persistent (X : σ → Prop) (hX : WeaklyPersistent X) :
    WeaklyPersistent (Domain3 X) := fun x y z h =>
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (hx : X x) (hy : X y) (hz : X z) => And.intro hx (And.intro hy hz)))
    (hX x h.1)) (hX y h.2.1)) (hX z h.2.2)

theorem domain3_persistent (X : σ → Prop) (hX : Persistent X) :
    Persistent (Domain3 X) :=
  modal_K _ _ (nec% (domain3_weakly_persistent X)) hX

/-- The exact finite instance with represented powers of arities one, two,
and three. This is not labeled as the unbounded finite schema. -/
theorem analytic_necessitism_three
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension (σ → Prop)))
    (nrc2 : □ (RigidComprehension (σ → σ → Prop)))
    (nrc3 : □ (RigidComprehension (σ → σ → σ → Prop)))
    (h : ◇ (HasReal σ)) :
    ∃ (X : σ → Prop) (le : σ → σ → Prop) (add mul : σ → σ → σ → Prop)
      (zero one : σ) (N : σ → Prop)
      (P1 : (σ → Prop) → Prop) (P2 : (σ → σ → Prop) → Prop)
      (P3 : (σ → σ → σ → Prop) → Prop),
      RigidStr X le add mul N ∧ □ (Real X le add mul zero one N) ∧
      RepresentedPower X P1 ∧ RepresentedPower (Domain2 X) P2 ∧
      RepresentedPower (Domain3 X) P3 := by
  obtain ⟨X, le, add, mul, zero, one, N, hr, hreal⟩ :=
    rigidify_possible c5 nrc nrc2 nrc3 h
  exact ⟨X, le, add, mul, zero, one, N,
    PowerFamily X, PowerFamily (Domain2 X), PowerFamily (Domain3 X),
    hr, hreal, represented_power c5 nrc X hr.1.1,
    represented_power c5 nrc2 (Domain2 X) (domain2_persistent X hr.1.1),
    represented_power c5 nrc3 (Domain3 X) (domain3_persistent X hr.1.1)⟩

end explicitTupleDomains
end Classicism.Research.Analytic
