import Classicism.Models.NominalChoiceInfrastructure
import Mathlib.Algebra.Group.End

/-!
# Infinite orbit sequences give admitted Dedekind operations

The shift acts on the WHOLE proposition domain, fixes everything outside the
chosen sequence, is injective, and omits its first member. It is admitted by an
explicit empty-support proof. The resulting certificate is an actual closed
typed sentence with an existential t→t operation, not an external injection
into a collection of propositions. The required sequence of distinct orbits is
an explicit sufficient premise; the converse orbit-finite theorem is not here.

Source: nominal-choice-classification-20261022.md §6, original local research,
unpaginated, misc. Ordinary ZFC metatheory; uncompiled candidate.
-/

namespace Classicism.Meta.Nominal
noncomputable section

def sequenceShift {E : Type} (q : Nat → E) (x : E) : E := by
  classical
  exact if h : ∃ n, q n = x then q ((Classical.choose h) + 1) else x

theorem sequenceShift_on {E : Type} (q : Nat → E) (hq : Function.Injective q) (n : Nat) :
    sequenceShift q (q n) = q (n + 1) := by
  classical
  unfold sequenceShift
  split
  · rename_i h
    rw [hq (Classical.choose_spec h)]
  · rename_i h
    exact False.elim (h ⟨n, rfl⟩)

theorem sequenceShift_off {E : Type} (q : Nat → E) (x : E) (hx : ¬∃ n, q n = x) :
    sequenceShift q x = x := by
  classical
  simp only [sequenceShift, dif_neg hx]

theorem sequenceShift_injective {E : Type} (q : Nat → E) (hq : Function.Injective q) :
    Function.Injective (sequenceShift q) := by
  classical
  intro x y h
  by_cases hx : ∃ n, q n = x
  · obtain ⟨n, rfl⟩ := hx
    rw [sequenceShift_on q hq n] at h
    by_cases hy : ∃ m, q m = y
    · obtain ⟨m, rfl⟩ := hy
      rw [sequenceShift_on q hq m] at h
      exact congrArg q (Nat.add_right_cancel (hq h))
    · rw [sequenceShift_off q y hy] at h
      exact False.elim (hy ⟨n + 1, h⟩)
  · rw [sequenceShift_off q x hx] at h
    by_cases hy : ∃ m, q m = y
    · obtain ⟨m, rfl⟩ := hy
      rw [sequenceShift_on q hq m] at h
      exact False.elim (hx ⟨m + 1, h.symm⟩)
    · rwa [sequenceShift_off q y hy] at h

theorem sequenceShift_omits {E : Type} (q : Nat → E) (hq : Function.Injective q) :
    ∀ x, sequenceShift q x ≠ q 0 := by
  classical
  intro x he
  by_cases hx : ∃ n, q n = x
  · obtain ⟨n, rfl⟩ := hx
    rw [sequenceShift_on q hq n] at he
    exact Nat.noConfusion (hq he)
  · rw [sequenceShift_off q x hx] at he
    exact hx ⟨0, he.symm⟩

variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

def shiftHom (X : Nom A I) (q : Nat → X) (hq : Function.Injective q)
    (hf : ∀ g n, X.obj.act g (q n) = q n) : Hom X X where
  fn := sequenceShift q
  comm g x := by
    classical
    by_cases hx : ∃ n, q n = x
    · obtain ⟨n, rfl⟩ := hx
      rw [hf g n, sequenceShift_on q hq n, hf g (n + 1)]
    · have hgx : ¬∃ n, q n = X.obj.act g x := by
        rintro ⟨n, hn⟩
        have he := congrArg (X.obj.act g⁻¹) hn
        rw [hf, inv_act] at he
        exact hx ⟨n, he⟩
      rw [sequenceShift_off q _ hgx, sequenceShift_off q _ hx]

def Orbit (W : Nom A I) (u v : W) : Prop := ∃ g : G, W.obj.act g u = v

theorem orbit_empty_support (W : Nom A I) (u : W) :
    Supports A (function W.obj (trivial Prop)) ∅ (Orbit W u) := by
    intro g _
    funext v
    apply propext
    change (∃ h, W.obj.act h u = W.obj.act g⁻¹ v) ↔ ∃ h, W.obj.act h u = v
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨g * h, by rw [W.obj.mul_act, hh, act_inv]⟩
    · rintro ⟨h, hh⟩
      exact ⟨g⁻¹ * h, by rw [W.obj.mul_act, hh]⟩

def orbitProp (W : Nom A I) (u : W) : propositions W :=
  ⟨Orbit W u, ∅, I.empty, orbit_empty_support W u⟩

theorem orbitProp_fixed (W : Nom A I) (u : W) (g : G) :
    (propositions W).obj.act g (orbitProp W u) = orbitProp W u := by
  apply Subtype.ext
  exact orbit_empty_support W u g (fun _ h => h.elim)

theorem orbitProp_injective (W : Nom A I) (u : Nat → W)
    (hu : ∀ n m, Orbit W (u n) (u m) → n = m) :
    Function.Injective (fun n => orbitProp W (u n)) := by
  intro n m he
  apply hu n m
  have ht := congrArg (fun p : propositions W => p.val (u m)) he
  exact Eq.mpr ht ⟨1, W.obj.one_act (u m)⟩

/-- A full-domain admitted operation, with its two decisive properties. -/
theorem orbit_sequence_dedekind (W : Nom A I) (u : Nat → W)
    (hu : ∀ n m, Orbit W (u n) (u m) → n = m) :
    ∃ f : exponential (propositions W) (propositions W),
      Function.Injective f.val ∧ ∃ r : propositions W, ∀ p, f.val p ≠ r := by
  let q : Nat → propositions W := fun n => orbitProp W (u n)
  have hq : Function.Injective q := orbitProp_injective W u hu
  refine ⟨element (shiftHom (propositions W) q hq (fun g n => orbitProp_fixed W (u n) g)),
    sequenceShift_injective q hq, q 0, sequenceShift_omits q hq⟩

namespace Hierarchy

/-- The ordinary original-language operational Dedekind-infinity sentence at t.
The operation is quantified at t→t; injectivity and the omitted value use rigid
typed equality. This introduces a name for syntax, not a new logical axiom. -/
def dedInfT : Sentence Signature.pure :=
  Term.exists' (σ := Ty.t ⇒ RTy.t)
    (Term.conj
      (Term.forall' (σ := Ty.t) (Term.forall' (σ := Ty.t)
        (Term.imp
          (Term.eq' (Term.app Term.v2 Term.v1) (Term.app Term.v2 Term.v0))
          (Term.eq' Term.v1 Term.v0))))
      (Term.exists' (σ := Ty.t) (Term.forall' (σ := Ty.t)
        (Term.neg (Term.eq' (Term.app Term.v2 Term.v0) Term.v1)))))

theorem dedInfT_iff (W : Nom A I) (w : W) :
    Holds W (pureConstants W) (Γ := []) () w dedInfT ↔
      ∃ f : exponential (propositions W) (propositions W),
        Function.Injective f.val ∧ ∃ r : propositions W, ∀ p, f.val p ≠ r := by
  classical
  suffices h : ∀ η : env W [],
      Holds W (pureConstants W) (Γ := []) η w dedInfT ↔
        ∃ f : exponential (propositions W) (propositions W),
          Function.Injective f.val ∧ ∃ r : propositions W, ∀ p, f.val p ≠ r by
    exact h ()
  intro η
  simp only [dedInfT, holds_exists W (pureConstants W), holds_and W (pureConstants W),
    holds_all W (pureConstants W), holds_imp W (pureConstants W),
    holds_eq W (pureConstants W), holds_not W (pureConstants W)]
  rfl

theorem orbit_sequence_dedInfT (W : Nom A I) (u : Nat → W)
    (hu : ∀ n m, Orbit W (u n) (u m) → n = m) (w : W) :
    Holds W (pureConstants W) (Γ := []) () w dedInfT :=
  (dedInfT_iff W w).2 (orbit_sequence_dedekind W u hu)

theorem orbit_sequence_boxed_dedInfT (W : Nom A I) (u : Nat → W)
    (hu : ∀ n m, Orbit W (u n) (u m) → n = m) (w : W) :
    Holds W (pureConstants W) (Γ := []) () w (Term.box dedInfT) :=
  (holds_box W (pureConstants W) dedInfT () w).2 (orbit_sequence_dedInfT W u hu)

end Hierarchy
end
end Classicism.Meta.Nominal
