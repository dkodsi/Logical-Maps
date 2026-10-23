import Classicism.Models.NominalChoiceInfrastructure

/-!
# Exact support-stabilizer criterion for an IC selector

For one admitted family F, an admitted unique-witness graph exists exactly when
some common small support fixes F and every world has an F-witness fixed by its
stabilizer inside the pointwise fixer of that support. The forward implication
keeps the world in the stabilizer. The reverse implication constructs orbit
representatives, transports chosen fixed witnesses, and proves independence of
the transport. It does not assume a selector or a cardinal reservoir theorem.

Sources: the stabilizer/transport arguments of
nominal-choice-classification-20261022.md §§3–5 and
support-bounds-world-geometry-20261022.md §1, local research, unpaginated, misc.
The packaged iff and its proofs are new ordinary metatheory. Uncompiled candidate.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

theorem fixes_one (S : Set A) : Fixes A S 1 := fun a _ => A.one_act a

theorem fixes_mul {S : Set A} {g h : G} (hg : Fixes A S g) (hh : Fixes A S h) :
    Fixes A S (g * h) := by
  intro a ha
  rw [A.mul_act, hh a ha, hg a ha]

theorem fixes_inv {S : Set A} {g : G} (hg : Fixes A S g) : Fixes A S g⁻¹ := by
  intro a ha
  have he := congrArg (A.act g⁻¹) (hg a ha)
  rw [inv_act] at he
  exact he.symm

def SupportOrbit (W : Nom A I) (S : Set A) (u v : W) : Prop :=
  ∃ g : G, Fixes A S g ∧ W.obj.act g u = v

theorem supportOrbit_self (W : Nom A I) (S : Set A) (w : W) : SupportOrbit W S w w :=
  ⟨1, fixes_one S, W.obj.one_act w⟩

theorem supportOrbit_move (W : Nom A I) (S : Set A) (g : G) (hg : Fixes A S g)
    (u w : W) : SupportOrbit W S u (W.obj.act g w) ↔ SupportOrbit W S u w := by
  constructor
  · rintro ⟨h, hh, he⟩
    exact ⟨g⁻¹ * h, fixes_mul (fixes_inv hg) hh,
      by rw [W.obj.mul_act, he, inv_act]⟩
  · rintro ⟨h, hh, he⟩
    exact ⟨g * h, fixes_mul hg hh, by rw [W.obj.mul_act, he]⟩

private theorem choose_predicate_congr {E : Type} {p q : E → Prop}
    (he : p = q) (hp : ∃ x, p x) (hq : ∃ x, q x) :
    Classical.choose hp = Classical.choose hq := by
  cases he
  rfl

def orbitRepresentative (W : Nom A I) (S : Set A) (w : W) : W :=
  Classical.choose (show ∃ u, SupportOrbit W S u w from ⟨w, supportOrbit_self W S w⟩)

theorem orbitRepresentative_spec (W : Nom A I) (S : Set A) (w : W) :
    SupportOrbit W S (orbitRepresentative W S w) w :=
  Classical.choose_spec (show ∃ u, SupportOrbit W S u w from ⟨w, supportOrbit_self W S w⟩)

theorem orbitRepresentative_move (W : Nom A I) (S : Set A) (g : G)
    (hg : Fixes A S g) (w : W) :
    orbitRepresentative W S (W.obj.act g w) = orbitRepresentative W S w := by
  apply choose_predicate_congr
  funext u
  exact propext (supportOrbit_move W S g hg u w)

/-- Equal transports of a world agree on a stabilizer-fixed witness. -/
theorem transports_agree (W X : Nom A I) (S : Set A) (w : W) (x : X)
    (hx : ∀ k, Fixes A S k → W.obj.act k w = w → X.obj.act k x = x)
    (g h : G) (hg : Fixes A S g) (hh : Fixes A S h)
    (he : W.obj.act g w = W.obj.act h w) : X.obj.act g x = X.obj.act h x := by
  have hw : W.obj.act (h⁻¹ * g) w = w := by
    rw [W.obj.mul_act, he, inv_act]
  have hx' := hx (h⁻¹ * g) (fixes_mul (fixes_inv hh) hg) hw
  have hx'' := congrArg (X.obj.act h) hx'
  simpa only [X.obj.mul_act, act_inv] using hx''

/-- Construct a supported external selector from fixed witnesses. The output
graph, below, is of original type X→t even when X=e. -/
theorem selector_of_fixed_witnesses (W X : Nom A I) (S : Set A) (hS : I.Small S)
    (F : exponential X (propositions W))
    (hF : Supports A (exponential X (propositions W)).obj S F)
    (hfiber : ∀ w : W, ∃ x : X, (F.val x).val w ∧
      ∀ g, Fixes A S g → W.obj.act g w = w → X.obj.act g x = x) :
    ∃ h : exponential W X, (∀ w, (F.val (h.val w)).val w) ∧
      Supports A (exponential W X).obj S h := by
  classical
  let r : W → W := orbitRepresentative W S
  let τ : W → G := fun w => Classical.choose (orbitRepresentative_spec W S w)
  have hτ : ∀ w, Fixes A S (τ w) ∧ W.obj.act (τ w) (r w) = w :=
    fun w => Classical.choose_spec (orbitRepresentative_spec W S w)
  let b : W → X := fun w => Classical.choose (hfiber w)
  have hb : ∀ w, (F.val (b w)).val w ∧
      ∀ g, Fixes A S g → W.obj.act g w = w → X.obj.act g (b w) = b w :=
    fun w => Classical.choose_spec (hfiber w)
  let h : W → X := fun w => X.obj.act (τ w) (b (r w))
  have hc : ∀ g, Fixes A S g → ∀ w, h (W.obj.act g w) = X.obj.act g (h w) := by
    intro g hg w
    have hr : r (W.obj.act g w) = r w := orbitRepresentative_move W S g hg w
    have ht := (hτ (W.obj.act g w)).2
    rw [hr] at ht
    have he : W.obj.act (τ (W.obj.act g w)) (r w) = W.obj.act (g * τ w) (r w) := by
      rw [W.obj.mul_act, (hτ w).2, ht]
    have hx := transports_agree W X S (r w) (b (r w)) (hb (r w)).2
      (τ (W.obj.act g w)) (g * τ w) (hτ _).1 (fixes_mul hg (hτ w).1) he
    change X.obj.act (τ (W.obj.act g w)) (b (r (W.obj.act g w))) = _
    rw [hr, hx, X.obj.mul_act]
  have hs : Supports A (function W.obj X.obj) S h :=
    (function_support_iff W X S h).2 hc
  let H : exponential W X := ⟨h, S, hS, hs⟩
  refine ⟨H, ?_, fun g hg => Subtype.ext (hs g hg)⟩
  intro w
  have hi : W.obj.act (τ w)⁻¹ w = r w := by
    have he := congrArg (W.obj.act (τ w)⁻¹) (hτ w).2
    rw [inv_act] at he
    exact he.symm
  have he := congrArg (fun p : propositions W => p.val w)
    (exponential_covariance X (propositions W) hF (τ w) (hτ w).1 (b (r w)))
  change (F.val (h w)).val w = (F.val (b (r w))).val (W.obj.act (τ w)⁻¹ w) at he
  rw [hi] at he
  exact Eq.mpr he (hb (r w)).1

def HasSelector (W X : Nom A I) (F : exponential X (propositions W)) : Prop :=
  ∃ Q : exponential X (propositions W),
    (∀ x w, (Q.val x).val w → (F.val x).val w) ∧
    ∀ w, ∃ x, (Q.val x).val w ∧ ∀ y, (Q.val y).val w → y = x

def StabilizerCriterion (W X : Nom A I) (F : exponential X (propositions W)) : Prop :=
  ∃ S : Set A, I.Small S ∧ Supports A (exponential X (propositions W)).obj S F ∧
    ∀ w : W, ∃ x : X, (F.val x).val w ∧
      ∀ g, Fixes A S g → W.obj.act g w = w → X.obj.act g x = x

theorem selector_iff_stabilizers (W X : Nom A I) (F : exponential X (propositions W)) :
    HasSelector W X F ↔ StabilizerCriterion W X F := by
  constructor
  · rintro ⟨Q, hQF, hQ⟩
    obtain ⟨S, hS, hs⟩ := (exponential X (propositions W)).supported F
    obtain ⟨T, hT, ht⟩ := (exponential X (propositions W)).supported Q
    have hs' := supports_mono A _ (fun _ h => Or.inl h : S ⊆ S ∪ T) hs
    have ht' := supports_mono A _ (fun _ h => Or.inr h : T ⊆ S ∪ T) ht
    refine ⟨S ∪ T, I.union hS hT, hs', ?_⟩
    intro w
    obtain ⟨x, hx, hu⟩ := hQ w
    exact ⟨x, hQF x w hx, fun g hg hw => unique_witness_fixed W X Q ht' w x hx hu g hg hw⟩
  · rintro ⟨S, hS, hF, hfiber⟩
    obtain ⟨h, hh, _⟩ := selector_of_fixed_witnesses W X S hS F hF hfiber
    exact ⟨(graph W X).fn h, graph_selects W X F h hh⟩

theorem ic_iff_stabilizers (W X : Nom A I) :
    IC W X ↔ ∀ F : exponential X (propositions W),
      (∀ w : W, ∃ x : X, (F.val x).val w) → StabilizerCriterion W X F := by
  constructor
  · intro h F hF
    exact (selector_iff_stabilizers W X F).1 (h F hF)
  · intro h F hF
    exact (selector_iff_stabilizers W X F).2 (h F hF)

end
end Classicism.Meta.Nominal
