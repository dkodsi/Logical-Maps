import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Conditional algebraic obstructions used in the SP research

ORDINARY METAMATHEMATICS, NOT AN OBJECT-LANGUAGE C CERTIFICATE.

This file proves Boolean-algebra and map-theoretic reductions under explicit
hypotheses. It neither constructs a genuine C model nor supplies the unfinished
Henkin completion. In particular it does not identify Mathlib's equality,
function extensionality, or Boolean algebra of Prop with those of C.

The quotient-map/kernel hypotheses are inputs. Establishing them for the full
many-sorted C term algebra, and deriving the numerical-map hypotheses from the
Goodsell arithmetic interpretation, remain separate formalization obligations.
No new axiom is declared. Verification evidence is saved in sp-verification/.
-/

namespace ClassicismResearch.StrongPossibilityConsequences.Algebra

universe u v

section BooleanKernel

variable {B : Type u} [BooleanAlgebra B]

def singleKernel (d : B → B) (g p : B) : Prop := d p ≤ g

def relativeKernel (d : B → B) (g : B) (K : B → Prop) (p : B) : Prop :=
  ∃ k, K k ∧ d p ⊓ k ≤ g

theorem singleKernel_bot (d : B → B) (g : B) (hbot : d ⊥ = ⊥) :
    singleKernel d g ⊥ := by
  show d ⊥ ≤ g
  rw [hbot]
  exact bot_le

theorem singleKernel_downward (d : B → B) (g : B) (hmono : Monotone d)
    {p q : B} (hpq : p ≤ q) (hq : singleKernel d g q) : singleKernel d g p :=
  (hmono hpq).trans hq

theorem singleKernel_sup (d : B → B) (g : B)
    (hsup : ∀ p q, d (p ⊔ q) = d p ⊔ d q)
    {p q : B} (hp : singleKernel d g p) (hq : singleKernel d g q) :
    singleKernel d g (p ⊔ q) := by
  show d (p ⊔ q) ≤ g
  rw [hsup]
  exact sup_le hp hq

theorem singleKernel_diamond (d : B → B) (g : B)
    (hid : ∀ p, d (d p) = d p) {p : B} (hp : singleKernel d g p) :
    singleKernel d g (d p) := by
  show d (d p) ≤ g
  rw [hid]
  exact hp

theorem singleKernel_below (d : B → B) (g : B)
    (hext : ∀ p, p ≤ d p) {p : B} (hp : singleKernel d g p) : p ≤ g :=
  (hext p).trans hp

theorem relativeKernel_bot (d : B → B) (g : B) (K : B → Prop)
    (hbot : d ⊥ = ⊥) (htop : K ⊤) : relativeKernel d g K ⊥ := by
  refine ⟨⊤, htop, ?_⟩
  simp [hbot]

theorem relativeKernel_downward (d : B → B) (g : B) (K : B → Prop)
    (hmono : Monotone d) {p q : B} (hpq : p ≤ q)
    (hq : relativeKernel d g K q) : relativeKernel d g K p := by
  obtain ⟨k, hk, hbound⟩ := hq
  refine ⟨k, hk, ?_⟩
  exact (le_inf (inf_le_left.trans (hmono hpq)) inf_le_right).trans hbound

theorem relativeKernel_sup (d : B → B) (g : B) (K : B → Prop)
    (hsup : ∀ p q, d (p ⊔ q) = d p ⊔ d q)
    (hK : ∀ k l, K k → K l → K (k ⊓ l))
    {p q : B} (hp : relativeKernel d g K p) (hq : relativeKernel d g K q) :
    relativeKernel d g K (p ⊔ q) := by
  obtain ⟨k, hk, hpk⟩ := hp
  obtain ⟨l, hl, hql⟩ := hq
  refine ⟨k ⊓ l, hK k l hk hl, ?_⟩
  rw [hsup, inf_sup_right]
  apply sup_le
  · exact (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans hpk
  · exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans hql

theorem relativeKernel_diamond (d : B → B) (g : B) (K : B → Prop)
    (hid : ∀ p, d (d p) = d p) {p : B} (hp : relativeKernel d g K p) :
    relativeKernel d g K (d p) := by
  obtain ⟨k, hk, hbound⟩ := hp
  refine ⟨k, hk, ?_⟩
  rw [hid]
  exact hbound

theorem below_of_inf_compl_zero (x g : B) (hz : x ⊓ gᶜ = ⊥) : x ≤ g := by
  have hx : x = (x ⊓ g) ⊔ (x ⊓ gᶜ) := by
    calc
      x = x ⊓ (g ⊔ gᶜ) := by simp
      _ = (x ⊓ g) ⊔ (x ⊓ gᶜ) := by rw [inf_sup_left]
  calc
    x = (x ⊓ g) ⊔ (x ⊓ gᶜ) := hx
    _ = x ⊓ g := by simp [hz]
    _ ≤ g := inf_le_right

/-- The algebraic part of the repair: even fixed points CREATED by the
quotient cannot be nonzero below g. This is conditional on the displayed
surjective map and kernel characterization, not an existence theorem. -/
theorem quotient_no_new_fixed_below
    {Q : Type v} [BooleanAlgebra Q]
    (d : B → B) (dQ : Q → Q) (g : B) (K : B → Prop)
    (hext : ∀ p, p ≤ d p)
    (f : B → Q) (hsurj : Function.Surjective f)
    (map_inf : ∀ x y, f (x ⊓ y) = f x ⊓ f y)
    (map_compl : ∀ x, f xᶜ = (f x)ᶜ)
    (map_diamond : ∀ x, f (d x) = dQ (f x))
    (hkernel : ∀ x, f x = ⊥ ↔ relativeKernel d g K x)
    (r : Q) (hfix : dQ r = r) (hbelow : r ⊓ (f g)ᶜ = ⊥) : r = ⊥ := by
  obtain ⟨p, hp⟩ := hsurj r
  have hzero : f (d p ⊓ gᶜ) = ⊥ := by
    rw [map_inf, map_compl, map_diamond, hp, hfix]
    exact hbelow
  obtain ⟨k, hk, hbound⟩ := (hkernel (d p ⊓ gᶜ)).mp hzero
  have ht : (d p ⊓ gᶜ) ⊓ k ≤ g :=
    (le_inf (inf_le_left.trans (hext (d p ⊓ gᶜ))) inf_le_right).trans hbound
  have htc : (d p ⊓ gᶜ) ⊓ k ≤ gᶜ := inf_le_left.trans inf_le_right
  have hzero' : (d p ⊓ gᶜ) ⊓ k = ⊥ := by
    apply le_antisymm ?_ bot_le
    simpa only [inf_compl_eq_bot'] using (le_inf ht htc)
  have hzero'' : (d p ⊓ k) ⊓ gᶜ = ⊥ := by
    calc
      (d p ⊓ k) ⊓ gᶜ = (d p ⊓ gᶜ) ⊓ k := by
        rw [inf_assoc, inf_comm k gᶜ, ← inf_assoc]
      _ = ⊥ := hzero'
  exact hp.symm.trans ((hkernel p).mpr
    ⟨k, hk, below_of_inf_compl_zero (d p ⊓ k) g hzero''⟩)

end BooleanKernel

section NumericalRetractions

variable {A : Type u} {B : Type v}

/-- Retraction plus numerical injectivity of the return map forces the
forward/return composite to be the identity on all target numbers. -/
theorem numerical_return_is_inverse
    (NA : A → Prop) (NB : B → Prop) (h : A → B) (j : B → A)
    (hN : ∀ a, NA a → NB (h a)) (jN : ∀ b, NB b → NA (j b))
    (ret : ∀ a, j (h a) = a)
    (j_inj : ∀ b c, NB b → NB c → j b = j c → b = c) :
    ∀ b, NB b → h (j b) = b := fun b hb =>
  j_inj (h (j b)) b (hN (j b) (jN b hb)) hb (ret (j b))

def numericalEquiv
    (NA : A → Prop) (NB : B → Prop) (h : A → B) (j : B → A)
    (hN : ∀ a, NA a → NB (h a)) (jN : ∀ b, NB b → NA (j b))
    (ret : ∀ a, j (h a) = a)
    (j_inj : ∀ b c, NB b → NB c → j b = j c → b = c) :
    {a : A // NA a} ≃ {b : B // NB b} where
  toFun a := ⟨h a.1, hN a.1 a.2⟩
  invFun b := ⟨j b.1, jN b.1 b.2⟩
  left_inv a := Subtype.ext (ret a.1)
  right_inv b := Subtype.ext (numerical_return_is_inverse NA NB h j hN jN ret j_inj b.1 b.2)

/-- The last step of the profile-standardness argument. The substantive C
canonicity and numerical-injection facts remain explicit hypotheses here. -/
theorem numerical_named_of_profiles
    (N : A → Prop) (f : A → B) (numA : Nat → A) (numB : Nat → B)
    (hnum : ∀ k, N (numA k)) (hmap : ∀ k, f (numA k) = numB k)
    (hinj : ∀ a b, N a → N b → f a = f b → a = b)
    (hcover : ∀ a, N a → ∃ k, f a = numB k) :
    ∀ a, N a → ∃ k, a = numA k := by
  intro a ha
  obtain ⟨k, hk⟩ := hcover a ha
  exact ⟨k, hinj a (numA k) ha (hnum k) (hk.trans (hmap k).symm)⟩

end NumericalRetractions

#print axioms singleKernel_bot
#print axioms singleKernel_downward
#print axioms singleKernel_sup
#print axioms singleKernel_diamond
#print axioms singleKernel_below
#print axioms relativeKernel_bot
#print axioms relativeKernel_downward
#print axioms relativeKernel_sup
#print axioms relativeKernel_diamond
#print axioms below_of_inf_compl_zero
#print axioms quotient_no_new_fixed_below
#print axioms numerical_return_is_inverse
#print axioms numericalEquiv
#print axioms numerical_named_of_profiles

end ClassicismResearch.StrongPossibilityConsequences.Algebra
