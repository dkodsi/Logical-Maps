import Classicism.Results.Records.C5

/-!
# A checked-language instance of generated-algebra transfer

Source: research/2026-10-22/notes/c5-generated-algebra-transfer-20261022.md,
§§1–5 (unpaginated original research, `misc`).

This module handles ONE source sort and ONE target sort, with one constant, one
unary constructor and one binary constructor. Both sorts are relational. It is
an object-language C instance of the source's finite-sorted theorem, not a
formalization of arbitrary finite signatures or a claim that their encoding is
already supplied. Purely unary generation is obtained by taking the binary
constructor to be a projection; the source/core bridge must check that instance.

All map and constructor equations are explicit premises. C5 means boxed ND_t.
The forward proof needs no C5. The reverse proof establishes that the represented
image is a supported rigid predicate, using C5 only for persistent-to-inextensible.
No Choice, RC, Actuality, free-algebra premise or external standardness is used.
-/

namespace Classicism.Research.GeneratedAlgebra
open Classicism.Paper

variable {μ ν : Type} [Rel μ] [Rel ν]

/-- Simultaneous closure under the displayed finite list of constructors. -/
def Carrier (c : μ) (f : μ → μ) (b : μ → μ → μ) (x : μ) : Prop :=
  ∀ V : μ → Prop, V c → (∀ a, V a → V (f a)) →
    (∀ a d, V a → V d → V (b a d)) → V x

theorem carrier_base (c : μ) (f : μ → μ) (b : μ → μ → μ) : Carrier c f b c :=
  fun _ hc _ _ => hc

theorem carrier_unary (c : μ) (f : μ → μ) (b : μ → μ → μ) (x : μ) :
    Carrier c f b x → Carrier c f b (f x) :=
  fun hx V hc hf hb => hf x (hx V hc hf hb)

theorem carrier_binary (c : μ) (f : μ → μ) (b : μ → μ → μ) (x y : μ) :
    Carrier c f b x → Carrier c f b y → Carrier c f b (b x y) :=
  fun hx hy V hc hf hb => hb x y (hx V hc hf hb) (hy V hc hf hb)

/-- Internal induction, not recursion over externally standard constructor terms. -/
theorem carrier_point_persistent (c : μ) (f : μ → μ) (b : μ → μ → μ) :
    ∀ x, Carrier c f b x → □ (Carrier c f b x) := fun x hx =>
  hx (fun a => □ (Carrier c f b a)) (nec% (carrier_base c f b))
    (fun a ha => modal_K _ _ (nec% (carrier_unary c f b a)) ha)
    (fun a d ha hd => modal_K _ _
      (modal_K _ _ (nec% (carrier_binary c f b a d)) ha) hd)

theorem carrier_persistent (c : μ) (f : μ → μ) (b : μ → μ → μ) :
    Persistent (Carrier c f b) := nec% (carrier_point_persistent c f b)

theorem carrier_rigid
    (hnd : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (c : μ) (f : μ → μ) (b : μ → μ → μ) : Rigid (Carrier c f b) :=
  ⟨carrier_persistent c f b,
   Proofs.inextensible_of_persistent_c5 hnd _ (carrier_persistent c f b)⟩

/-- Target induction ranges over represented supported rigid predicates. -/
def CoreCarrier (H : ν → Prop) (d : ν) (g : ν → ν) (k : ν → ν → ν)
    (y : ν) : Prop :=
  H y ∧ ∀ V : ν → Prop, (Rigid V ∧ V ≤ H) → V d →
    (∀ a, H a → V a → V (g a)) →
    (∀ a z, H a → H z → V a → V z → V (k a z)) → V y

theorem core_base (H : ν → Prop) (d : ν) (g : ν → ν) (k : ν → ν → ν)
    (hd : H d) : CoreCarrier H d g k d := ⟨hd, fun _ _ hVd _ _ => hVd⟩

theorem core_unary (H : ν → Prop) (d : ν) (g : ν → ν) (k : ν → ν → ν)
    (hg : ∀ a, H a → H (g a)) (y : ν) (hy : CoreCarrier H d g k y) :
    CoreCarrier H d g k (g y) :=
  ⟨hg y hy.1, fun V hV hd hf hb => hf y hy.1 (hy.2 V hV hd hf hb)⟩

theorem core_binary (H : ν → Prop) (d : ν) (g : ν → ν) (k : ν → ν → ν)
    (hk : ∀ a z, H a → H z → H (k a z)) (y z : ν)
    (hy : CoreCarrier H d g k y) (hz : CoreCarrier H d g k z) :
    CoreCarrier H d g k (k y z) :=
  ⟨hk y z hy.1 hz.1, fun V hV hd hf hb =>
    hb y z hy.1 hz.1 (hy.2 V hV hd hf hb) (hz.2 V hV hd hf hb)⟩

/-- Pullback induction requires the commuting equations only on supported inputs. -/
theorem forward
    (c : μ) (f : μ → μ) (b : μ → μ → μ)
    (H : ν → Prop) (d : ν) (g : ν → ν) (k : ν → ν → ν) (q : μ → ν)
    (hd : H d) (hg : ∀ a, H a → H (g a))
    (hk : ∀ a z, H a → H z → H (k a z))
    (hq0 : q c = d) (hqf : ∀ x, H (q x) → q (f x) = g (q x))
    (hqb : ∀ x y, H (q x) → H (q y) → q (b x y) = k (q x) (q y))
    (x : μ) (hx : Carrier c f b x) : CoreCarrier H d g k (q x) := by
  apply hx (fun a => CoreCarrier H d g k (q a))
  · exact hq0.symm ▸ core_base H d g k hd
  · intro a ha
    exact (hqf a ha.1).symm ▸ core_unary H d g k hg (q a) ha
  · intro a z ha hz
    exact (hqb a z ha.1 hz.1).symm ▸ core_binary H d g k hk (q a) (q z) ha hz

/-- The image is a formula of the original language, not an external subset. -/
def Image (H : ν → Prop) (G : μ → Prop) (q : μ → ν) (y : ν) : Prop :=
  H y ∧ ∃ x, G x ∧ q x = y

theorem image_intro (H : ν → Prop) (G : μ → Prop) (q : μ → ν) (x : μ) (y : ν) :
    H y → G x → q x = y → Image H G q y :=
  fun hy hx he => ⟨hy, x, hx, he⟩

/-- Positive existential persistence uses a single witness, with no BF. -/
theorem image_weakly_persistent (H : ν → Prop) (G : μ → Prop) (q : μ → ν) :
    WeaklyPersistent H → WeaklyPersistent G → WeaklyPersistent (Image H G q) := by
  intro hH hG y hy
  obtain ⟨x, hx, he⟩ := hy.2
  exact modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (image_intro H G q x y)) (hH y hy.1)) (hG x hx))
    (necessity_of_identity _ _ he)

theorem image_persistent (H : ν → Prop) (G : μ → Prop) (q : μ → ν)
    (hH : Persistent H) (hG : Persistent G) : Persistent (Image H G q) :=
  modal_K _ _ (modal_K _ _ (nec% (image_weakly_persistent H G q)) hH) hG

theorem image_support (H : ν → Prop) (G : μ → Prop) (q : μ → ν) :
    Image H G q ≤ H :=
  le_of_box_incl (nec% (fun y (hy : Image H G q y) => hy.1))

/-- C5 supplies exactly the inextensibility missing from the positive image proof. -/
theorem image_rigid
    (hnd : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (H : ν → Prop) (G : μ → Prop) (q : μ → ν)
    (hH : Persistent H) (hG : Persistent G) : Rigid (Image H G q) :=
  ⟨image_persistent H G q hH hG,
   Proofs.inextensible_of_persistent_c5 hnd _ (image_persistent H G q hH hG)⟩

/-- Surjectivity onto the internally generated target, using its represented image. -/
theorem onto
    (hnd : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (c : μ) (f : μ → μ) (b : μ → μ → μ)
    (H : ν → Prop) (d : ν) (g : ν → ν) (k : ν → ν → ν) (q : μ → ν)
    (hH : Persistent H) (hd : H d) (hg : ∀ a, H a → H (g a))
    (hk : ∀ a z, H a → H z → H (k a z))
    (hq0 : q c = d) (hqf : ∀ x, H (q x) → q (f x) = g (q x))
    (hqb : ∀ x y, H (q x) → H (q y) → q (b x y) = k (q x) (q y))
    (y : ν) (hy : CoreCarrier H d g k y) :
    ∃ x, Carrier c f b x ∧ q x = y := by
  have himage : Image H (Carrier c f b) q y := by
    apply hy.2 (Image H (Carrier c f b) q)
      ⟨image_rigid hnd H _ q hH (carrier_persistent c f b), image_support H _ q⟩
    · exact ⟨hd, c, carrier_base c f b, hq0⟩
    · intro z hz hIz
      obtain ⟨a, ha, hea⟩ := hIz.2
      exact ⟨hg z hz, f a, carrier_unary c f b a ha,
        (hqf a (hea.symm ▸ hz)).trans (congrArg g hea)⟩
    · intro z w hz hw hIz hIw
      obtain ⟨a, ha, hea⟩ := hIz.2
      obtain ⟨u, hu, heu⟩ := hIw.2
      have he : k (q a) (q u) = k z w :=
        (congrArg (fun v => k v (q u)) hea).trans (congrArg (k z) heu)
      exact ⟨hk z w hz hw, b a u, carrier_binary c f b a u ha hu,
        (hqb a u (hea.symm ▸ hz) (heu.symm ▸ hw)).trans he⟩
  exact himage.2

/-- A supplied reverse map, commuting on the target support, is a left inverse.
The proof does not assume that either generated algebra is free. -/
theorem left_inverse
    (c : μ) (f : μ → μ) (b : μ → μ → μ)
    (H : ν → Prop) (d : ν) (g : ν → ν) (k : ν → ν → ν)
    (q : μ → ν) (l : ν → μ)
    (hd : H d) (hg : ∀ a, H a → H (g a))
    (hk : ∀ a z, H a → H z → H (k a z))
    (hq0 : q c = d) (hqf : ∀ x, H (q x) → q (f x) = g (q x))
    (hqb : ∀ x y, H (q x) → H (q y) → q (b x y) = k (q x) (q y))
    (hl0 : l d = c) (hlg : ∀ y, H y → l (g y) = f (l y))
    (hlk : ∀ y z, H y → H z → l (k y z) = b (l y) (l z))
    (x : μ) (hx : Carrier c f b x) : H (q x) ∧ l (q x) = x := by
  apply hx (fun a => H (q a) ∧ l (q a) = a)
  · exact ⟨hq0.symm ▸ hd, (congrArg l hq0).trans hl0⟩
  · intro a ha
    exact ⟨(hqf a ha.1).symm ▸ hg (q a) ha.1,
      (congrArg l (hqf a ha.1)).trans ((hlg (q a) ha.1).trans (congrArg f ha.2))⟩
  · intro a z ha hz
    have he : b (l (q a)) (l (q z)) = b a z :=
      (congrArg (fun v => b v (l (q z))) ha.2).trans (congrArg (b a) hz.2)
    exact ⟨(hqb a z ha.1 hz.1).symm ▸ hk (q a) (q z) ha.1 hz.1,
      (congrArg l (hqb a z ha.1 hz.1)).trans
        ((hlk (q a) (q z) ha.1 hz.1).trans he)⟩

/-- A genuine object-level inverse law yields injectivity on the generated part. -/
theorem injective_of_left_inverse (G : μ → Prop) (q : μ → ν) (l : ν → μ)
    (hl : ∀ x, G x → l (q x) = x) (x z : μ) (hx : G x) (hz : G z)
    (he : q x = q z) : x = z :=
  (hl x hx).symm.trans ((congrArg l he).trans (hl z hz))

/-- Combining onto and the left-inverse law gives the reverse law on the target. -/
theorem right_inverse_on_target (G : μ → Prop) (K : ν → Prop)
    (q : μ → ν) (l : ν → μ)
    (honto : ∀ y, K y → ∃ x, G x ∧ q x = y)
    (hl : ∀ x, G x → l (q x) = x)
    (y : ν) (hy : K y) : G (l y) ∧ q (l y) = y := by
  obtain ⟨x, hx, he⟩ := honto y hy
  have hly : l y = x := (congrArg l he).symm.trans (hl x hx)
  exact ⟨hly.symm ▸ hx, (congrArg q hly).trans he⟩

end Classicism.Research.GeneratedAlgebra
