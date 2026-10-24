import Classicism.Results.Research.ChoiceFixedPoint

/-!
# Canonical chains before completeness

Direct source: `research/2026-10-22/notes/relational-choice-countable-completeness-ccc.md`,
§§2,4, and `notes/relational-choice-boolean-completeness-transversal-proof.md`,
§5 (original research, `misc`, 22 October 2026; unpaginated).

Unlike the chain-complete fixed-point theorem, the conforming union below is
formed with no completeness premise. Only its own supremum is needed for the
final fixed-point argument. This is the input required by the CBC/CCC upgrade.
-/

namespace Classicism.Research.Choice
open Classicism.Paper Classicism.P

def GraphImage {σ : Type} [Ty σ] (f : σ → σ → Prop) (A : σ → Prop) : σ → Prop :=
  fun z => ∃ y, A y ∧ f y z

def ChainSup {σ : Type} [Ty σ] (P : σ → Prop) (R f : σ → σ → Prop)
    (A : σ → Prop) (x : σ) : Prop := DomainLUB P R (GraphImage f A) x

def CanonicalUnion {σ : Type} [Ty σ] (P : σ → Prop) (R f : σ → σ → Prop) : σ → Prop :=
  Proofs.LUstar R (ChainSup P R f)

theorem chainSup_coext {σ : Type} [Ty σ] (P : σ → Prop) (R f : σ → σ → Prop)
    (A B : σ → Prop) (e : ∀ y, A y ↔ B y) (x : σ)
    (h : ChainSup P R f A x) : ChainSup P R f B x :=
  domainLUB_coext P R _ _ (fun z =>
    ⟨fun h => h.elim fun y hy => ⟨y, (e y).1 hy.1, hy.2⟩,
     fun h => h.elim fun y hy => ⟨y, (e y).2 hy.1, hy.2⟩⟩) x h

theorem chainSup_unique {σ : Type} [Ty σ] (P : σ → Prop) (R f : σ → σ → Prop)
    (ha : ∀ x y, R x y → R y x → x = y) (A : σ → Prop) (x y : σ)
    (hx : ChainSup P R f A x) (hy : ChainSup P R f A y) : x = y :=
  domainLUB_unique P R ha _ x y hx hy

/-- A represented well-ordered conforming union, with no completeness assumption. -/
theorem canonical_union_conforming {σ : Type} [Ty σ] (P : σ → Prop)
    (R f : σ → σ → Prop)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (ha : ∀ x y, R x y → R y x → x = y) :
    Proofs.LConf R (ChainSup P R f) (CanonicalUnion P R f) :=
  Proofs.lewin_lemma4 ht (chainSup_coext P R f) (chainSup_unique P R f ha)

theorem canonical_member_domain {σ : Type} [Ty σ] (P : σ → Prop)
    (R f : σ → σ → Prop)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (ha : ∀ x y, R x y → R y x → x = y)
    (x : σ) (hx : CanonicalUnion P R f x) : P x :=
  ((canonical_union_conforming P R f ht ha).2 x hx).1

/-- Before a later chain point, every selected successor has already appeared
below that point. This is the disjoint-increment argument's order input. -/
theorem canonical_successor_bound {σ : Type} [Ty σ] (P : σ → Prop)
    (R f : σ → σ → Prop)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (ha : ∀ x y, R x y → R y x → x = y)
    (x y z : σ) (hx : CanonicalUnion P R f x) (hy : CanonicalUnion P R f y)
    (hxy : R x y) (hne : x ≠ y) (hf : f x z) : R z y :=
  ((canonical_union_conforming P R f ht ha).2 y hy).2.1 z
    ⟨x, ⟨hx, hxy, fun hyx => hne (ha x y hxy hyx)⟩, hf⟩

/-- Appending a strict upper endpoint whose predecessor-image supremum is itself
preserves conformity. All comparisons refer to actual extensions. -/
theorem append_conforming {σ : Type} [Ty σ] (P : σ → Prop) (R f : σ → σ → Prop)
    (hr : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (A : σ → Prop) (hA : Proofs.LConf R (ChainSup P R f) A) (x : σ)
    (below : ∀ y, A y → R y x ∧ ¬ R x y)
    (hs : ChainSup P R f A x) :
    Proofs.LConf R (ChainSup P R f) (fun y => A y ∨ y = x) := by
  refine ⟨⟨⟨fun a b c _ _ _ => ht a b c, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro a b ha hb hab hba
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hA.1.1.2.1 a b ha hb hab hba
    · rw [hb] at hba; exact ((below a ha).2 hba).elim
    · rw [ha] at hab; exact ((below b hb).2 hab).elim
    · exact ha.trans hb.symm
  · intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hA.1.1.2.2 a b ha hb
    · rw [hb]; exact Or.inl (below a ha).1
    · rw [ha]; exact Or.inr (below b hb).1
    · rw [ha, hb]; exact Or.inl (hr x)
  · intro Y hY hne
    refine (em (∃ y, Y y ∧ A y)).elim (fun hex => ?_) (fun hn => ?_)
    · obtain ⟨m, ⟨hmY, hmA⟩, hml⟩ :=
        Proofs.lwo_exists_least R hA.1 (fun y => Y y ∧ A y) (fun _ h => h.2) hex
      refine ⟨m, hmY, fun y hy hym => ?_⟩
      rcases hY y hy with hyA | hyx
      · exact hA.1.1.2.1 y m hyA hmA hym (hml y ⟨hy, hyA⟩)
      · rw [hyx] at hym; exact ((below m hmA).2 hym).elim
    · obtain ⟨y₀, hy₀⟩ := hne
      have allx : ∀ y, Y y → y = x := fun y hy =>
        (hY y hy).elim (fun h => (hn ⟨y, hy, h⟩).elim) id
      exact ⟨y₀, hy₀, fun y hy _ => (allx y hy).trans (allx y₀ hy₀).symm⟩
  · intro w hw
    rcases hw with hwA | hwx
    · apply chainSup_coext P R f (Proofs.LP R A w) _ _ w (hA.2 w hwA)
      intro y
      exact ⟨fun h => ⟨Or.inl h.1, h.2⟩,
        fun h => ⟨h.1.elim id (fun e =>
          ((below w hwA).2 (e ▸ h.2.1)).elim), h.2⟩⟩
    · rw [hwx]
      apply chainSup_coext P R f A _ _ x hs
      intro y
      exact ⟨fun hy => ⟨Or.inl hy, below y hy⟩,
        fun h => h.1.elim id (fun e => by
          rw [e] at h
          exact (h.2.2 h.2.1).elim)⟩

/-- Abstracting the represented union keeps the translated proof small.
The maximal-conformity premise is discharged by the definition of CanonicalUnion
in the public theorem below; it is not an added premise of that theorem. -/
theorem conforming_fixedpoint_of_supremum {σ : Type} [Ty σ]
    (P : σ → Prop) (R f : σ → σ → Prop)
    (hr : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (ha : ∀ x y, R x y → R y x → x = y)
    (hserial : ∀ x, P x → ∃ y, f x y)
    (hclosed : ∀ x y, P x → f x y → P y)
    (hprog : ∀ x y, P x → f x y → R x y)
    (huniq : ∀ x y z, P x → f x y → f x z → y = z)
    (A : σ → Prop) (hA : Proofs.LConf R (ChainSup P R f) A)
    (hMax : ∀ B, Proofs.LConf R (ChainSup P R f) B → ∀ x, B x → A x)
    (u : σ) (hu : DomainLUB P R A u) : A u ∧ f u u := by
  have hAP : ∀ x, A x → P x := fun x hx => (hA.2 x hx).1
  have hin : A u := by
    refine (em (A u)).elim id (fun hn => False.elim ?_)
    have later : ∀ a, A a → ∃ b, A b ∧ R a b ∧ ¬ R b a := by
      intro a haa
      refine (em (∃ b, A b ∧ R a b ∧ ¬ R b a)).elim id (fun hn' => False.elim ?_)
      have hub : ∀ b, A b → R b a := fun b hb =>
        (hA.1.1.2.2 b a hb haa).elim id fun hab =>
          (em (R b a)).elim id (fun hba => (hn' ⟨b, hb, hab, hba⟩).elim)
      have e : u = a := ha u a (hu.2.2 a (hAP a haa) hub) (hu.2.1 a haa)
      exact hn (e.symm ▸ haa)
    have hs : ChainSup P R f A u := by
      refine ⟨hu.1, ?_, ?_⟩
      · intro z hz
        obtain ⟨a, haa, haz⟩ := hz
        obtain ⟨b, hb, hab, hnba⟩ := later a haa
        exact ht z b u
          (((hA.2 b hb).2.1 z) ⟨a, ⟨haa, hab, hnba⟩, haz⟩) (hu.2.1 b hb)
      · intro v hv hupper
        apply hu.2.2 v hv
        intro a haa
        obtain ⟨z, haz⟩ := hserial a (hAP a haa)
        exact ht a z v (hprog a z (hAP a haa) haz) (hupper z ⟨a, haa, haz⟩)
    have below : ∀ a, A a → R a u ∧ ¬ R u a := fun a haa =>
      ⟨hu.2.1 a haa, fun hua => hn ((ha u a hua (hu.2.1 a haa)).symm ▸ haa)⟩
    have happ := append_conforming P R f hr ht A hA u below hs
    exact hn (hMax _ happ u (Or.inr rfl))
  refine ⟨hin, ?_⟩
  obtain ⟨z, huz⟩ := hserial u hu.1
  refine (em (z = u)).elim (fun e => e ▸ huz) (fun hne => False.elim ?_)
  have huzle := hprog u z hu.1 huz
  have hnzu : ¬ R z u := fun hzu => hne (ha z u hzu huzle)
  have below : ∀ a, A a → R a z ∧ ¬ R z a := fun a haa =>
    ⟨ht a u z (hu.2.1 a haa) huzle,
      fun hza => hnzu (ht z a u hza (hu.2.1 a haa))⟩
  have hs : ChainSup P R f A z := by
    refine ⟨hclosed u z hu.1 huz, ?_, fun v _ hv => hv z ⟨u, hin, huz⟩⟩
    intro b hb
    obtain ⟨a, haa, hab⟩ := hb
    refine (em (a = u)).elim (fun e => ?_) (fun hne' => ?_)
    · rw [e] at hab
      have ebz := huniq u b z hu.1 hab huz
      rw [ebz]
      exact hr z
    · exact ht b u z
        ((hA.2 u hin).2.1 b
          ⟨a, ⟨haa, hu.2.1 a haa,
            fun hua => hne' (ha a u (hu.2.1 a haa) hua)⟩, hab⟩) huzle
  have happ := append_conforming P R f hr ht A hA z below hs
  exact hnzu (hu.2.1 z (hMax _ happ z (Or.inr rfl)))


/-- Only the represented canonical union needs a supremum. This allows a
countability argument to establish that one supremum before invoking the lemma. -/
theorem canonical_fixedpoint_of_supremum {σ : Type} [Ty σ]
    (P : σ → Prop) (R f : σ → σ → Prop)
    (hr : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (ha : ∀ x y, R x y → R y x → x = y)
    (hserial : ∀ x, P x → ∃ y, f x y)
    (hclosed : ∀ x y, P x → f x y → P y)
    (hprog : ∀ x y, P x → f x y → R x y)
    (huniq : ∀ x y z, P x → f x y → f x z → y = z)
    (u : σ) (hu : DomainLUB P R (CanonicalUnion P R f) u) :
    CanonicalUnion P R f u ∧ f u u :=
  conforming_fixedpoint_of_supremum P R f hr ht ha hserial hclosed hprog huniq
    (CanonicalUnion P R f) (canonical_union_conforming P R f ht ha)
    (fun B hB x hx => ⟨B, hB, hx⟩) u hu

end Classicism.Research.Choice
