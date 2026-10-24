import Classicism.Results.Research.C5Frege

/-!
# Finite Hume classes from actual bijection graphs

Direct source: research/2026-10-22/notes/frege-infinity-20261022-1726.md §25.3,
unpaginated original research, misc. Bijections are relations, including when the
base is the individual sort. Each existential choice occurs inside one Frege
induction step; no selecting operation or Plenitude is assumed.
-/
namespace Classicism.Research.FregeHumeClasses
open Classicism.Paper
open Classicism.Research.FregeFiniteSets

variable {σ : Type} [Ty σ]

def Bijection (A B : σ → Prop) (R : σ → σ → Prop) : Prop :=
  (∀ x, A x → ∃ y, R x y) ∧
  (∀ x y, R x y → A x ∧ B y) ∧
  (∀ x y z, R x y → R x z → y = z) ∧
  (∀ x z y, R x y → R z y → x = z) ∧
  (∀ y, B y → ∃ x, R x y)

def Equinumerous (A B : σ → Prop) : Prop := ∃ R : σ → σ → Prop, Bijection A B R

def Hume (A : σ → Prop) : (σ → Prop) → Prop := fun B => Equinumerous A B

theorem bijection_adjoin (A B : σ → Prop) (a b : σ) (ha : A a) (hb : B b)
    (R : σ → σ → Prop)
    (hR : Bijection (fun x => A x ∧ x ≠ a) (fun y => B y ∧ y ≠ b) R) :
    Bijection A B (fun x y => (x = a ∧ y = b) ∨ R x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (em (x = a)).elim (fun he => ⟨b, Or.inl ⟨he, rfl⟩⟩)
      (fun he => (hR.1 x ⟨hx, he⟩).elim fun y hy => ⟨y, Or.inr hy⟩)
  · intro x y h
    exact h.elim (fun he => ⟨he.1.symm ▸ ha, he.2.symm ▸ hb⟩)
      (fun hr => ⟨(hR.2.1 x y hr).1.1, (hR.2.1 x y hr).2.1⟩)
  · intro x y z hy hz
    apply hy.elim
    · intro hy
      exact hz.elim (fun hz => hy.2.trans hz.2.symm)
        (fun hz => ((hR.2.1 x z hz).1.2 hy.1).elim)
    · intro hy
      exact hz.elim (fun hz => ((hR.2.1 x y hy).1.2 hz.1).elim)
        (fun hz => hR.2.2.1 x y z hy hz)
  · intro x z y hx hz
    apply hx.elim
    · intro hx
      exact hz.elim (fun hz => hx.1.trans hz.1.symm)
        (fun hz => ((hR.2.1 z y hz).2.2 hx.2).elim)
    · intro hx
      exact hz.elim (fun hz => ((hR.2.1 x y hx).2.2 hz.2).elim)
        (fun hz => hR.2.2.2.1 x z y hx hz)
  · intro y hy
    exact (em (y = b)).elim (fun he => ⟨a, Or.inl ⟨rfl, he⟩⟩)
      (fun he => (hR.2.2.2.2 y ⟨hy, he⟩).elim fun x hx => ⟨x, Or.inr hx⟩)

theorem equinumerous_of_common_count (n : (σ → Prop) → Prop)
    (hn : FiniteCardinality n) :
    ∀ A B : σ → Prop, n A → n B → Equinumerous A B := by
  apply hn (fun m => ∀ A B : σ → Prop, m A → m B → Equinumerous A B)
  constructor
  · intro A B ha hb
    exact ⟨(fun _ _ => False), ⟨fun x hx => (ha x hx).elim,
      fun _ _ h => h.elim, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim,
      fun y hy => (hb y hy).elim⟩⟩
  · intro m hm A B ha hb
    obtain ⟨a, ha, hdelA⟩ := ha
    obtain ⟨b, hb, hdelB⟩ := hb
    obtain ⟨R, hR⟩ := hm (fun x => A x ∧ x ≠ a) (fun y => B y ∧ y ≠ b) hdelA hdelB
    exact ⟨(fun x y => (x = a ∧ y = b) ∨ R x y), bijection_adjoin A B a b ha hb R hR⟩

theorem count_of_bijection (n : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (A B : σ → Prop) (hA : n A) (R : σ → σ → Prop) (hR : Bijection A B R) : n B := by
  have hi : n (Image A R) := injective_image_count n hn A R hA hR.1
    (fun x y z _ => hR.2.2.1 x y z) (fun x z y _ _ => hR.2.2.2.1 x z y)
  apply finiteCardinality_coext n hn (Image A R) B hi
  intro y
  constructor
  · intro h
    obtain ⟨x, _, hxy⟩ := h
    exact (hR.2.1 x y hxy).2
  · intro hy
    obtain ⟨x, hxy⟩ := hR.2.2.2.2 y hy
    exact ⟨x, (hR.2.1 x y hxy).1, hxy⟩

theorem count_iff_equinumerous (n : (σ → Prop) → Prop) :
    FiniteCardinality n → ∀ A : σ → Prop, n A →
      ∀ B : σ → Prop, n B ↔ Equinumerous A B := by
  intro hn A ha B
  exact ⟨equinumerous_of_common_count n hn A B ha,
    fun h => h.elim fun R hR => count_of_bijection n hn A B ha R hR⟩

theorem hume_eq_number_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (A : σ → Prop) (hA : Persistent A)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) (hnA : n A) : Hume A = n := by
  apply Eq.symm
  apply intensionality n (Hume A)
  have h := modal_K _ _ (nec% (count_iff_equinumerous n)) (frege_number_persistent n hn)
  have hAcount : □ (n A) := (C5Frege.persistent_count_settled c5 n hn A hA).1 hnA
  exact modal_K _ _ (converse_barcan (fun X => n X → ∀ B, n B ↔ Equinumerous X B) h A)
    hAcount

theorem hume_is_number_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (A : σ → Prop) (hA : Persistent A) (hf : Finite A) : FiniteCardinality (Hume A) := by
  obtain ⟨n, hn, hnA⟩ := hf
  exact (hume_eq_number_c5 c5 A hA n hn hnA).symm ▸ hn

theorem hume_identity_iff_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (A B : σ → Prop) (hA : Persistent A) (hB : Persistent B)
    (hfA : Finite A) (hfB : Finite B) : Hume A = Hume B ↔ Equinumerous A B := by
  obtain ⟨n, hn, hnA⟩ := hfA
  obtain ⟨m, hm, hmB⟩ := hfB
  have heA := hume_eq_number_c5 c5 A hA n hn hnA
  have heB := hume_eq_number_c5 c5 B hB m hm hmB
  constructor
  · intro he
    have hnm : n = m := heA.symm.trans (he.trans heB)
    exact (count_iff_equinumerous n hn A hnA B).1 (hnm.symm ▸ hmB)
  · intro he
    have hnB := (count_iff_equinumerous n hn A hnA B).2 he
    exact heA.trans ((frege_common_instance_eq n m hn hm B hnB hmB).trans heB.symm)

end Classicism.Research.FregeHumeClasses
