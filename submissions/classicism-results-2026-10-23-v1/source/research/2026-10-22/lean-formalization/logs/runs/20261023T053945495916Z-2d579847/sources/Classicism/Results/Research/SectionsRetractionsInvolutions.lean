import Classicism.Results.Research.SectionsRetractionsPlenitude

/-!
# Pairing representation is Plenitude

Direct source: `research/2026-10-22/notes/reversible-comprehension-and-algebraic-laws.md`,
§1 (misc; original research, 22 October 2026; unpaginated).
The construction codes inputs, including individuals, by relational pair codes.
All graph assertions are actual. No operation with individual output is used.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def xorOutput {ν : Type} [Ty ν] (z y : ν → Prop) : ν → Prop :=
  fun u => (z u ∧ ¬ y u) ∨ (¬ z u ∧ y u)

theorem xorOutput_twice {ν : Type} [Ty ν] (z y : ν → Prop) :
    xorOutput (xorOutput z y) y = z :=
  funext fun u => propext
    ⟨fun h => h.elim
      (fun h => h.1.elim And.left (fun h' => (h.2 h'.2).elim))
      (fun h => (em (z u)).elim id (fun hn => (h.1 (Or.inr ⟨hn, h.2⟩)).elim)),
     fun hz => (em (y u)).elim
      (fun hy => Or.inr ⟨fun h => h.elim (fun h => h.2 hy) (fun h => h.1 hz), hy⟩)
      (fun hn => Or.inl ⟨Or.inl ⟨hz, hn⟩, hn⟩)⟩

theorem xorOutput_zero {ν : Type} [Ty ν] (y : ν → Prop) :
    xorOutput (fun _ => False) y = y :=
  funext fun u => propext
    ⟨fun h => h.elim (fun h => h.1.elim) And.right,
     fun hy => Or.inr ⟨fun hf => hf, hy⟩⟩

def HasPairCode {σ τ : Type} [Ty σ] [Ty τ] (k : σ → τ → Prop) : Prop :=
  ∃ x z, k = pairCode x z

def pairSwap {σ ν : Type} [Ty σ] [Ty ν]
    (U : σ → (ν → Prop) → Prop) (k l : σ → (ν → Prop) → Prop) : Prop :=
  (∃ x z y, U x y ∧ k = pairCode x z ∧ l = pairCode x (xorOutput z y)) ∨
    (¬ HasPairCode k ∧ l = k)

def PairingRepresentation (A : Type) [Rel A] : Prop :=
  ∀ R : A → A → Prop, Functional R → (∀ a b, R a b → R b a) →
    ∃ f : A → A, ∀ a, R a (f a)

theorem plenitude_pairing_representation {A : Type} [Rel A] :
    Plenitude A A → PairingRepresentation A := fun pl R hr _ => pl R hr

theorem pairSwap_value {σ ν : Type} [Ty σ] [Ty ν]
    (U : σ → (ν → Prop) → Prop) (hu : Functional U)
    (x : σ) (z y : ν → Prop) (hy : U x y) (l : σ → (ν → Prop) → Prop) :
    pairSwap U (pairCode x z) l → l = pairCode x (xorOutput z y) := by
  intro h
  refine h.elim (fun h => ?_) (fun h => (h.1 ⟨x, z, rfl⟩).elim)
  obtain ⟨x', z', y', hy', he, hl⟩ := h
  have hc := pairCode_components x x' z z' he
  have heY : y' = y := functional_outputs U hu x y' y (hc.1.symm ▸ hy') hy
  exact hl.trans ((congrArg (fun a => pairCode a (xorOutput z' y')) hc.1.symm).trans
    ((congrArg (fun b => pairCode x (xorOutput b y')) hc.2.symm).trans
      (congrArg (fun a => pairCode x (xorOutput z a)) heY)))

theorem pairSwap_functional {σ ν : Type} [Ty σ] [Ty ν]
    (U : σ → (ν → Prop) → Prop) (hu : Functional U) : Functional (pairSwap U) := by
  intro k
  refine (em (HasPairCode k)).elim (fun hk => ?_) (fun hk => ?_)
  · obtain ⟨x, z, he⟩ := hk
    obtain ⟨y, hy, _⟩ := hu x
    refine ⟨pairCode x (xorOutput z y), Or.inl ⟨x, z, y, hy, he, rfl⟩, ?_⟩
    intro l hl
    exact (pairSwap_value U hu x z y hy l (he ▸ hl)).symm
  · refine ⟨k, Or.inr ⟨hk, rfl⟩, fun l hl => ?_⟩
    exact hl.elim
      (fun h => h.elim fun x hx => hx.elim fun z hz => hz.elim fun y hy =>
        (hk ⟨x, z, hy.2.1⟩).elim)
      (fun h => h.2.symm)

theorem pairSwap_symmetric {σ ν : Type} [Ty σ] [Ty ν]
    (U : σ → (ν → Prop) → Prop) : ∀ k l, pairSwap U k l → pairSwap U l k := by
  intro k l h
  refine h.elim (fun h => ?_) (fun h => ?_)
  · obtain ⟨x, z, y, hy, hk, hl⟩ := h
    exact Or.inl ⟨x, xorOutput z y, y, hy, hl,
      hk.trans (congrArg (pairCode x) (xorOutput_twice z y).symm)⟩
  · exact Or.inr ⟨fun hl => h.1 (h.2 ▸ hl), h.2.symm⟩

theorem pairing_representation_plenitude {ν σ : Type} [Ty ν] [Ty σ] :
    PairingRepresentation (σ → (ν → Prop) → Prop) → Plenitude σ (ν → Prop) := by
  intro pr U hu
  obtain ⟨f, hf⟩ := pr (pairSwap U) (pairSwap_functional U hu) (pairSwap_symmetric U)
  let h : σ → ν → Prop := fun x => decodePair (f (pairCode x (fun _ => False))) x
  refine ⟨h, fun x => ?_⟩
  obtain ⟨y, hy, _⟩ := hu x
  have he : f (pairCode x (fun _ => False)) = pairCode x y :=
    (pairSwap_value U hu x (fun _ => False) y hy _ (hf _)).trans
      (congrArg (pairCode x) (xorOutput_zero y))
  have hd : h x = y := (congrArg (fun k => decodePair k x) he).trans (decodePair_code x y)
  exact Eq.mpr (congrArg (U x) hd) hy

end Classicism.Research.Splitting
