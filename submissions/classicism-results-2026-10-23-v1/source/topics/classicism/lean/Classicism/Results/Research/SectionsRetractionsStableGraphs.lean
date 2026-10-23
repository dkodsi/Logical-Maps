import Classicism.Results.Research.SectionsRetractionsPairs

/-!
# Stable unique graph representation is Barcan

Direct source: `research/2026-10-22/notes/choice-uniformization.md`, §2,
Theorems 3–4 (`misc`, original research, 22 October 2026; unpaginated).
Stable uniqueness puts a fixed witness inside a box separately for each input.
It is stronger than ordinary current functionality; no witness is chosen by
an external choice operator in the representing lambda term.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def StableUnique {σ τ : Type} [Ty σ] [Rel τ] (U : σ → τ → Prop) : Prop :=
  ∀ x, ∃ y, □ (U x y ∧ ∀ z, U x z → z = y)

def StableUniqueGraphRepresentation (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ U : σ → τ → Prop, StableUnique U → ∃ f : σ → τ, □ (∀ x, U x (f x))

theorem unique_decode_coext {σ ν : Type} [Ty σ] [Ty ν]
    (U : σ → (ν → Prop) → Prop) (x : σ) (y : ν → Prop) :
    (U x y ∧ ∀ z, U x z → z = y) → decodePair U x ≡ y := by
  intro h u
  exact ⟨fun hu => hu.elim fun z hz => h.2 z hz.1 ▸ hz.2,
    fun hu => ⟨y, h.1, hu⟩⟩

theorem stable_unique_decode {σ ν : Type} [Ty σ] [Ty ν]
    (U : σ → (ν → Prop) → Prop) (hu : StableUnique U) (x : σ) :
    □ (U x (decodePair U x)) := by
  obtain ⟨y, hy⟩ := hu x
  have he : decodePair U x = y :=
    intensionality _ _ (modal_K _ _ (nec% (unique_decode_coext U x y)) hy)
  have hxy : □ (U x y) := modal_K _ _
    (nec% (fun (h : U x y ∧ ∀ z, U x z → z = y) => h.1)) hy
  exact Eq.mpr (congrArg (fun z => □ (U x z)) he) hxy

theorem barcan_stable_unique_graphs {ν σ : Type} [Ty ν] [Ty σ] :
    Barcan σ → StableUniqueGraphRepresentation σ (ν → Prop) :=
  fun bf U hu => ⟨decodePair U, bf (fun x => U x (decodePair U x))
    (stable_unique_decode U hu)⟩

theorem truth_graph_stable {σ : Type} [Ty σ] (P : σ → Prop) :
    (∀ x, □ (P x)) → StableUnique (fun x (q : Prop) => P x ∧ q = True) :=
  fun hp x => ⟨True, modal_K _ _
    (nec% (fun (h : P x) =>
      (⟨⟨h, rfl⟩, fun _ hz => hz.2⟩ :
        (P x ∧ True = True) ∧ ∀ z : Prop, (P x ∧ z = True) → z = True)))
    (hp x)⟩

theorem stable_unique_truth_graphs_barcan {σ : Type} [Ty σ] :
    StableUniqueGraphRepresentation σ Prop → Barcan σ := by
  intro sg P hp
  obtain ⟨f, hf⟩ := sg (fun x (q : Prop) => P x ∧ q = True) (truth_graph_stable P hp)
  exact modal_K _ _ (nec% (fun (h : ∀ x, P x ∧ f x = True) (x : σ) => (h x).1)) hf

theorem uniform_graph_witnesses {σ τ : Type} [Ty σ] [Rel τ]
    (U : σ → τ → Prop) :
    (∃ f : σ → τ, □ (∀ x, U x (f x))) → ∀ x, ∃ y, □ (U x y) :=
  fun hf x => hf.elim fun f h => ⟨f x, converse_barcan (fun z => U z (f z)) h x⟩

theorem stable_subgraph_functional {σ τ : Type} [Ty σ] [Rel τ]
    (U : σ → τ → Prop) (hu : Functional U) (hs : ∀ x, ∃ y, □ (U x y)) :
    Functional (fun x y => □ (U x y)) := by
  intro x
  obtain ⟨y, hy⟩ := hs x
  obtain ⟨a, _, ha⟩ := hu x
  exact ⟨y, hy, fun z hz => (ha y (box_elim hy)).symm.trans (ha z (box_elim hz))⟩

theorem uniform_graph_iff_stable_witnesses {σ τ : Type} [Ty σ] [Rel τ]
    (pl : Plenitude σ τ) (bf : Barcan σ) (U : σ → τ → Prop) (hu : Functional U) :
    (∃ f : σ → τ, □ (∀ x, U x (f x))) ↔ ∀ x, ∃ y, □ (U x y) := by
  refine ⟨uniform_graph_witnesses U, fun hs => ?_⟩
  obtain ⟨f, hf⟩ := pl (fun x y => □ (U x y)) (stable_subgraph_functional U hu hs)
  exact ⟨f, bf (fun x => U x (f x)) hf⟩

end Classicism.Research.Splitting
