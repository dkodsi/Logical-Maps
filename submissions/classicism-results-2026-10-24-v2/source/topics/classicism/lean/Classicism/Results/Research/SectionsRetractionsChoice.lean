import Classicism.Results.Research.SectionsRetractionsPairs

/-!
# Sections realize arbitrary relational choices

Direct source: `research/2026-10-22/notes/functional-choice-by-sections.md`,
§3 (`misc`, original research, 22 October 2026; unpaginated).
The first type parameter of the final law is the output argument, so its
list rule covers every relational output, including t. The input may be e.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def choiceRoute {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (U : σ → τ → Prop) (w : Prop) (x₀ : σ)
    (H : Prop → σ → τ → Prop) : σ → τ → Prop :=
  mixPair (E (ValidPair U (H True))) (projectPair U w (H True))
    (mixPair (E (PinRange w (H False))) (pin w x₀) (H False))

theorem choiceRoute_valid {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (w : Prop) (x₀ : σ) (H : Prop → σ → τ → Prop)
    (hv : ValidPair U (H True)) : choiceRoute E U w x₀ H = projectPair U w (H True) := by
  unfold choiceRoute
  rw [(hE _).1 hv, mixPair_true]

theorem choiceRoute_escape {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (w : Prop) (x₀ : σ) (H : Prop → σ → τ → Prop)
    (hv : ¬ ValidPair U (H True)) (hb : ¬ PinRange w (H False)) :
    choiceRoute E U w x₀ H = H False := by
  unfold choiceRoute
  rw [(hE _).2 hv, mixPair_false, (hE _).2 hb, mixPair_false]

theorem choiceRoute_default {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (w : Prop) (x₀ : σ) (H : Prop → σ → τ → Prop)
    (hv : ¬ ValidPair U (H True)) (hb : PinRange w (H False)) :
    choiceRoute E U w x₀ H = pin w x₀ := by
  unfold choiceRoute
  rw [(hE _).2 hv, mixPair_false, (hE _).1 hb, mixPair_true]

theorem choiceRoute_surjective {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (hu : Serial U) (w : Prop) (hw : ActualWorld w) (x₀ : σ) :
    Surjective (choiceRoute E U w x₀) := by
  intro b
  refine (em (PinRange w b)).elim (fun hb => ?_) (fun hb => ?_)
  · obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := hu x
    let H := slotsPair (fun (_ : σ) (_ : τ) => False) (pairCode x y)
    have ht : H True = pairCode x y := slotsPair_true _ _
    refine ⟨H, ?_⟩
    calc choiceRoute E U w x₀ H = projectPair U w (H True) :=
           choiceRoute_valid E hE U w x₀ H ⟨x, y, hy, ht⟩
      _ = projectPair U w (pairCode x y) := congrArg (projectPair U w) ht
      _ = pin w x := projectPair_actual U w hw x y hy
      _ = b := hx.symm
  · let H := slotsPair b (fun (_ : σ) (_ : τ) => False)
    have ht : H True = (fun (_ : σ) (_ : τ) => False) := slotsPair_true _ _
    have hf : H False = b := slotsPair_false _ _
    have hv : ¬ ValidPair U (H True) :=
      fun h => invalid_bottom U (Eq.mp (congrArg (ValidPair U) ht) h)
    have hn : ¬ PinRange w (H False) :=
      fun h => hb (Eq.mp (congrArg (PinRange w) hf) h)
    exact ⟨H, (choiceRoute_escape E hE U w x₀ H hv hn).trans hf⟩

theorem choiceRoute_section_code {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (w : Prop) (hw : ActualWorld w) (x₀ : σ)
    (s : (σ → τ → Prop) → Prop → σ → τ → Prop)
    (hs : RightInverse (choiceRoute E U w x₀) s) (x : σ) (hx : x ≠ x₀) :
    ∃ y, U x y ∧ s (pin w x) True = pairCode x y := by
  let H := s (pin w x)
  have he : choiceRoute E U w x₀ H = pin w x := hs (pin w x)
  have hv : ValidPair U (H True) := by
    refine (em (ValidPair U (H True))).elim id (fun hn => ?_)
    refine (em (PinRange w (H False))).elim (fun hb => ?_) (fun hb => ?_)
    · have hpin : pin (τ := τ) w x₀ = pin w x :=
        (choiceRoute_default E hE U w x₀ H hn hb).symm.trans he
      exact (hx (pin_injective w hw.1 x₀ x hpin).symm).elim
    · have hpin : H False = pin w x :=
        (choiceRoute_escape E hE U w x₀ H hn hb).symm.trans he
      exact (hb ⟨x, hpin⟩).elim
  obtain ⟨a, y, hu, hk⟩ := hv
  have hp : projectPair U w (H True) = pin w x :=
    (choiceRoute_valid E hE U w x₀ H ⟨a, y, hu, hk⟩).symm.trans he
  have ha : a = x := pin_injective w hw.1 a x
    ((projectPair_actual U w hw a y hu).symm.trans
      ((congrArg (projectPair U w) hk).symm.trans hp))
  exact ⟨y, ha ▸ hu, hk.trans (congrArg (fun z => pairCode z y) ha)⟩

theorem evaluator_sections_choice {ν σ : Type} [Ty ν] [Ty σ] :
    HasActualEvaluator →
    RightSplitting (Prop → σ → (ν → Prop) → Prop) (σ → (ν → Prop) → Prop) →
    FunctionalChoice σ (ν → Prop) := by
  intro be sr U hu
  obtain ⟨E, hE⟩ := be
  let w := truthKernel E
  have hw : ActualWorld w := positiveEvaluator_actualWorld E (actualEvaluator_positive E hE)
  refine (em (∃ x : σ, x = x)).elim (fun hex => ?_) (fun hn => ?_)
  · obtain ⟨x₀, _⟩ := hex
    obtain ⟨y₀, hy₀⟩ := hu x₀
    obtain ⟨s, hs⟩ := sr (choiceRoute E U w x₀)
      (choiceRoute_surjective E hE U hu w hw x₀)
    let h : σ → ν → Prop := fun x =>
      mix (E (x = x₀)) y₀ (decodePair (s (pin w x) True) x)
    refine ⟨h, fun x => ?_⟩
    refine (em (x = x₀)).elim (fun hx => ?_) (fun hx => ?_)
    · have he : h x = y₀ :=
        (congrArg (fun p => mix p y₀ (decodePair (s (pin w x) True) x))
          ((hE (x = x₀)).1 hx)).trans (mix_true _ _)
      exact Eq.mpr (congrArg (U x) he) (hx.symm ▸ hy₀)
    · obtain ⟨y, hy, hk⟩ := choiceRoute_section_code E hE U w hw x₀ s hs x hx
      have hd : decodePair (s (pin w x) True) x = y :=
        (congrArg (fun k => decodePair k x) hk).trans (decodePair_code x y)
      have he : h x = y :=
        ((congrArg (fun p => mix p y₀ (decodePair (s (pin w x) True) x))
          ((hE (x = x₀)).2 hx)).trans (mix_false _ _)).trans hd
      exact Eq.mpr (congrArg (U x) he) hy
  · exact ⟨fun _ _ => False, fun x => (hn ⟨x, rfl⟩).elim⟩

theorem actuality_sections_choice {ν σ : Type} [Ty ν] [Ty σ] :
    Actuality → RightSplitting (Prop → Prop) Prop →
    RightSplitting (Prop → σ → (ν → Prop) → Prop) (σ → (ν → Prop) → Prop) →
    FunctionalChoice σ (ν → Prop) :=
  fun act sr₀ sr => evaluator_sections_choice (actuality_sections_evaluator act sr₀) sr

end Classicism.Research.Splitting
