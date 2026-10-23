import Classicism.Results.Research.SectionsRetractionsPairs

/-!
# Retractions realize functional graphs

Direct source: `research/2026-10-22/notes/choice-uniformization.md`, §12,
Theorem 18 (`misc`, original research, 22 October 2026; unpaginated).
The mirrored injection uses relational pair codes, including when its original
input is an individual. No individual-valued operation is introduced.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def wrapPair {σ τ : Type} [Ty σ] [Ty τ]
    (k : σ → τ → Prop) : Prop → σ → τ → Prop :=
  fun r u v => r = True ∧ k u v

def junkPair {σ τ : Type} [Ty σ] [Ty τ]
    (k : σ → τ → Prop) : Prop → σ → τ → Prop :=
  fun r u v => (r = True ∧ k u v) ∨ r ≠ True

theorem wrapPair_true {σ τ : Type} [Ty σ] [Ty τ] (k : σ → τ → Prop) :
    wrapPair k True = k := funext fun u => funext fun v =>
  propext ⟨And.right, fun h => ⟨rfl, h⟩⟩

theorem junkPair_true {σ τ : Type} [Ty σ] [Ty τ] (k : σ → τ → Prop) :
    junkPair k True = k := funext fun u => funext fun v =>
  propext ⟨fun h => h.elim And.right (fun h => (h rfl).elim),
    fun h => Or.inl ⟨rfl, h⟩⟩

theorem wrapPair_ne_junk {σ τ : Type} [Ty σ] [Ty τ]
    (x : σ) (y : τ) (k l : σ → τ → Prop) : wrapPair k ≠ junkPair l := by
  intro he
  have h : wrapPair k False x y :=
    (congrFun (congrFun (congrFun he False) x) y).mpr
      (Or.inr (fun e => Eq.mpr e trivial))
  exact Eq.mpr h.1 trivial

def pairInjection {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (U : σ → τ → Prop) (w : Prop)
    (k : σ → τ → Prop) : Prop → σ → τ → Prop :=
  fun r => mixPair (E (ValidPair U k))
    (wrapPair (projectPair U w k) r) (junkPair k r)

theorem pairInjection_valid {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (w : Prop) (k : σ → τ → Prop) (hk : ValidPair U k) :
    pairInjection E U w k = wrapPair (projectPair U w k) := by
  unfold pairInjection
  rw [(hE _).1 hk]
  exact funext fun r => mixPair_true _ _

theorem pairInjection_invalid {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (w : Prop) (k : σ → τ → Prop) (hk : ¬ ValidPair U k) :
    pairInjection E U w k = junkPair k := by
  unfold pairInjection
  rw [(hE _).2 hk]
  exact funext fun r => mixPair_false _ _

theorem pairInjection_code {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (w : Prop) (hw : ActualWorld w) (x : σ) (y : τ) (hu : U x y) :
    pairInjection E U w (pairCode x y) = wrapPair (pin w x) :=
  (pairInjection_valid E hE U w (pairCode x y) ⟨x, y, hu, rfl⟩).trans
    (congrArg wrapPair (projectPair_actual U w hw x y hu))

theorem functional_outputs {σ τ : Type} [Ty σ] [Rel τ]
    (U : σ → τ → Prop) (hu : Functional U) (x : σ) (y z : τ) :
    U x y → U x z → y = z := fun hy hz =>
  (hu x).elim fun a ha => (ha.2 y hy).symm.trans (ha.2 z hz)

theorem pairInjection_injective {σ τ : Type} [Ty σ] [Rel τ]
    (E : Prop → Prop) (hE : ActualEvaluator E) (U : σ → τ → Prop)
    (hu : Functional U) (w : Prop) (hw : ActualWorld w) :
    Injective (pairInjection E U w) := by
  intro k l he
  refine (em (ValidPair U k)).elim (fun hk => ?_) (fun hk => ?_)
  · obtain ⟨x, y, hxy, hkc⟩ := hk
    have hkv : pairInjection E U w k = wrapPair (pin w x) :=
      (congrArg (pairInjection E U w) hkc).trans
        (pairInjection_code E hE U w hw x y hxy)
    refine (em (ValidPair U l)).elim (fun hl => ?_) (fun hl => ?_)
    · obtain ⟨x', y', hx'y', hlc⟩ := hl
      have hlv : pairInjection E U w l = wrapPair (pin w x') :=
        (congrArg (pairInjection E U w) hlc).trans
          (pairInjection_code E hE U w hw x' y' hx'y')
      have hp : pin (τ := τ) w x = pin w x' :=
        (wrapPair_true (pin w x)).symm.trans
          ((congrFun (hkv.symm.trans (he.trans hlv)) True).trans
            (wrapPair_true (pin w x')))
      have hx : x = x' := pin_injective w hw.1 x x' hp
      have hy : y = y' := functional_outputs U hu x y y' hxy (hx.symm ▸ hx'y')
      exact hkc.trans ((congrArg (fun a => pairCode a y) hx).trans
        ((congrArg (pairCode x') hy).trans hlc.symm))
    · exact (wrapPair_ne_junk x y (pin w x) l
        (hkv.symm.trans (he.trans (pairInjection_invalid E hE U w l hl)))).elim
  · refine (em (ValidPair U l)).elim (fun hl => ?_) (fun hl => ?_)
    · obtain ⟨x, y, hxy, hlc⟩ := hl
      have hlv : pairInjection E U w l = wrapPair (pin w x) :=
        (congrArg (pairInjection E U w) hlc).trans
          (pairInjection_code E hE U w hw x y hxy)
      exact (wrapPair_ne_junk x y (pin w x) k
        (hlv.symm.trans (he.symm.trans (pairInjection_invalid E hE U w k hk)))).elim
    · have hj : junkPair k = junkPair l :=
        (pairInjection_invalid E hE U w k hk).symm.trans
          (he.trans (pairInjection_invalid E hE U w l hl))
      exact (junkPair_true k).symm.trans ((congrFun hj True).trans (junkPair_true l))

theorem evaluator_retractions_plenitude {ν σ : Type} [Ty ν] [Ty σ] :
    HasActualEvaluator →
    LeftSplitting (σ → (ν → Prop) → Prop) (Prop → σ → (ν → Prop) → Prop) →
    Plenitude σ (ν → Prop) := by
  intro be sl U hu
  obtain ⟨E, hE⟩ := be
  let w := truthKernel E
  have hw : ActualWorld w := positiveEvaluator_actualWorld E (actualEvaluator_positive E hE)
  obtain ⟨g, hg⟩ := sl (pairInjection E U w) (pairInjection_injective E hE U hu w hw)
  let h : σ → ν → Prop := fun x => decodePair (g (wrapPair (pin w x))) x
  refine ⟨h, fun x => ?_⟩
  obtain ⟨y, hy, _⟩ := hu x
  have hk : g (wrapPair (pin w x)) = pairCode x y :=
    (congrArg g (pairInjection_code E hE U w hw x y hy)).symm.trans (hg (pairCode x y))
  have he : h x = y := (congrArg (fun k => decodePair k x) hk).trans (decodePair_code x y)
  exact Eq.mpr (congrArg (U x) he) hy

theorem actuality_retractions_evaluator :
    Actuality → LeftSplitting Prop (Prop → Prop) → HasActualEvaluator := by
  intro act sl
  obtain ⟨w, hw⟩ := act
  exact ⟨worldEvaluator w,
    worldEvaluator_actual w hw (truth_retractions_modal_b sl w hw.1)⟩

theorem actuality_retractions_plenitude {ν σ : Type} [Ty ν] [Ty σ] :
    Actuality → LeftSplitting Prop (Prop → Prop) →
    LeftSplitting (σ → (ν → Prop) → Prop) (Prop → σ → (ν → Prop) → Prop) →
    Plenitude σ (ν → Prop) :=
  fun act sl₀ sl => evaluator_retractions_plenitude (actuality_retractions_evaluator act sl₀) sl

end Classicism.Research.Splitting
