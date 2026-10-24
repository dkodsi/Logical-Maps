import Classicism.Results.Research.ActualityCoreNumbers
import Classicism.Results.Research.FregeArithmeticGraphs

/-!
# Addition and multiplication in the actual supported core

Direct source: `research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md`,
§3 (unpaginated original research, `misc`). The least-graph definitions make the
recurrence argument explicit. Core quantification is over admitted supported
binary relations, and the pushed graph used for reflection is proved admitted.

Forward transfer and target totality need Actuality only. Reflection and target
functionality additionally use quantified Infinity. These are current graph and
represented-subset comparisons, not identities of arbitrary ambient predicates,
external standardness, or a truth lemma for all higher-order syntax.
-/

namespace Classicism.Research.ActualityCoreArithmetic
open Classicism.Paper Classicism.P Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.FregeArithmeticGraphs

variable {σ : Type} [Ty σ]

def BinarySupport (w : Prop) :
    ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop :=
  fun x y => Cardinals w x ∧ Cardinals w y

def TernarySupport (w : Prop) : ((σ → Prop) → Prop) →
    ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop :=
  fun x y z => Cardinals w x ∧ Cardinals w y ∧ Cardinals w z

def BinaryPush (w : Prop)
    (R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)
    (x y : (σ → Prop) → Prop) : Prop :=
  Cardinals w x ∧ Cardinals w y ∧ ∃ i j,
    FiniteCardinality i ∧ FiniteCardinality j ∧
      numberMap w i = x ∧ numberMap w j = y ∧ R i j

theorem binaryPush_admitted (w : Prop) (hw : ActualWorld w)
    (R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop) :
    Domain w (BinarySupport w) (BinaryPush w R) :=
  ⟨hw.1, le_of_box_incl (nec% (fun (x y : (σ → Prop) → Prop)
    (h : BinaryPush w R x y) => ⟨h.1, h.2.1⟩))⟩

theorem binary_push_pull (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)
    (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) :
    BinaryPush w R (numberMap w a) (numberMap w b) ↔ R a b := by
  constructor
  · intro h
    obtain ⟨i, j, hi, hj, hie, hje, hij⟩ := h.2.2
    have hei : i = a := numberMap_injective w hw hInf i a hi ha hie
    have hej : j = b := numberMap_injective w hw hInf j b hj hb hje
    exact hej ▸ (hei ▸ hij)
  · intro h
    exact ⟨numberMap_in_cardinals w hw a, numberMap_in_cardinals w hw b,
      a, b, ha, hb, rfl, rfl, h⟩

theorem binary_pull_push (w : Prop) (hw : ActualWorld w)
    (R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)
    (x y : (σ → Prop) → Prop) (hx : Numbers w x) (hy : Numbers w y) :
    BinaryPush w (fun i j => R (numberMap w i) (numberMap w j)) x y ↔ R x y := by
  constructor
  · intro h
    obtain ⟨i, j, _, _, hie, hje, hij⟩ := h.2.2
    exact hje ▸ (hie ▸ hij)
  · intro h
    obtain ⟨i, hi, hie⟩ := numberMap_onto w hw x hx
    obtain ⟨j, hj, hje⟩ := numberMap_onto w hw y hy
    refine ⟨hx.1, hy.1, i, j, hi, hj, hie, hje, ?_⟩
    change R (numberMap w i) (numberMap w j)
    rw [hie, hje]
    exact h

/-- Core addition quantifies over its admitted supported binary predicates. -/
def CoreAdd (w : Prop) (a b c : (σ → Prop) → Prop) : Prop :=
  Numbers w a ∧ Numbers w b ∧ Numbers w c ∧
    ∀ R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop,
      Domain w (BinarySupport w) R → R (coreZero w) a →
      (∀ i j, Numbers w i → Numbers w j →
        R i j → R (coreSuc w i) (coreSuc w j)) → R b c

theorem coreAdd_admitted (w : Prop) (hw : ActualWorld w) :
    Domain w (TernarySupport (σ := σ) w) (CoreAdd w) :=
  ⟨hw.1, le_of_box_incl (nec% (fun (a b c : (σ → Prop) → Prop)
    (h : CoreAdd w a b c) => ⟨h.1.1, h.2.1.1, h.2.2.1.1⟩))⟩

theorem core_add_zero (w : Prop) (hw : ActualWorld w)
    (a : (σ → Prop) → Prop) (ha : Numbers w a) : CoreAdd w a (coreZero w) a :=
  ⟨ha, numbers_zero w hw, ha, fun _ _ hzero _ => hzero⟩

theorem core_add_suc (w : Prop) (hw : ActualWorld w)
    (a b c : (σ → Prop) → Prop) (h : CoreAdd w a b c) :
    CoreAdd w a (coreSuc w b) (coreSuc w c) :=
  ⟨h.1, numbers_suc w hw b h.2.1, numbers_suc w hw c h.2.2.1,
    fun R hR hzero hstep => hstep b c h.2.1 h.2.2.1 (h.2.2.2 R hR hzero hstep)⟩

theorem add_forward (w : Prop) (hw : ActualWorld w)
    (a b c : (σ → Prop) → Prop) (h : AddGraph a b c) :
    CoreAdd w (numberMap w a) (numberMap w b) (numberMap w c) := by
  refine ⟨numberMap_forward w hw a h.1, numberMap_forward w hw b h.2.1,
    numberMap_forward w hw c h.2.2.1, ?_⟩
  intro R _ hzero hstep
  apply h.2.2.2 (fun i j => R (numberMap w i) (numberMap w j)) hzero
  intro i j hi hj hij
  rw [numberMap_suc w hw i, numberMap_suc w hw j]
  exact hstep _ _ (numberMap_forward w hw i hi) (numberMap_forward w hw j hj) hij

theorem add_reflect (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) (hc : FiniteCardinality c)
    (h : CoreAdd w (numberMap w a) (numberMap w b) (numberMap w c)) :
    AddGraph a b c := by
  apply (binary_push_pull w hw hInf (AddGraph a) b c hb hc).1
  apply h.2.2.2 (BinaryPush w (AddGraph a)) (binaryPush_admitted w hw (AddGraph a))
  · exact ⟨numberMap_in_cardinals w hw (ZeroCard σ), numberMap_in_cardinals w hw a,
      ZeroCard σ, a, finiteCardinality_zero, ha, rfl, rfl, add_zero a ha⟩
  · intro x y _ _ hxy
    obtain ⟨i, j, hi, hj, hie, hje, hij⟩ := hxy.2.2
    exact ⟨coreSuc_in_cardinals w hw x, coreSuc_in_cardinals w hw y,
      SucCard i, SucCard j, finiteCardinality_suc i hi, finiteCardinality_suc j hj,
      (numberMap_suc w hw i).trans (congrArg (coreSuc w) hie),
      (numberMap_suc w hw j).trans (congrArg (coreSuc w) hje), add_suc a i j hij⟩

theorem addition_iff (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) (hc : FiniteCardinality c) :
    AddGraph a b c ↔ CoreAdd w (numberMap w a) (numberMap w b) (numberMap w c) :=
  ⟨add_forward w hw a b c, add_reflect w hw hInf a b c ha hb hc⟩

theorem core_add_total (w : Prop) (hw : ActualWorld w)
    (a b : (σ → Prop) → Prop) (ha : Numbers w a) (hb : Numbers w b) :
    ∃ c, CoreAdd w a b c := by
  obtain ⟨i, hi, hie⟩ := numberMap_onto w hw a ha
  obtain ⟨j, hj, hje⟩ := numberMap_onto w hw b hb
  obtain ⟨k, hijk⟩ := add_total i j hi hj
  exact ⟨numberMap w k, hje ▸ (hie ▸ add_forward w hw i j k hijk)⟩

theorem core_add_functional (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c d : (σ → Prop) → Prop) (hc : CoreAdd w a b c)
    (hd : CoreAdd w a b d) : c = d := by
  obtain ⟨i, hi, hie⟩ := numberMap_onto w hw a hc.1
  obtain ⟨j, hj, hje⟩ := numberMap_onto w hw b hc.2.1
  obtain ⟨k, hk, hke⟩ := numberMap_onto w hw c hc.2.2.1
  obtain ⟨l, hl, hle⟩ := numberMap_onto w hw d hd.2.2.1
  have hsrc : AddGraph i j k := add_reflect w hw hInf i j k hi hj hk
    (hke.symm ▸ (hje.symm ▸ (hie.symm ▸ hc)))
  have htgt : AddGraph i j l := add_reflect w hw hInf i j l hi hj hl
    (hle.symm ▸ (hje.symm ▸ (hie.symm ▸ hd)))
  exact hke.symm.trans ((congrArg (numberMap w)
    (add_functional hInf i j hj k l hsrc htgt)).trans hle)

def CoreMul (w : Prop) (a b c : (σ → Prop) → Prop) : Prop :=
  Numbers w a ∧ Numbers w b ∧ Numbers w c ∧
    ∀ R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop,
      Domain w (BinarySupport w) R → R (coreZero w) (coreZero w) →
      (∀ i j k, Numbers w i → Numbers w j → Numbers w k →
        R i j → CoreAdd w a j k → R (coreSuc w i) k) → R b c

theorem coreMul_admitted (w : Prop) (hw : ActualWorld w) :
    Domain w (TernarySupport (σ := σ) w) (CoreMul w) :=
  ⟨hw.1, le_of_box_incl (nec% (fun (a b c : (σ → Prop) → Prop)
    (h : CoreMul w a b c) => ⟨h.1.1, h.2.1.1, h.2.2.1.1⟩))⟩

theorem core_mul_zero (w : Prop) (hw : ActualWorld w)
    (a : (σ → Prop) → Prop) (ha : Numbers w a) :
    CoreMul w a (coreZero w) (coreZero w) :=
  ⟨ha, numbers_zero w hw, numbers_zero w hw, fun _ _ hzero _ => hzero⟩

theorem core_mul_suc (w : Prop) (hw : ActualWorld w)
    (a b c d : (σ → Prop) → Prop) (h : CoreMul w a b c) (ha : CoreAdd w a c d) :
    CoreMul w a (coreSuc w b) d :=
  ⟨h.1, numbers_suc w hw b h.2.1, ha.2.2.1,
    fun R hR hzero hstep => hstep b c d h.2.1 h.2.2.1 ha.2.2.1
      (h.2.2.2 R hR hzero hstep) ha⟩

theorem mul_forward (w : Prop) (hw : ActualWorld w)
    (a b c : (σ → Prop) → Prop) (h : MulGraph a b c) :
    CoreMul w (numberMap w a) (numberMap w b) (numberMap w c) := by
  refine ⟨numberMap_forward w hw a h.1, numberMap_forward w hw b h.2.1,
    numberMap_forward w hw c h.2.2.1, ?_⟩
  intro R _ hzero hstep
  apply h.2.2.2 (fun i j => R (numberMap w i) (numberMap w j)) hzero
  intro i j k hi hj hk hij hadd
  rw [numberMap_suc w hw i]
  exact hstep _ _ _ (numberMap_forward w hw i hi) (numberMap_forward w hw j hj)
    (numberMap_forward w hw k hk) hij (add_forward w hw a j k hadd)

theorem mul_reflect (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) (hc : FiniteCardinality c)
    (h : CoreMul w (numberMap w a) (numberMap w b) (numberMap w c)) :
    MulGraph a b c := by
  apply (binary_push_pull w hw hInf (MulGraph a) b c hb hc).1
  apply h.2.2.2 (BinaryPush w (MulGraph a)) (binaryPush_admitted w hw (MulGraph a))
  · exact ⟨numberMap_in_cardinals w hw (ZeroCard σ),
      numberMap_in_cardinals w hw (ZeroCard σ), ZeroCard σ, ZeroCard σ,
      finiteCardinality_zero, finiteCardinality_zero, rfl, rfl, mul_zero a ha⟩
  · intro x y z _ _ hz hxy hadd
    obtain ⟨i, j, hi, hj, hie, hje, hij⟩ := hxy.2.2
    obtain ⟨k, hk, hke⟩ := numberMap_onto w hw z hz
    have haijk : AddGraph a j k := add_reflect w hw hInf a j k ha hj hk
      (hke.symm ▸ (hje.symm ▸ hadd))
    exact ⟨coreSuc_in_cardinals w hw x, hz.1, SucCard i, k,
      finiteCardinality_suc i hi, hk,
      (numberMap_suc w hw i).trans (congrArg (coreSuc w) hie), hke,
      mul_suc a i j k hij haijk⟩

theorem multiplication_iff (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) (hc : FiniteCardinality c) :
    MulGraph a b c ↔ CoreMul w (numberMap w a) (numberMap w b) (numberMap w c) :=
  ⟨mul_forward w hw a b c, mul_reflect w hw hInf a b c ha hb hc⟩

theorem core_mul_total (w : Prop) (hw : ActualWorld w)
    (a b : (σ → Prop) → Prop) (ha : Numbers w a) (hb : Numbers w b) :
    ∃ c, CoreMul w a b c := by
  obtain ⟨i, hi, hie⟩ := numberMap_onto w hw a ha
  obtain ⟨j, hj, hje⟩ := numberMap_onto w hw b hb
  obtain ⟨k, hijk⟩ := mul_total i j hi hj
  exact ⟨numberMap w k, hje ▸ (hie ▸ mul_forward w hw i j k hijk)⟩

theorem core_mul_functional (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c d : (σ → Prop) → Prop) (hc : CoreMul w a b c)
    (hd : CoreMul w a b d) : c = d := by
  obtain ⟨i, hi, hie⟩ := numberMap_onto w hw a hc.1
  obtain ⟨j, hj, hje⟩ := numberMap_onto w hw b hc.2.1
  obtain ⟨k, hk, hke⟩ := numberMap_onto w hw c hc.2.2.1
  obtain ⟨l, hl, hle⟩ := numberMap_onto w hw d hd.2.2.1
  have hsrc : MulGraph i j k := mul_reflect w hw hInf i j k hi hj hk
    (hke.symm ▸ (hje.symm ▸ (hie.symm ▸ hc)))
  have htgt : MulGraph i j l := mul_reflect w hw hInf i j l hi hj hl
    (hle.symm ▸ (hje.symm ▸ (hie.symm ▸ hd)))
  exact hke.symm.trans ((congrArg (numberMap w)
    (mul_functional hInf i j hj k l hsrc htgt)).trans hle)

def LeGraph (a b : (σ → Prop) → Prop) : Prop := ∃ c, AddGraph a c b

def CoreLe (w : Prop) (a b : (σ → Prop) → Prop) : Prop := ∃ c, CoreAdd w a c b

theorem coreLe_admitted (w : Prop) (hw : ActualWorld w) :
    Domain w (BinarySupport (σ := σ) w) (CoreLe w) :=
  ⟨hw.1, le_of_box_incl (nec% (fun (a b : (σ → Prop) → Prop)
    (h : CoreLe w a b) => h.elim fun _ hc => ⟨hc.1.1, hc.2.2.1.1⟩))⟩

theorem order_iff (w : Prop) (hw : ActualWorld w)
    (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) :
    LeGraph a b ↔ CoreLe w (numberMap w a) (numberMap w b) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨numberMap w c, add_forward w hw a c b hc⟩
  · intro h
    obtain ⟨y, hy⟩ := h
    obtain ⟨c, hc, hce⟩ := numberMap_onto w hw y hy.2.1
    exact ⟨c, add_reflect w hw hInf a c b ha hc hb (hce.symm ▸ hy)⟩

end Classicism.Research.ActualityCoreArithmetic
