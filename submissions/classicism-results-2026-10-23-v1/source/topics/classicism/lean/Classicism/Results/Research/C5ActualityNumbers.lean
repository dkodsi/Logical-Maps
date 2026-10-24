import Classicism.Results.Research.C5Frege
import Classicism.Results.Research.ActualityNumericalRelations

/-!
# The actual-world number comparison under C5, including finite bases

Direct sources: research/2026-10-22/notes/frege-infinity-20261022-1726.md
§20.2–§20.4 and proof-refinements/infinity-core-number-isomorphism.md §3;
unpaginated original research, misc.

C5 null collapse replaces the earlier actual-Infinity premise in the concrete
Actuality number-map injection and graph reflection proofs. The underlying map,
source and target number predicates, arithmetic graphs and image predicates are
the existing definitions. Both finite and infinite internal numerical fields are
covered. The inverse is a graph; no choosing operation is inserted.
-/
namespace Classicism.Research.C5ActualityNumbers
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ActualityCoreArithmetic
open Classicism.Research.FregeArithmeticGraphs

variable {σ : Type} [Ty σ]

theorem numberMap_injective_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (n m : (σ → Prop) → Prop)
    (hn : FiniteCardinality n) (hm : FiniteCardinality m)
    (he : numberMap w n = numberMap w m) : n = m := by
  apply C5Frege.numerical_extensionality c5 n m hn hm
  intro X
  obtain ⟨Y, hY, hXY⟩ := properties_cover w hw X
  have heY : n Y ↔ m Y :=
    ⟨fun h => (Eq.mp (congrFun he Y) (show numberMap w n Y from ⟨hY, h⟩)).2,
     fun h => (Eq.mpr (congrFun he Y) (show numberMap w m Y from ⟨hY, h⟩)).2⟩
  exact ⟨fun h => finiteCardinality_coext m hm Y X
      (heY.1 (finiteCardinality_coext n hn X Y h hXY)) (fun x => (hXY x).symm),
    fun h => finiteCardinality_coext n hn Y X
      (heY.2 (finiteCardinality_coext m hm X Y h hXY)) (fun x => (hXY x).symm)⟩

theorem numberMap_identity_iff_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (n m : (σ → Prop) → Prop)
    (hn : FiniteCardinality n) (hm : FiniteCardinality m) :
    numberMap w n = numberMap w m ↔ n = m :=
  ⟨numberMap_injective_c5 c5 w hw n m hn hm, congrArg (numberMap w)⟩

theorem numberMap_successor_iff_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (n m : (σ → Prop) → Prop)
    (hn : FiniteCardinality n) (hm : FiniteCardinality m) :
    numberMap w n = coreSuc w (numberMap w m) ↔ n = SucCard m :=
  ⟨fun he => numberMap_injective_c5 c5 w hw n (SucCard m) hn
      (finiteCardinality_suc m hm) (he.trans (numberMap_suc w hw m).symm),
   fun he => (congrArg (numberMap w) he).trans (numberMap_suc w hw m)⟩

theorem numberMap_inverse_graph_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (y : (σ → Prop) → Prop) (hy : Numbers w y) :
    ∃ n, NumberInverse (Numbers w) (numberMap w) y n ∧
      ∀ m, NumberInverse (Numbers w) (numberMap w) y m → m = n := by
  obtain ⟨n, hn, he⟩ := numberMap_onto w hw y hy
  exact ⟨n, ⟨hy, hn, he⟩, fun m hm => numberMap_injective_c5 c5 w hw m n
    hm.2.1 hn (hm.2.2.trans he.symm)⟩

theorem subset_push_pull_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (V : ((σ → Prop) → Prop) → Prop)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    SubsetPush w V (numberMap w n) ↔ V n := by
  constructor
  · intro h
    obtain ⟨m, hm, he, hV⟩ := h.2
    exact numberMap_injective_c5 c5 w hw m n hm hn he ▸ hV
  · intro h
    exact ⟨numberMap_in_cardinals w hw n, n, hn, rfl, h⟩

theorem binary_push_pull_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w)
    (R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)
    (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a) (hb : FiniteCardinality b) :
    BinaryPush w R (numberMap w a) (numberMap w b) ↔ R a b := by
  constructor
  · intro h
    obtain ⟨i, j, hi, hj, hie, hje, hij⟩ := h.2.2
    have hei := numberMap_injective_c5 c5 w hw i a hi ha hie
    have hej := numberMap_injective_c5 c5 w hw j b hj hb hje
    exact hej ▸ (hei ▸ hij)
  · intro h
    exact ⟨numberMap_in_cardinals w hw a, numberMap_in_cardinals w hw b,
      a, b, ha, hb, rfl, rfl, h⟩

theorem add_reflect_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (a b c : (σ → Prop) → Prop)
    (ha : FiniteCardinality a) (hb : FiniteCardinality b) (hc : FiniteCardinality c)
    (h : CoreAdd w (numberMap w a) (numberMap w b) (numberMap w c)) :
    AddGraph a b c := by
  apply (binary_push_pull_c5 c5 w hw (AddGraph a) b c hb hc).1
  apply h.2.2.2 (BinaryPush w (AddGraph a)) (binaryPush_admitted w hw (AddGraph a))
  · exact ⟨numberMap_in_cardinals w hw (ZeroCard σ), numberMap_in_cardinals w hw a,
      ZeroCard σ, a, finiteCardinality_zero, ha, rfl, rfl, add_zero a ha⟩
  · intro x y _ _ hxy
    obtain ⟨i, j, hi, hj, hie, hje, hij⟩ := hxy.2.2
    exact ⟨coreSuc_in_cardinals w hw x, coreSuc_in_cardinals w hw y,
      SucCard i, SucCard j, finiteCardinality_suc i hi, finiteCardinality_suc j hj,
      (numberMap_suc w hw i).trans (congrArg (coreSuc w) hie),
      (numberMap_suc w hw j).trans (congrArg (coreSuc w) hje), add_suc a i j hij⟩

theorem addition_iff_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (a b c : (σ → Prop) → Prop)
    (ha : FiniteCardinality a) (hb : FiniteCardinality b) (hc : FiniteCardinality c) :
    AddGraph a b c ↔ CoreAdd w (numberMap w a) (numberMap w b) (numberMap w c) :=
  ⟨add_forward w hw a b c, add_reflect_c5 c5 w hw a b c ha hb hc⟩

theorem mul_reflect_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (a b c : (σ → Prop) → Prop)
    (ha : FiniteCardinality a) (hb : FiniteCardinality b) (hc : FiniteCardinality c)
    (h : CoreMul w (numberMap w a) (numberMap w b) (numberMap w c)) :
    MulGraph a b c := by
  apply (binary_push_pull_c5 c5 w hw (MulGraph a) b c hb hc).1
  apply h.2.2.2 (BinaryPush w (MulGraph a)) (binaryPush_admitted w hw (MulGraph a))
  · exact ⟨numberMap_in_cardinals w hw (ZeroCard σ),
      numberMap_in_cardinals w hw (ZeroCard σ), ZeroCard σ, ZeroCard σ,
      finiteCardinality_zero, finiteCardinality_zero, rfl, rfl, mul_zero a ha⟩
  · intro x y z _ _ hz hxy hadd
    obtain ⟨i, j, hi, hj, hie, hje, hij⟩ := hxy.2.2
    obtain ⟨k, hk, hke⟩ := numberMap_onto w hw z hz
    have haijk := add_reflect_c5 c5 w hw a j k ha hj hk
      (hke.symm ▸ (hje.symm ▸ hadd))
    exact ⟨coreSuc_in_cardinals w hw x, hz.1, SucCard i, k,
      finiteCardinality_suc i hi, hk,
      (numberMap_suc w hw i).trans (congrArg (coreSuc w) hie), hke,
      mul_suc a i j k hij haijk⟩

theorem multiplication_iff_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (a b c : (σ → Prop) → Prop)
    (ha : FiniteCardinality a) (hb : FiniteCardinality b) (hc : FiniteCardinality c) :
    MulGraph a b c ↔ CoreMul w (numberMap w a) (numberMap w b) (numberMap w c) :=
  ⟨mul_forward w hw a b c, mul_reflect_c5 c5 w hw a b c ha hb hc⟩

theorem order_iff_c5
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (w : Prop) (hw : ActualWorld w) (a b : (σ → Prop) → Prop)
    (ha : FiniteCardinality a) (hb : FiniteCardinality b) :
    LeGraph a b ↔ CoreLe w (numberMap w a) (numberMap w b) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨numberMap w c, add_forward w hw a c b hc⟩
  · intro h
    obtain ⟨y, hy⟩ := h
    obtain ⟨c, hc, hce⟩ := numberMap_onto w hw y hy.2.1
    exact ⟨c, add_reflect_c5 c5 w hw a c b ha hc hb (hce.symm ▸ hy)⟩

end Classicism.Research.C5ActualityNumbers
