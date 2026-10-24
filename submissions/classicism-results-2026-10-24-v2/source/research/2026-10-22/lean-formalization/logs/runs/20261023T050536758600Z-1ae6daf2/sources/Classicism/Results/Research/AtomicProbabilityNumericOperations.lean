import Classicism.Results.Research.ActualityCoreGraphs
import Classicism.Results.Research.ActualityNumericalRelations
import Classicism.Results.Research.AtomicProbabilityNaturalOrder

/-!
# Concrete current numerical operations without Choice or Plenitude

The output number type is relational. The actual-world supported union realizes
the already proved unique CoreAdd/CoreMul graphs. These are actual lambda terms,
not selected operation parameters. All statements are current and retain
Actuality plus quantified Infinity; they do not give a forbidden e-to-e map.

This is the numerical operation resource for signed-fraction coding in the
probability lane. Source: local-propositional-probability.md, internal numerical
and real construction; infinity-core-number-isomorphism.md, section 3.
-/

namespace Classicism.Research.ProbabilityNumericOperations
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ActualityCoreArithmetic
open Classicism.Research.ActualityNumericalRelations

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)

def plus (w : Prop) (a b : ν) : ν :=
  Realize w (Numbers w) (Properties w) (fun x y => CoreAdd w x b y) a

def times (w : Prop) (a b : ν) : ν :=
  Realize w (Numbers w) (Properties w) (fun x y => CoreMul w x b y) a

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem plus_eq (a b c : ν) (h : CoreAdd w a b c) : plus w a b = c :=
  realize_selected w hw (Numbers w) (Properties w) (domain_supported w (BaseTop w))
    (fun x y => CoreAdd w x b y) a c h.1 h.2.2.1.1 h
    (fun d _ hd => core_add_functional w hw hInf a b d c hd h)

include hw hInf in
theorem times_eq (a b c : ν) (h : CoreMul w a b c) : times w a b = c :=
  realize_selected w hw (Numbers w) (Properties w) (domain_supported w (BaseTop w))
    (fun x y => CoreMul w x b y) a c h.1 h.2.2.1.1 h
    (fun d _ hd => core_mul_functional w hw hInf a b d c hd h)

include hw hInf in
theorem plus_graph (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    CoreAdd w a b (plus w a b) := by
  obtain ⟨c, hc⟩ := core_add_total w hw a b ha hb
  exact (plus_eq w hw hInf a b c hc).symm ▸ hc

include hw hInf in
theorem times_graph (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    CoreMul w a b (times w a b) := by
  obtain ⟨c, hc⟩ := core_mul_total w hw a b ha hb
  exact (times_eq w hw hInf a b c hc).symm ▸ hc

include hw hInf in
theorem plus_numbers (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    Numbers w (plus w a b) := (plus_graph w hw hInf a b ha hb).2.2.1

include hw hInf in
theorem times_numbers (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    Numbers w (times w a b) := (times_graph w hw hInf a b ha hb).2.2.1

/-- Ordinary-looking induction is justified by an actual admitted supported predicate. -/
include hw in
theorem number_induction (P : ν → Prop) (hzero : P (coreZero w))
    (hstep : ∀ n, Numbers w n → P n → P (coreSuc w n)) : ∀ n, Numbers w n → P n := by
  intro n hn
  exact (core_number_induction w hw (fun x => Numbers w x ∧ P x)
    ⟨hw.1, le_of_box_incl (nec% (fun (x : ν) (h : Numbers w x ∧ P x) => h.1))⟩
    ⟨numbers_zero w hw, hzero⟩
    (fun x hx hPx => ⟨numbers_suc w hw x hx, hstep x hx hPx.2⟩) n hn).2

include hw in
theorem number_cases (a : ν) (ha : Numbers w a) :
    a = coreZero w ∨ ∃ b, Numbers w b ∧ a = coreSuc w b := by
  obtain ⟨n, hn, hna⟩ := numberMap_onto w hw a ha
  cases ProbabilityNaturalOrder.number_cases n hn with
  | inl hn0 => exact Or.inl (hna.symm.trans (congrArg (numberMap w) hn0))
  | inr hs =>
    obtain ⟨m, hm, hnm⟩ := hs
    exact Or.inr ⟨numberMap w m, numberMap_forward w hw m hm,
      hna.symm.trans ((congrArg (numberMap w) hnm).trans (numberMap_suc w hw m))⟩

include hw hInf in
theorem plus_zero_right (a : ν) (ha : Numbers w a) : plus w a (coreZero w) = a :=
  plus_eq w hw hInf a (coreZero w) a (core_add_zero w hw a ha)

include hw hInf in
theorem plus_suc_right (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    plus w a (coreSuc w b) = coreSuc w (plus w a b) :=
  plus_eq w hw hInf a (coreSuc w b) (coreSuc w (plus w a b))
    (core_add_suc w hw a b (plus w a b) (plus_graph w hw hInf a b ha hb))

include hw hInf in
theorem times_zero_right (a : ν) (ha : Numbers w a) :
    times w a (coreZero w) = coreZero w :=
  times_eq w hw hInf a (coreZero w) (coreZero w) (core_mul_zero w hw a ha)

include hw hInf in
theorem times_suc_right (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    times w a (coreSuc w b) = plus w a (times w a b) :=
  times_eq w hw hInf a (coreSuc w b) (plus w a (times w a b))
    (core_mul_suc w hw a b (times w a b) (plus w a (times w a b))
      (times_graph w hw hInf a b ha hb)
      (plus_graph w hw hInf a (times w a b) ha (times_numbers w hw hInf a b ha hb)))

end Classicism.Research.ProbabilityNumericOperations
