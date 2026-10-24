import Classicism.Results.Research.AtomicProbabilityNaturalOrder

/-!
# Internal least numbers and a canonical least-index graph

Concrete C + quantified Infinity theorems, proved from the actual Frege graphs.
The least-element argument uses internal induction over FiniteCardinality and
C's excluded middle. No external Nat, Choice, assumed well-order, or selecting
operation is used. This supplies the least-index step for positive-mass labels;
real Archimedeanness is still needed to prove that their threshold fields are
nonempty. The output here is a literal single-valued graph at type (σt)t.

Source: choice-free-faithful-probability.md, sections 1-3; the detailed internal
order/least-element proof is part of this formalization, not a cited paper.
-/

namespace Classicism.Research.ProbabilityNaturalOrder
open Classicism.Research.FregeArithmeticGraphs

variable {σ : Type} [Ty σ]

theorem le_suc_self (a : (σ → Prop) → Prop) (ha : FiniteCardinality a) : LE a (SucCard a) :=
  ⟨SucCard (ZeroCard σ), add_suc a (ZeroCard σ) a (add_zero a ha)⟩

theorem le_eq_or_lt (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b : (σ → Prop) → Prop) (h : LE a b) : a = b ∨ LT a b := by
  obtain ⟨c, hc⟩ := h
  cases number_cases c hc.2.1 with
  | inl hc0 => exact Or.inl (add_at_zero a b (hc0 ▸ hc)).symm
  | inr hs =>
    obtain ⟨d, hd, hcd⟩ := hs
    obtain ⟨v, hv, hav, hb⟩ := add_at_suc hInf a d b hd (hcd ▸ hc)
    exact Or.inr ⟨d, hb.symm ▸ add_suc_left a d v hav⟩

theorem lt_implies_le (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (h : LT a b) : LE a b := le_trans a (SucCard a) b (le_suc_self a ha) h

theorem lt_irrefl (hInf : Classicism.P.AxiomOfInfinity σ)
    (a : (σ → Prop) → Prop) (ha : FiniteCardinality a) : ¬ LT a a :=
  not_suc_le_self hInf a ha

theorem le_suc_cases (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a) (hb : FiniteCardinality b)
    (h : LE a (SucCard b)) : LE a b ∨ a = SucCard b := by
  cases le_total a b ha hb with
  | inl hab => exact Or.inl hab
  | inr hba =>
    cases le_eq_or_lt hInf b a hba with
    | inl hbe =>
      subst a
      exact Or.inl (le_refl b hb)
    | inr hlt => exact Or.inr
        (le_antisymm hInf a ha (SucCard b) (finiteCardinality_suc b hb) h hlt)

def LeastNumber (P : ((σ → Prop) → Prop) → Prop) (n : (σ → Prop) → Prop) : Prop :=
  FiniteCardinality n ∧ P n ∧ ∀ m, FiniteCardinality m → P m → LE n m

theorem bounded_field_has_least (hInf : Classicism.P.AxiomOfInfinity σ)
    (b : (σ → Prop) → Prop) (hb : FiniteCardinality b) :
    ∀ P : ((σ → Prop) → Prop) → Prop,
      (∃ m, FiniteCardinality m ∧ P m ∧ LE m b) → ∃ n, LeastNumber P n := by
  refine (hb (fun i => FiniteCardinality i ∧
    ∀ P : ((σ → Prop) → Prop) → Prop,
      (∃ m, FiniteCardinality m ∧ P m ∧ LE m i) → ∃ n, LeastNumber P n)
    ⟨?_, ?_⟩).2
  · refine ⟨finiteCardinality_zero, ?_⟩
    intro P hP
    obtain ⟨m, hm, hPm, hm0⟩ := hP
    have he := le_zero m hm0
    exact ⟨ZeroCard σ, finiteCardinality_zero, he ▸ hPm, fun n hn _ => zero_le n hn⟩
  · intro i hi
    refine ⟨finiteCardinality_suc i hi.1, ?_⟩
    intro P hP
    cases em (∃ m, FiniteCardinality m ∧ P m ∧ LE m i) with
    | inl hsmall => exact hi.2 P hsmall
    | inr hsmall =>
      obtain ⟨m, hm, hPm, hms⟩ := hP
      have hPs : P (SucCard i) := by
        cases le_suc_cases hInf m i hm hi.1 hms with
        | inl hmi => exact False.elim (hsmall ⟨m, hm, hPm, hmi⟩)
        | inr hme => exact hme ▸ hPm
      refine ⟨SucCard i, finiteCardinality_suc i hi.1, hPs, ?_⟩
      intro n hn hPn
      cases le_total (SucCard i) n (finiteCardinality_suc i hi.1) hn with
      | inl hsn => exact hsn
      | inr hns =>
        cases le_suc_cases hInf n i hn hi.1 hns with
        | inl hni => exact False.elim (hsmall ⟨n, hn, hPn, hni⟩)
        | inr hne => exact hne.symm ▸ le_refl (SucCard i) (finiteCardinality_suc i hi.1)

theorem represented_field_has_least (hInf : Classicism.P.AxiomOfInfinity σ)
    (P : ((σ → Prop) → Prop) → Prop)
    (hP : ∃ n, FiniteCardinality n ∧ P n) : ∃ n, LeastNumber P n := by
  obtain ⟨b, hb, hPb⟩ := hP
  exact bounded_field_has_least hInf b hb P ⟨b, hb, hPb, le_refl b hb⟩

theorem leastNumber_unique (hInf : Classicism.P.AxiomOfInfinity σ)
    (P : ((σ → Prop) → Prop) → Prop) (m n : (σ → Prop) → Prop)
    (hm : LeastNumber P m) (hn : LeastNumber P n) : m = n :=
  le_antisymm hInf m hm.1 n hn.1 (hm.2.2 n hn.1 hn.2.1) (hn.2.2 m hm.1 hm.2.1)

def LeastIndex {α : Type} [Ty α] (D : α → Prop)
    (R : α → ((σ → Prop) → Prop) → Prop) : α → ((σ → Prop) → Prop) → Prop :=
  fun a n => D a ∧ LeastNumber (R a) n

theorem least_index_graph {α : Type} [Ty α]
    (hInf : Classicism.P.AxiomOfInfinity σ) (D : α → Prop)
    (R : α → ((σ → Prop) → Prop) → Prop)
    (h : ∀ a, D a → ∃ n, FiniteCardinality n ∧ R a n) :
    ∀ a, D a → ∃ n, LeastIndex D R a n ∧
      ∀ m, LeastIndex D R a m → n = m := by
  intro a ha
  obtain ⟨n, hn⟩ := represented_field_has_least hInf (R a) (h a ha)
  exact ⟨n, ⟨ha, hn⟩, fun m hm => leastNumber_unique hInf (R a) n m hn hm.2⟩

end Classicism.Research.ProbabilityNaturalOrder
