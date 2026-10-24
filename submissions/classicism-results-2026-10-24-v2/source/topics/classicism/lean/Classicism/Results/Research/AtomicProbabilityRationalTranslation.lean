import Classicism.Results.Research.AtomicProbabilityRationalOrder
import Classicism.Results.Research.AtomicProbabilityCutAddition

/-!
# Rational translation and an everywhere guarded addition graph

The graph is empty off the constructed domain. Its associativity is therefore
a theorem for all codes without pretending that invalid codes are numbers.
This is the graph used in the concrete cut-addition construction.
Source: new internal-real bridge formalization, 23 October 2026.
-/

namespace Classicism.Research.ProbabilityRationals
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ProbabilityCuts

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)
local notation "ρ" => (φ → φ → Prop)

def rsub (w : Prop) (R S : ρ) : ρ := rplus w R (rneg w S)
def RationalSumGraph (w : Prop) (R S U : ρ) : Prop :=
  w ∧ RationalField w R ∧ RationalField w S ∧ RationalField w U ∧ rplus w R S = U

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem rsub_in_field (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    RationalField w (rsub w R S) :=
  rplus_in_field w hw hInf R _ hR (rneg_in_field w hw hInf S hS)

include hw hInf in
theorem radd_sub_cancel (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    rsub w (rplus w R S) S = R := by
  change rplus w (rplus w R S) (rneg w S) = R
  rw [rplus_assoc w hw hInf R S _ hR hS (rneg_in_field w hw hInf S hS),
    rplus_neg w hw hInf S hS, rplus_zero_right w hw hInf R hR]

include hw hInf in
theorem rsub_add_cancel (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    rplus w (rsub w R S) S = R := by
  change rplus w (rplus w R (rneg w S)) S = R
  rw [rplus_right_comm w hw hInf R _ S hR (rneg_in_field w hw hInf S hS) hS]
  exact radd_sub_cancel w hw hInf R S hR hS

include hw hInf in
theorem radd_sub_cancel_left (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    rplus w S (rsub w R S) = R := by
  rw [rplus_comm w hw hInf S _ hS (rsub_in_field w hw hInf R S hR hS)]
  exact rsub_add_cancel w hw hInf R S hR hS

include hw hInf in
theorem rlt_add_right (R S U : ρ) (hRS : RLt w R S) (hU : RationalField w U) :
    RLt w (rplus w R U) (rplus w S U) :=
  ⟨rle_add_right w hw hInf R S U hRS.1 hU,
    fun he => hRS.2 (rplus_cancel_right w hw hInf R S U hRS.1.1 hRS.1.2.1 hU he)⟩

include hw hInf in
theorem rlt_add_left (R S U : ρ) (hRS : RLt w R S) (hU : RationalField w U) :
    RLt w (rplus w U R) (rplus w U S) := by
  rw [rplus_comm w hw hInf U R hU hRS.1.1, rplus_comm w hw hInf U S hU hRS.1.2.1]
  exact rlt_add_right w hw hInf R S U hRS hU

include hw hInf in
theorem rlt_add_both (R S U V : ρ) (hRS : RLt w R S) (hUV : RLt w U V) :
    RLt w (rplus w R U) (rplus w S V) :=
  rlt_trans w hw hInf _ _ _ (rlt_add_right w hw hInf R S U hRS hUV.1.1)
    (rlt_add_left w hw hInf U V S hUV hRS.1.2.1)

include hw hInf in
theorem rsub_lt_zero (R S : ρ) (hRS : RLt w R S) : RLt w (rsub w R S) (rzero w) := by
  have h := rlt_add_right w hw hInf R S (rneg w S) hRS
    (rneg_in_field w hw hInf S hRS.1.2.1)
  rw [rplus_neg w hw hInf S hRS.1.2.1] at h
  exact h

include hw hInf in
theorem rationalSumGraph_comm (R S U : ρ) (h : RationalSumGraph w R S U) :
    RationalSumGraph w S R U :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.1,
    (rplus_comm w hw hInf S R h.2.2.1 h.2.1).trans h.2.2.2.2⟩

include hw hInf in
theorem rationalSumGraph_associative : GraphAssociative (RationalSumGraph (σ := σ) w) := by
  intro A B C R
  constructor
  · intro h
    obtain ⟨U, hAB, hUC⟩ := h
    have hBC := rplus_in_field w hw hInf B C hAB.2.2.1 hUC.2.2.1
    refine ⟨rplus w B C, ⟨hw.1, hAB.2.2.1, hUC.2.2.1, hBC, rfl⟩,
      hw.1, hAB.2.1, hBC, hUC.2.2.2.1, ?_⟩
    rw [← rplus_assoc w hw hInf A B C hAB.2.1 hAB.2.2.1 hUC.2.2.1,
      hAB.2.2.2.2, hUC.2.2.2.2]
  · intro h
    obtain ⟨V, hBC, hAV⟩ := h
    have hAB := rplus_in_field w hw hInf A B hAV.2.1 hBC.2.1
    refine ⟨rplus w A B, ⟨hw.1, hAV.2.1, hBC.2.1, hAB, rfl⟩,
      hw.1, hAB, hBC.2.2.1, hAV.2.2.2.1, ?_⟩
    rw [rplus_assoc w hw hInf A B C hAV.2.1 hBC.2.1 hBC.2.2.1,
      hBC.2.2.2.2, hAV.2.2.2.2]

end Classicism.Research.ProbabilityRationals
