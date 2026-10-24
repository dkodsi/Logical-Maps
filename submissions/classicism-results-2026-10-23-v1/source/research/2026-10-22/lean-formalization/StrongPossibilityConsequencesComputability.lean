import Mathlib.Computability.RE

/-!
# Concrete diagonal programs underlying the effective lower-bound arguments

ORDINARY COMPUTABILITY METATHEORY; no object-language C conclusion is asserted.
Source: notes/positive-effective.md §§13–17, max-degree.md §§8–10,
strong-possibility-degree.md §§5–6. The diagonal argument is standard; this
implementation uses Mathlib's actual program codes and recursion theorem.

This is not a field assuming that a separator is noncomputable. It constructs
the self-referential program and proves the contradiction. Connecting these
programs to the fixed C arithmetic/finite-trace interpretation, and relativizing
the compiler to uniform oracle programs, are separate unmet obligations.
-/

namespace ClassicismResearch.StrongPossibilityConsequences.Computability

open Nat.Partrec (Code)
open Nat.Partrec.Code

def outputZero (c : Code) : Prop := 0 ∈ eval c 0
def outputOne (c : Code) : Prop := 1 ∈ eval c 0

theorem output_disjoint (c : Code) : ¬ (outputZero c ∧ outputOne c) := by
  rintro ⟨h0, h1⟩
  have h : (0 : Nat) = 1 := Part.mem_unique h0 h1
  exact Nat.zero_ne_one h

/-- The two actual halting-output sets have no computable separator. No
soundness or model-existence hypothesis occurs in this computability theorem. -/
theorem no_computable_separator (S : Code → Prop)
    (h0 : ∀ c, outputZero c → S c)
    (h1 : ∀ c, outputOne c → ¬ S c) : ¬ ComputablePred S := by
  classical
  intro hS
  let g : Code → Nat := fun c => cond (decide (S c)) 1 0
  have hg : Computable g := Computable.cond hS.decide
    (Computable.const 1) (Computable.const 0)
  have hf : Partrec₂ (fun (c : Code) (_ : Nat) => Part.some (g c)) :=
    (hg.comp Computable.fst).partrec
  obtain ⟨c, hc⟩ := fixed_point₂ hf
  have ho : g c ∈ eval c 0 := by
    rw [hc]
    exact Part.mem_some _
  by_cases hs : S c
  · have h : outputOne c := by simpa [g, hs, outputOne] using ho
    exact h1 c h hs
  · have h : outputZero c := by simpa [g, hs, outputZero] using ho
    exact hs (h0 c h)

/-- A total computable prediction of a code's output at zero cannot disagree
with that output on every code. The fixed point supplies a counterexample. -/
theorem computable_prediction_has_fixed_program (g : Code → Nat)
    (hg : Computable g) : ∃ c, g c ∈ eval c 0 := by
  have hf : Partrec₂ (fun (c : Code) (_ : Nat) => Part.some (g c)) :=
    (hg.comp Computable.fst).partrec
  obtain ⟨c, hc⟩ := fixed_point₂ hf
  refine ⟨c, ?_⟩
  rw [hc]
  exact Part.mem_some _

theorem no_computable_diagonal_avoider (g : Code → Nat)
    (havoid : ∀ c, g c ∉ eval c 0) : ¬ Computable g := by
  intro hg
  obtain ⟨c, hc⟩ := computable_prediction_has_fixed_program g hg
  exact havoid c hc

#print axioms no_computable_separator
#print axioms output_disjoint
#print axioms computable_prediction_has_fixed_program
#print axioms no_computable_diagonal_avoider

end ClassicismResearch.StrongPossibilityConsequences.Computability
