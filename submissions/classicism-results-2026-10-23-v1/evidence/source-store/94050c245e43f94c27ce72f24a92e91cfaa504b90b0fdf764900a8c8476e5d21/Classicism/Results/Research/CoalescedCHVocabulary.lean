import Classicism.Results.Research.AnalyticStructures

/-!
# Structural CH in the relational language

Source: `non-contingency-of-ch`, Background "Analysis", and Andrew Bacon,
Could the truths of mathematics have been different?, 9 October 2025 draft,
section 5, pp. 21–22. The relational real-structure vocabulary is the existing
`Analytic.Real`, with its source attribution and nonempty completeness convention.

This transcription and the normalization proofs are by Codex (OpenAI), prompted
by Daniel Kodsi, 23 October 2026. Quantification over subproperties and graphs is
internal object-language quantification. No external powerset or choice is used.
-/

namespace Classicism.Research.CoalescedCH

variable {σ : Type} [Ty σ]

/-- A graph supported on `Y × Z`, total and functional on `Y`, and injective. -/
def Injection (Y Z : σ → Prop) (G : σ → σ → Prop) : Prop :=
  (∀ x y, G x y → Y x ∧ Z y) ∧
  (∀ x, Y x → ∃ y, G x y) ∧
  (∀ x y z, G x y → G x z → y = z) ∧
  (∀ x y z, G x z → G y z → x = y)

/-- A relational injection whose range is the entire target subproperty. -/
def Bijection (Y Z : σ → Prop) (G : σ → σ → Prop) : Prop :=
  Injection Y Z G ∧ ∀ y, Z y → ∃ x, G x y

/-- Every internal subproperty of the continuum injects into its naturals or is
in bijection with the continuum. The empty subproperty is included. -/
def StructuralCH (X N : σ → Prop) : Prop :=
  ∀ Y : σ → Prop, (∀ x, Y x → X x) →
    (∃ G : σ → σ → Prop, Injection Y N G) ∨
    (∃ G : σ → σ → Prop, Bijection Y X G)

def HasRealCH (σ : Type) [Ty σ] : Prop :=
  ∃ (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (zero one : σ) (N : σ → Prop),
      Analytic.Real X le add mul zero one N ∧ StructuralCH X N

def HasRealNotCH (σ : Type) [Ty σ] : Prop :=
  ∃ (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (zero one : σ) (N : σ → Prop),
      Analytic.Real X le add mul zero one N ∧ ¬ StructuralCH X N

def AllRealCH (σ : Type) [Ty σ] : Prop :=
  ∀ (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (zero one : σ) (N : σ → Prop),
      Analytic.Real X le add mul zero one N → StructuralCH X N

def AllRealNotCH (σ : Type) [Ty σ] : Prop :=
  ∀ (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (zero one : σ) (N : σ → Prop),
      Analytic.Real X le add mul zero one N → ¬ StructuralCH X N

/-- The exact source formulation: boxes are outside all seven object binders. -/
def NonContingency (σ : Type) [Ty σ] : Prop :=
  □ (AllRealCH σ) ∨ □ (AllRealNotCH σ)

theorem no_counterexample_eq (σ : Type) [Ty σ] :
    (¬ HasRealNotCH σ) = AllRealCH σ := by
  apply propext
  constructor
  · intro h X le add mul zero one N hR
    exact (em (StructuralCH X N)).elim id
      (fun hn => (h ⟨X, le, add, mul, zero, one, N, hR, hn⟩).elim)
  · intro h hex
    obtain ⟨X, le, add, mul, zero, one, N, hR, hn⟩ := hex
    exact hn (h X le add mul zero one N hR)

theorem no_example_eq (σ : Type) [Ty σ] :
    (¬ HasRealCH σ) = AllRealNotCH σ := by
  apply propext
  constructor
  · intro h X le add mul zero one N hR hc
    exact h ⟨X, le, add, mul, zero, one, N, hR, hc⟩
  · intro h hex
    obtain ⟨X, le, add, mul, zero, one, N, hR, hc⟩ := hex
    exact h X le add mul zero one N hR hc

/-- A closed C identity, so replacing the formulas inside the boxes is licensed. -/
theorem normal_form (σ : Type) [Ty σ] :
    NonContingency σ = (□ (¬ HasRealNotCH σ) ∨ □ (¬ HasRealCH σ)) := by
  unfold NonContingency
  rw [← no_counterexample_eq σ, ← no_example_eq σ]

end Classicism.Research.CoalescedCH
