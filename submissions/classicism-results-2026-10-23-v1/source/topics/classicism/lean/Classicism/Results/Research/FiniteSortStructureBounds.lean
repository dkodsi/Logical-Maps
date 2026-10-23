import Classicism.Results.Research.FiniteSortStructure

/-! Fixed finite C proof candidates. Generated externally; no internal Nat induction.
Source: positive-effective.md §§23.1–23.3 (original research, unpaginated).
The accompanying certificate driver must pass before any C certification claim. -/

namespace Classicism.Research.FiniteSortStructure
open Classicism.Paper Classicism.P

/-- A 1-entry exhaustive cover; entries may repeat. -/
def AtMost1 (σ : Type) [Ty σ] : Prop :=
  ∃ a0 : σ, ∀ z : σ, (z = a0 ∨ False)

theorem atMost1_atomicity {τ : Type} [Rel τ] [Order τ] [Pointwise τ]
    (h : AtMost1 τ) : Atomicity τ := by
  obtain ⟨a0, hall⟩ := h
  intro p
  rcases em (p ≤ ¬ p) with hp | hp
  · exact Or.inl hp
  · have h0 : ∀ z : τ, False → ¬ z ≤ ¬ z → z ≤ p → p ≤ z :=
      fun _ h => h.elim
    obtain ⟨q1, hn1, hle1, h1⟩ :=
      minimum_step (fun z : τ => False) p a0 hp h0
    have hp1 : q1 ≤ p := hle1
    exact Or.inr ⟨q1, atom_of_minimal q1 hn1
      (fun z => h1 z (hall z)), hp1⟩

theorem atMost1_booleanCompleteness {τ : Type} [Rel τ] [Order τ] [Pointwise τ]
    (h : AtMost1 τ) : BooleanCompleteness τ := by
  obtain ⟨a0, hall⟩ := h
  intro X
  have h0 := glb_empty X
  obtain ⟨y1, h1⟩ :=
    glb_step X (fun z : τ => False) a0 (⊤ : τ) h0
  exact ⟨y1, glb_cover X (fun z : τ => (z = a0 ∨ False)) y1 hall h1⟩

theorem atMost1_actuality (h : AtMost1 Prop) : Actuality := by
  obtain ⟨a0, hall⟩ := h
  have h0 : ∀ p : Prop, False → p → (True : Prop) ≤ p := fun _ h => h.elim
  obtain ⟨w1, hw1, h1⟩ :=
    truth_step (fun z : Prop => False) True a0 True.intro h0
  exact ⟨w1, hw1, fun p => h1 p (hall p)⟩

theorem atMost1_relationalChoice {σ τ : Type} [Ty σ] [Ty τ]
    (h : AtMost1 σ) : RelationalChoice σ τ := by
  obtain ⟨a0, hall⟩ := h
  intro U hu
  have h0 := partial_empty U
  obtain ⟨S1, h1⟩ :=
    partial_step (fun z : σ => False) U (fun _ _ => False) a0 hu h0
  exact ⟨S1, partial_cover (fun z : σ => (z = a0 ∨ False)) U S1 hall h1⟩

/-- A 2-entry exhaustive cover; entries may repeat. -/
def AtMost2 (σ : Type) [Ty σ] : Prop :=
  ∃ a0 a1 : σ, ∀ z : σ, (z = a1 ∨ (z = a0 ∨ False))

theorem atMost2_atomicity {τ : Type} [Rel τ] [Order τ] [Pointwise τ]
    (h : AtMost2 τ) : Atomicity τ := by
  obtain ⟨a0, a1, hall⟩ := h
  intro p
  rcases em (p ≤ ¬ p) with hp | hp
  · exact Or.inl hp
  · have h0 : ∀ z : τ, False → ¬ z ≤ ¬ z → z ≤ p → p ≤ z :=
      fun _ h => h.elim
    obtain ⟨q1, hn1, hle1, h1⟩ :=
      minimum_step (fun z : τ => False) p a0 hp h0
    have hp1 : q1 ≤ p := hle1
    obtain ⟨q2, hn2, hle2, h2⟩ :=
      minimum_step (fun z : τ => (z = a0 ∨ False)) q1 a1 hn1 h1
    have hp2 : q2 ≤ p := le_trans_rel q2 q1 p hle2 hp1
    exact Or.inr ⟨q2, atom_of_minimal q2 hn2
      (fun z => h2 z (hall z)), hp2⟩

theorem atMost2_booleanCompleteness {τ : Type} [Rel τ] [Order τ] [Pointwise τ]
    (h : AtMost2 τ) : BooleanCompleteness τ := by
  obtain ⟨a0, a1, hall⟩ := h
  intro X
  have h0 := glb_empty X
  obtain ⟨y1, h1⟩ :=
    glb_step X (fun z : τ => False) a0 (⊤ : τ) h0
  obtain ⟨y2, h2⟩ :=
    glb_step X (fun z : τ => (z = a0 ∨ False)) a1 y1 h1
  exact ⟨y2, glb_cover X (fun z : τ => (z = a1 ∨ (z = a0 ∨ False))) y2 hall h2⟩

theorem atMost2_actuality (h : AtMost2 Prop) : Actuality := by
  obtain ⟨a0, a1, hall⟩ := h
  have h0 : ∀ p : Prop, False → p → (True : Prop) ≤ p := fun _ h => h.elim
  obtain ⟨w1, hw1, h1⟩ :=
    truth_step (fun z : Prop => False) True a0 True.intro h0
  obtain ⟨w2, hw2, h2⟩ :=
    truth_step (fun z : Prop => (z = a0 ∨ False)) w1 a1 hw1 h1
  exact ⟨w2, hw2, fun p => h2 p (hall p)⟩

theorem atMost2_relationalChoice {σ τ : Type} [Ty σ] [Ty τ]
    (h : AtMost2 σ) : RelationalChoice σ τ := by
  obtain ⟨a0, a1, hall⟩ := h
  intro U hu
  have h0 := partial_empty U
  obtain ⟨S1, h1⟩ :=
    partial_step (fun z : σ => False) U (fun _ _ => False) a0 hu h0
  obtain ⟨S2, h2⟩ :=
    partial_step (fun z : σ => (z = a0 ∨ False)) U S1 a1 hu h1
  exact ⟨S2, partial_cover (fun z : σ => (z = a1 ∨ (z = a0 ∨ False))) U S2 hall h2⟩

/-- A 3-entry exhaustive cover; entries may repeat. -/
def AtMost3 (σ : Type) [Ty σ] : Prop :=
  ∃ a0 a1 a2 : σ, ∀ z : σ, (z = a2 ∨ (z = a1 ∨ (z = a0 ∨ False)))

theorem atMost3_atomicity {τ : Type} [Rel τ] [Order τ] [Pointwise τ]
    (h : AtMost3 τ) : Atomicity τ := by
  obtain ⟨a0, a1, a2, hall⟩ := h
  intro p
  rcases em (p ≤ ¬ p) with hp | hp
  · exact Or.inl hp
  · have h0 : ∀ z : τ, False → ¬ z ≤ ¬ z → z ≤ p → p ≤ z :=
      fun _ h => h.elim
    obtain ⟨q1, hn1, hle1, h1⟩ :=
      minimum_step (fun z : τ => False) p a0 hp h0
    have hp1 : q1 ≤ p := hle1
    obtain ⟨q2, hn2, hle2, h2⟩ :=
      minimum_step (fun z : τ => (z = a0 ∨ False)) q1 a1 hn1 h1
    have hp2 : q2 ≤ p := le_trans_rel q2 q1 p hle2 hp1
    obtain ⟨q3, hn3, hle3, h3⟩ :=
      minimum_step (fun z : τ => (z = a1 ∨ (z = a0 ∨ False))) q2 a2 hn2 h2
    have hp3 : q3 ≤ p := le_trans_rel q3 q2 p hle3 hp2
    exact Or.inr ⟨q3, atom_of_minimal q3 hn3
      (fun z => h3 z (hall z)), hp3⟩

theorem atMost3_booleanCompleteness {τ : Type} [Rel τ] [Order τ] [Pointwise τ]
    (h : AtMost3 τ) : BooleanCompleteness τ := by
  obtain ⟨a0, a1, a2, hall⟩ := h
  intro X
  have h0 := glb_empty X
  obtain ⟨y1, h1⟩ :=
    glb_step X (fun z : τ => False) a0 (⊤ : τ) h0
  obtain ⟨y2, h2⟩ :=
    glb_step X (fun z : τ => (z = a0 ∨ False)) a1 y1 h1
  obtain ⟨y3, h3⟩ :=
    glb_step X (fun z : τ => (z = a1 ∨ (z = a0 ∨ False))) a2 y2 h2
  exact ⟨y3, glb_cover X (fun z : τ => (z = a2 ∨ (z = a1 ∨ (z = a0 ∨ False)))) y3 hall h3⟩

theorem atMost3_actuality (h : AtMost3 Prop) : Actuality := by
  obtain ⟨a0, a1, a2, hall⟩ := h
  have h0 : ∀ p : Prop, False → p → (True : Prop) ≤ p := fun _ h => h.elim
  obtain ⟨w1, hw1, h1⟩ :=
    truth_step (fun z : Prop => False) True a0 True.intro h0
  obtain ⟨w2, hw2, h2⟩ :=
    truth_step (fun z : Prop => (z = a0 ∨ False)) w1 a1 hw1 h1
  obtain ⟨w3, hw3, h3⟩ :=
    truth_step (fun z : Prop => (z = a1 ∨ (z = a0 ∨ False))) w2 a2 hw2 h2
  exact ⟨w3, hw3, fun p => h3 p (hall p)⟩

theorem atMost3_relationalChoice {σ τ : Type} [Ty σ] [Ty τ]
    (h : AtMost3 σ) : RelationalChoice σ τ := by
  obtain ⟨a0, a1, a2, hall⟩ := h
  intro U hu
  have h0 := partial_empty U
  obtain ⟨S1, h1⟩ :=
    partial_step (fun z : σ => False) U (fun _ _ => False) a0 hu h0
  obtain ⟨S2, h2⟩ :=
    partial_step (fun z : σ => (z = a0 ∨ False)) U S1 a1 hu h1
  obtain ⟨S3, h3⟩ :=
    partial_step (fun z : σ => (z = a1 ∨ (z = a0 ∨ False))) U S2 a2 hu h2
  exact ⟨S3, partial_cover (fun z : σ => (z = a2 ∨ (z = a1 ∨ (z = a0 ∨ False)))) U S3 hall h3⟩

end Classicism.Research.FiniteSortStructure
