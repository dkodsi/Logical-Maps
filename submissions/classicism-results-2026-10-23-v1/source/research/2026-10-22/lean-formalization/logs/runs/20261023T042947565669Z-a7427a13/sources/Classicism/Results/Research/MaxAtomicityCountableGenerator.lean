import Classicism.Results.Research.MaxAtomicityWellOrder
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Nat.Find

/-!
# A splitter from a countable complete generating family

External algebraic metatheory. For a fixed b, the elements a for which b ≤ a or
b ≤ aᶜ form a complete Boolean subalgebra. Consequently, in an atomless complete
Boolean algebra a complete generating family must include an element splitting
every nonzero b. A countable family therefore supplies a selector by its least
splitting index. No well-order of the Boolean algebra is needed.

The source of this argument is the present original proof (misc, 22 October
2026, unpaginated). Its proposed application is the countable branch-cylinder
family of the forcing in Jech--Shelah, Journal of Algebra 182 (1996), pp. 749--750.
This module does not prove that that specific family completely generates, that
the forcing completion is rigid, or that the family is purely definable in C.
The input `CompletelyGenerates` is the usual closure definition of complete
generation, not a splitting or selector assumption.

Source preparation is not a successful Lean check. Compilation and final axiom
reports belong to the designated serial checker.
-/

namespace Classicism.Meta.Research.MaxAtomicityCountableGenerator

open MaxAtomicityWellOrder

universe u v

variable {B : Type u} [CompleteBooleanAlgebra B]

/-- The two pieces of b cut out by a are both nonzero. -/
def Splits (b a : B) : Prop := b ⊓ a ≠ ⊥ ∧ b ⊓ aᶜ ≠ ⊥

/-- An element decides b uniformly: it contains b or is disjoint from b. -/
def NonSplit (b a : B) : Prop := b ≤ a ∨ b ≤ aᶜ

/-- A complete Boolean subalgebra described by its carrier and closure laws. -/
def CompleteClosed (S : Set B) : Prop :=
  (⊥ : B) ∈ S ∧ (∀ a ∈ S, aᶜ ∈ S) ∧
    ∀ X : Set B, X ⊆ S → sSup X ∈ S

/-- Every complete Boolean subalgebra containing the family is the whole algebra. -/
def CompletelyGenerates {I : Type v} (g : I → B) : Prop :=
  ∀ S : Set B, CompleteClosed S → (∀ i : I, g i ∈ S) → ∀ a : B, a ∈ S

theorem nonSplit_bot (b : B) : NonSplit b ⊥ := by
  right
  rw [compl_bot]
  exact le_top

theorem nonSplit_compl {b a : B} (h : NonSplit b a) : NonSplit b aᶜ := by
  rcases h with h | h
  · right
    simpa only [compl_compl] using h
  · exact Or.inl h

/-- The arbitrary-join step uses completeness, not complete distributivity. -/
theorem nonSplit_sSup {b : B} {X : Set B} (h : ∀ a ∈ X, NonSplit b a) :
    NonSplit b (sSup X) := by
  classical
  by_cases hex : ∃ a ∈ X, b ≤ a
  · obtain ⟨a, ha, hba⟩ := hex
    exact Or.inl (hba.trans (le_sSup ha))
  · right
    rw [compl_sSup]
    apply le_iInf
    intro a
    apply le_iInf
    intro ha
    rcases h a ha with hba | hba
    · exact (hex ⟨a, ha, hba⟩).elim
    · exact hba

/-- The same carrier is also closed under arbitrary meets. -/
theorem nonSplit_iInf {I : Sort v} {b : B} {f : I → B}
    (h : ∀ i : I, NonSplit b (f i)) : NonSplit b (⨅ i, f i) := by
  classical
  by_cases hall : ∀ i : I, b ≤ f i
  · exact Or.inl (le_iInf hall)
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    right
    rcases h i with hbi | hbi
    · exact (hi hbi).elim
    · exact hbi.trans (compl_le_compl (iInf_le f i))

/-- This is an actual complete subalgebra, established from Boolean laws. -/
theorem nonSplit_completeClosed (b : B) : CompleteClosed {a : B | NonSplit b a} := by
  refine ⟨nonSplit_bot b, ?_, ?_⟩
  · intro a ha
    exact nonSplit_compl ha
  · intro X hX
    exact nonSplit_sSup (fun a ha => hX ha)

theorem not_nonSplit_iff_splits (b a : B) : ¬ NonSplit b a ↔ Splits b a := by
  constructor
  · intro h
    constructor
    · intro hz
      apply h
      right
      calc
        b = (b ⊓ a) ⊔ (b ⊓ aᶜ) := (sup_inf_inf_compl (x := b) (y := a)).symm
        _ = b ⊓ aᶜ := by rw [hz, bot_sup_eq]
        _ ≤ aᶜ := inf_le_right
    · intro hz
      apply h
      left
      calc
        b = (b ⊓ a) ⊔ (b ⊓ aᶜ) := (sup_inf_inf_compl (x := b) (y := a)).symm
        _ = b ⊓ a := by rw [hz, sup_bot_eq]
        _ ≤ a := inf_le_right
  · rintro ⟨ha, hna⟩ (h | h)
    · apply hna
      apply le_bot_iff.mp
      calc
        b ⊓ aᶜ ≤ a ⊓ aᶜ := inf_le_inf_right _ h
        _ = ⊥ := inf_compl_eq_bot
    · apply ha
      apply le_bot_iff.mp
      calc
        b ⊓ a ≤ aᶜ ⊓ a := inf_le_inf_right _ h
        _ = ⊥ := compl_inf_eq_bot

/-- Complete generation forces a splitting generator; this is stronger than
merely selecting from the full Boolean algebra. -/
theorem exists_generator_splits {I : Type v} (g : I → B)
    (gen : CompletelyGenerates g) (atomless : AtomlessParts B)
    {b : B} (hb : b ≠ ⊥) : ∃ i : I, Splits b (g i) := by
  classical
  by_contra hn
  have hg : ∀ i : I, NonSplit b (g i) := by
    intro i
    by_contra hi
    exact hn ⟨i, (not_nonSplit_iff_splits b (g i)).mp hi⟩
  have hall := gen {a : B | NonSplit b a} (nonSplit_completeClosed b) hg
  obtain ⟨a, ha⟩ := atomless b hb
  exact ((not_nonSplit_iff_splits b a).mpr (properPart_splits ha)) (hall a)

/-- The selected natural number is constructed with Nat.find. -/
noncomputable def leastIndex (g : ℕ → B) (gen : CompletelyGenerates g)
    (atomless : AtomlessParts B) (b : B) (hb : b ≠ ⊥) : ℕ := by
  classical
  exact Nat.find (exists_generator_splits g gen atomless hb)

theorem leastIndex_spec (g : ℕ → B) (gen : CompletelyGenerates g)
    (atomless : AtomlessParts B) (b : B) (hb : b ≠ ⊥) :
    Splits b (g (leastIndex g gen atomless b hb)) := by
  classical
  exact Nat.find_spec (exists_generator_splits g gen atomless hb)

theorem leastIndex_min (g : ℕ → B) (gen : CompletelyGenerates g)
    (atomless : AtomlessParts B) (b : B) (hb : b ≠ ⊥)
    {m : ℕ} (hm : m < leastIndex g gen atomless b hb) : ¬ Splits b (g m) := by
  classical
  exact Nat.find_min (exists_generator_splits g gen atomless hb) hm

/-- A concrete total splitter, bottom at bottom and the least splitting generator
elsewhere. Its definition uses no well-order of B. -/
noncomputable def splitter (g : ℕ → B) (gen : CompletelyGenerates g)
    (atomless : AtomlessParts B) (b : B) : B := by
  classical
  exact if hb : b = ⊥ then ⊥ else g (leastIndex g gen atomless b hb)

theorem splitter_splits (g : ℕ → B) (gen : CompletelyGenerates g)
    (atomless : AtomlessParts B) {b : B} (hb : b ≠ ⊥) :
    b ⊓ splitter g gen atomless b ≠ ⊥ ∧
      b ⊓ (splitter g gen atomless b)ᶜ ≠ ⊥ := by
  classical
  simpa only [splitter, dif_neg hb] using leastIndex_spec g gen atomless b hb

#print axioms nonSplit_completeClosed
#print axioms nonSplit_iInf
#print axioms exists_generator_splits
#print axioms leastIndex_spec
#print axioms leastIndex_min
#print axioms splitter_splits

end Classicism.Meta.Research.MaxAtomicityCountableGenerator
