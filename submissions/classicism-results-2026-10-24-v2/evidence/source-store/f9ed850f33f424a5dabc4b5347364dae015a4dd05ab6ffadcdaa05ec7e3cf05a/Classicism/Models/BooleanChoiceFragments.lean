import Classicism.Models.BooleanChoiceCutoff
import Classicism.Results.ChoiceHierarchySchemas

/-!
# Finite bounds for actual Functional Choice schema fragments

Original supporting formalization (misc), 23 October 2026, of section 7
of `research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
Membership in the actual project schema supplies the input/output types,
their closedness, and equality with the quoted sentence. List induction
and maxima then bound the output ranks for a finite fragment. The same
witnesses give the concrete recursive protection condition at that cutoff.

These are syntactic finite-bound lemmas. No separating model, semantic
agreement, or finite-fragment gap is assumed or asserted here.
-/

namespace Classicism.Meta.ChoiceBoolean.ChoiceFragments

open ChoiceCutoff ProtectedCoverage

private theorem boundInstances (q : Ty → RTy → Sentence Signature.pure)
    (L : List (Sentence Signature.pure)) :
    (∀ p ∈ L, ∃ σ : Ty, ∃ ρ : RTy, σ.Closed ∧ ρ.Closed ∧ p = q σ ρ) →
    ∃ m : Nat, ∀ p ∈ L, ∃ σ : Ty, ∃ ρ : RTy,
      σ.Closed ∧ ρ.Closed ∧ p = q σ ρ ∧ rankTy (.rel ρ) ≤ m := by
  induction L with
  | nil =>
      intro _
      refine ⟨0, ?_⟩
      intro p hp
      cases hp
  | cons p L ih =>
      intro hL
      obtain ⟨σ, ρ, hσ, hρ, hp⟩ := hL p (List.mem_cons_self ..)
      obtain ⟨m, hm⟩ := ih (fun r hr => hL r (List.mem_cons_of_mem p hr))
      refine ⟨max (rankTy (.rel ρ)) m, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with he | ht
      · subst r
        exact ⟨σ, ρ, hσ, hρ, hp, Nat.le_max_left _ _⟩
      · obtain ⟨τ, ν, hτ, hν, he, hn⟩ := hm r ht
        exact ⟨τ, ν, hτ, hν, he, hn.trans (Nat.le_max_right _ _)⟩

/-- Every sentence in a finite boxed Choice fragment retains its actual
closed-type representation, with one common bound on output rank. -/
theorem finite_boxed_bound (L : List (Sentence Signature.pure))
    (hL : ∀ p ∈ L, P.NecFunctionalChoice.schema p) :
    ∃ m : Nat, ∀ p ∈ L, ∃ σ : Ty, ∃ ρ : RTy,
      σ.Closed ∧ ρ.Closed ∧ p = P.NecFunctionalChoice.quoted σ ρ ∧
        rankTy (.rel ρ) ≤ m :=
  boundInstances P.NecFunctionalChoice.quoted L hL

/-- The analogous statement for the actual unboxed Choice schema. -/
theorem finite_unboxed_bound (L : List (Sentence Signature.pure))
    (hL : ∀ p ∈ L, P.FunctionalChoice.schema p) :
    ∃ m : Nat, ∀ p ∈ L, ∃ σ : Ty, ∃ ρ : RTy,
      σ.Closed ∧ ρ.Closed ∧ p = P.FunctionalChoice.quoted σ ρ ∧
        rankTy (.rel ρ) ≤ m :=
  boundInstances P.FunctionalChoice.quoted L hL

/-- The finite boxed fragment's outputs are protected at the actual
regular successor cutoff, using the proved rank-to-protection theorem. -/
theorem finite_boxed_protected (L : List (Sentence Signature.pure))
    (hL : ∀ p ∈ L, P.NecFunctionalChoice.schema p) :
    ∃ m : Nat, ∀ p ∈ L, ∃ σ : Ty, ∃ ρ : RTy,
      σ.Closed ∧ ρ.Closed ∧ p = P.NecFunctionalChoice.quoted σ ρ ∧
        Protected (cutoff m) Nat (.rel ρ) := by
  obtain ⟨m, hm⟩ := finite_boxed_bound L hL
  refine ⟨m, ?_⟩
  intro p hp
  obtain ⟨σ, ρ, hσ, hρ, he, hr⟩ := hm p hp
  exact ⟨σ, ρ, hσ, hρ, he, protected_of_rank m (.rel ρ) hr⟩

theorem finite_unboxed_protected (L : List (Sentence Signature.pure))
    (hL : ∀ p ∈ L, P.FunctionalChoice.schema p) :
    ∃ m : Nat, ∀ p ∈ L, ∃ σ : Ty, ∃ ρ : RTy,
      σ.Closed ∧ ρ.Closed ∧ p = P.FunctionalChoice.quoted σ ρ ∧
        Protected (cutoff m) Nat (.rel ρ) := by
  obtain ⟨m, hm⟩ := finite_unboxed_bound L hL
  refine ⟨m, ?_⟩
  intro p hp
  obtain ⟨σ, ρ, hσ, hρ, he, hr⟩ := hm p hp
  exact ⟨σ, ρ, hσ, hρ, he, protected_of_rank m (.rel ρ) hr⟩

end Classicism.Meta.ChoiceBoolean.ChoiceFragments
