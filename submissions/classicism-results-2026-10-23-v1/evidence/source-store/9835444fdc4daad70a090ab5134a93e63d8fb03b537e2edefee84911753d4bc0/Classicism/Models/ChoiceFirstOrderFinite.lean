import Classicism.Models.ChoiceFirstOrderTerms

/-!
# Finite free-variable support of the first-order interpretation

Original formalization (misc), 23 October 2026, of the finite-formula boundary
in `research/2026-10-23/finite-choice-forcing-extraction-review.md` sections
2--4 (unpaginated). The formula language permits a general family of variable
names for convenient capture-free translation, but each formula depends on
an explicitly computed finite list of those names. Thus its comprehension
scheme does not silently admit a predicate with infinitely many parameters.

This is not yet an encoding into Mathlib's countable first-order language or
a ground-model extraction theorem. Those require further construction.
-/

namespace Classicism.Meta.ChoiceFirstOrder

def argsVariables {V : Ty → Type} : ∀ ρ, Args V ρ → List (Sigma V)
  | .t, _ => []
  | .arr σ ρ, a => ⟨σ, a.1⟩ :: argsVariables ρ a.2

def freeVariable {V : Ty → Type} {ρ : RTy} : Sigma (Extend V ρ) → Option (Sigma V)
  | ⟨σ, .inl v⟩ => some ⟨σ, v⟩
  | ⟨_, .inr _⟩ => none

/-- A concrete finite list, with repetitions harmless, of all free variable names. -/
def Formula.variables : {V : Ty → Type} → Formula V → List (Sigma V)
  | _, .equal (σ := σ) x y => [⟨σ, x⟩, ⟨σ, y⟩]
  | _, .rel ρ x a => ⟨.rel ρ, x⟩ :: argsVariables ρ a
  | _, .falsum => []
  | _, .neg p => p.variables
  | _, .conj p q => p.variables ++ q.variables
  | _, .disj p q => p.variables ++ q.variables
  | _, .all _ p => p.variables.filterMap freeVariable
  | _, .ex _ p => p.variables.filterMap freeVariable

theorem mapArgs_eq_of_agree {V D : Ty → Type}
    (η θ : ∀ σ, V σ → D σ) : ∀ ρ (a : Args V ρ),
    (∀ σ v, (⟨σ, v⟩ : Sigma V) ∈ argsVariables ρ a → η σ v = θ σ v) →
    mapArgs η ρ a = mapArgs θ ρ a
  | .t, _, _ => rfl
  | .arr σ ρ, a, h => by
    change (η σ a.1, mapArgs η ρ a.2) = (θ σ a.1, mapArgs θ ρ a.2)
    rw [h σ a.1 List.mem_cons_self]
    rw [mapArgs_eq_of_agree η θ ρ a.2
      (fun τ v hv => h τ v (List.mem_cons_of_mem _ hv))]

private theorem extend_agree {V D : Ty → Type} {ρ : RTy}
    (L : List (Sigma (Extend V ρ))) (η θ : ∀ σ, V σ → D σ)
    (h : ∀ σ v, (⟨σ, v⟩ : Sigma V) ∈ L.filterMap freeVariable → η σ v = θ σ v)
    (a : Args D ρ) :
    ∀ σ v, (⟨σ, v⟩ : Sigma (Extend V ρ)) ∈ L →
      extendEnv η ρ a σ v = extendEnv θ ρ a σ v := by
  intro σ v hv
  cases v with
  | inl v =>
    exact h σ v (List.mem_filterMap.mpr ⟨⟨σ, Sum.inl v⟩, hv, rfl⟩)
  | inr v => rfl

/-- Formula truth depends only on the displayed finite list, including under
quantification over arbitrarily large domains. -/
theorem Formula.realize_agree (S : Structure) :
    ∀ {V : Ty → Type} (φ : Formula V) (η θ : ∀ σ, V σ → S.D σ),
      (∀ σ v, (⟨σ, v⟩ : Sigma V) ∈ φ.variables → η σ v = θ σ v) →
      (φ.Realize S η ↔ φ.Realize S θ)
  | _, .equal (σ := σ) x y, η, θ, h => by
    change η σ x = η σ y ↔ θ σ x = θ σ y
    rw [h σ x List.mem_cons_self,
      h σ y (List.mem_cons_of_mem _ List.mem_cons_self)]
  | _, .rel ρ x a, η, θ, h => by
    change S.rel ρ (η _ x) (mapArgs η ρ a) ↔ S.rel ρ (θ _ x) (mapArgs θ ρ a)
    rw [h _ x List.mem_cons_self]
    rw [mapArgs_eq_of_agree η θ ρ a
      (fun σ v hv => h σ v (List.mem_cons_of_mem _ hv))]
  | _, .falsum, _, _, _ => Iff.rfl
  | _, .neg p, η, θ, h => not_congr (realize_agree S p η θ h)
  | _, .conj p q, η, θ, h =>
    and_congr
      (realize_agree S p η θ (fun σ v hv => h σ v (List.mem_append.mpr (Or.inl hv))))
      (realize_agree S q η θ (fun σ v hv => h σ v (List.mem_append.mpr (Or.inr hv))))
  | _, .disj p q, η, θ, h =>
    or_congr
      (realize_agree S p η θ (fun σ v hv => h σ v (List.mem_append.mpr (Or.inl hv))))
      (realize_agree S q η θ (fun σ v hv => h σ v (List.mem_append.mpr (Or.inr hv))))
  | _, .all ρ p, η, θ, h => by
    change (∀ a : Args S.D ρ, _) ↔ ∀ a : Args S.D ρ, _
    exact forall_congr' (fun a => realize_agree S p (extendEnv η ρ a)
      (extendEnv θ ρ a) (extend_agree p.variables η θ h a))
  | _, .ex ρ p, η, θ, h => by
    change (∃ a : Args S.D ρ, _) ↔ ∃ a : Args S.D ρ, _
    exact exists_congr (fun a => realize_agree S p (extendEnv η ρ a)
      (extendEnv θ ρ a) (extend_agree p.variables η θ h a))

/-- The actual sentence translation has no external parameter names. -/
theorem sentenceTranslation_no_free_variables (p : Sentence Signature.pure) :
    (sentenceTranslation p).variables = [] := by
  cases h : (sentenceTranslation p).variables with
  | nil => rfl
  | cons v rest => exact nomatch v.2

end Classicism.Meta.ChoiceFirstOrder
