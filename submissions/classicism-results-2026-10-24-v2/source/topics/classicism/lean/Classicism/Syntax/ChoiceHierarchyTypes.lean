import Classicism.Syntax.Types

/-!
# Finite type bounds for the Choice hierarchies

Metalogical arithmetic on the library's actual `Ty`/`RTy` codes. This file does
not add type quantification to C and does not prove semantic type embeddings.
The natural-number budget is the explicit syntactic bound from
`research/2026-10-22/followup/finite-functional-choice.md` §§5 and 8–9.
Closed types are the original language; the auxiliary variable case is only
provided to make the recursive functions total on the library's syntax.
-/

namespace Classicism.Meta.ChoiceHierarchy

mutual
  def typeOrder : Ty → Nat
    | .e => 0
    | .rel ρ => relOrder ρ
    | .var _ => 0
  def relOrder : RTy → Nat
    | .t => 0
    | .arr σ ρ => max (typeOrder σ + 1) (relOrder ρ)
end

mutual
  def embeddingBudget : Ty → Nat
    | .e => 0
    | .rel ρ => relEmbeddingBudget ρ
    | .var _ => 0
  def relEmbeddingBudget : RTy → Nat
    | .t => 0
    | .arr σ ρ => max (embeddingBudget σ) (relEmbeddingBudget ρ) + 3
end

/-- `A₀=et`, `Aₙ₊₁=Aₙt`, all admitted relational types. -/
def tower : Nat → RTy
  | 0 => .arr .e .t
  | n + 1 => .arr (.rel (tower n)) .t

theorem tower_closed : ∀ n, (tower n).Closed
  | 0 => ⟨trivial, trivial⟩
  | n + 1 => ⟨tower_closed n, trivial⟩

theorem tower_order : ∀ n, relOrder (tower n) = n + 1
  | 0 => rfl
  | n + 1 => by
    simp only [tower, relOrder, typeOrder, tower_order n, Nat.max_zero]

/-- Domain and codomain orders are bounded by the arrow order. -/
theorem domain_order_le (σ : Ty) (ρ : RTy) :
    typeOrder σ ≤ relOrder (.arr σ ρ) :=
  Nat.le_trans (Nat.le_succ _) (Nat.le_max_left _ _)

theorem codomain_order_le (σ : Ty) (ρ : RTy) :
    relOrder ρ ≤ relOrder (.arr σ ρ) := Nat.le_max_right _ _

def finiteBound (f : Ty → Nat) : List Ty → Nat
  | [] => 0
  | σ :: rest => max (f σ) (finiteBound f rest)

theorem le_finiteBound (f : Ty → Nat) :
    ∀ (types : List Ty) (σ : Ty), σ ∈ types → f σ ≤ finiteBound f types
  | [], _, h => False.elim (List.not_mem_nil h)
  | τ :: rest, σ, h => by
    rcases List.mem_cons.mp h with he | hm
    · subst σ
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_finiteBound f rest σ hm) (Nat.le_max_right _ _)

/-- Finitely many elaborated types admit one order bound. This alone makes no
claim that a particular model preserves the corresponding formula fragment. -/
theorem finite_order_bound (types : List Ty) :
    ∃ n, ∀ σ ∈ types, typeOrder σ ≤ n :=
  ⟨finiteBound typeOrder types, le_finiteBound typeOrder types⟩

/-- The same finite bound for the proposed embedding levels. Existence and
injectivity of those embeddings are separate mathematical obligations. -/
theorem finite_embedding_budget (types : List Ty) :
    ∃ n, ∀ σ ∈ types, embeddingBudget σ ≤ n :=
  ⟨finiteBound embeddingBudget types, le_finiteBound embeddingBudget types⟩

theorem tower_zero : tower 0 = .arr .e .t := rfl
theorem tower_succ (n : Nat) : tower (n + 1) = .arr (.rel (tower n)) .t := rfl

end Classicism.Meta.ChoiceHierarchy
