import Classicism.Models.BooleanProtectedCoverage
import Classicism.Syntax.ChoiceHierarchyTypes
import Mathlib.Data.Finset.Lattice.Fold

/-!
# A regular cutoff for finitely many ground types

Original supporting formalization (misc), 23 October 2026, of section 7
of `research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
The ground individual domain is Nat. Concrete rank bounds put every
ground type below a finite beth number. Taking its successor protects
any prescribed finite collection and the next predicate tower, while
that next tower admits an external injection of the cutoff cardinal.

All bounds concern the actual `ChoiceFirstOrder.Full` domains/tuples;
protection is the recursive cardinal condition of ProtectedCoverage.
No cardinal-size, coverage, injection, or separating verdict is assumed.
-/

namespace Classicism.Meta.ChoiceBoolean.ChoiceCutoff

open ProtectedCoverage

noncomputable section

/-- The finite beth sequence, starting with the cardinality of Nat. -/
def finiteBeth : Nat → Cardinal
  | 0 => Cardinal.aleph0
  | n + 1 => 2 ^ finiteBeth n

theorem finiteBeth_mono : Monotone finiteBeth :=
  monotone_nat_of_le_succ (fun n => (Cardinal.cantor (finiteBeth n)).le)

theorem aleph0_le_finiteBeth : ∀ n, Cardinal.aleph0 ≤ finiteBeth n
  | 0 => le_rfl
  | n + 1 => (aleph0_le_finiteBeth n).trans (Cardinal.cantor (finiteBeth n)).le

/-- Identification with Mathlib's ordinal-indexed beth function. -/
theorem finiteBeth_eq_beth : ∀ n, finiteBeth n = Cardinal.beth (n : Ordinal)
  | 0 => Cardinal.beth_zero.symm
  | n + 1 => by
      change 2 ^ finiteBeth n = Cardinal.beth ((n + 1 : Nat) : Ordinal)
      rw [finiteBeth_eq_beth n, Nat.cast_add, Nat.cast_one, Cardinal.beth_add_one]

mutual
  def rankTy : Ty → Nat
    | .e => 0
    | .rel ρ => rankArgs ρ + 1
    | .var _ => 0

  def rankArgs : RTy → Nat
    | .t => 0
    | .arr σ ρ => max (rankTy σ) (rankArgs ρ)
end

mutual
  theorem ground_dom_bound : ∀ σ,
      Cardinal.mk (ChoiceFirstOrder.Full.Dom Nat σ) ≤ finiteBeth (rankTy σ)
    | .e => Cardinal.mk_nat.le
    | .var _ => Cardinal.mk_nat.le
    | .rel ρ => by
        change Cardinal.mk (Set (ChoiceFirstOrder.Full.Tuple Nat ρ)) ≤
          2 ^ finiteBeth (rankArgs ρ)
        rw [Cardinal.mk_set]
        exact Cardinal.power_le_power_left (by simp) (ground_tuple_bound ρ)

  theorem ground_tuple_bound : ∀ ρ,
      Cardinal.mk (ChoiceFirstOrder.Full.Tuple Nat ρ) ≤ finiteBeth (rankArgs ρ)
    | .t => by
        change Cardinal.mk PUnit ≤ Cardinal.aleph0
        rw [Cardinal.mk_punit]
        exact Cardinal.one_lt_aleph0.le
    | .arr σ ρ => by
        change Cardinal.mk (ChoiceFirstOrder.Full.Dom Nat σ ×
          ChoiceFirstOrder.Full.Tuple Nat ρ) ≤ finiteBeth (max (rankTy σ) (rankArgs ρ))
        rw [Cardinal.mk_prod]
        simp only [Cardinal.lift_id]
        exact (mul_le_mul'
          ((ground_dom_bound σ).trans (finiteBeth_mono (Nat.le_max_left _ _)))
          ((ground_tuple_bound ρ).trans (finiteBeth_mono (Nat.le_max_right _ _)))).trans_eq
            (Cardinal.mul_eq_self (aleph0_le_finiteBeth _))
end

/-- The regular cardinal used for a fragment of rank at most m. -/
def cutoff (m : Nat) : Cardinal := Order.succ (finiteBeth m)

theorem cutoff_regular (m : Nat) : (cutoff m).IsRegular :=
  Cardinal.isRegular_succ (aleph0_le_finiteBeth m)

theorem finiteBeth_lt_cutoff (m : Nat) : finiteBeth m < cutoff m := Order.lt_succ _

theorem small_args_of_rank (m : Nat) (ρ : RTy) (hρ : rankArgs ρ ≤ m) :
    Cardinal.mk (ChoiceFirstOrder.Full.Tuple Nat ρ) < cutoff m :=
  ((ground_tuple_bound ρ).trans (finiteBeth_mono hρ)).trans_lt (finiteBeth_lt_cutoff m)

mutual
  theorem protected_of_rank (m : Nat) :
      ∀ σ, rankTy σ ≤ m → Protected (cutoff m) Nat σ
    | .e, _ => trivial
    | .var _, _ => trivial
    | .rel ρ, h =>
        ⟨protectedArgs_of_rank m ρ (Nat.le_of_succ_le h),
          small_args_of_rank m ρ (Nat.le_of_succ_le h)⟩

  theorem protectedArgs_of_rank (m : Nat) :
      ∀ ρ, rankArgs ρ ≤ m → ProtectedArgs (cutoff m) Nat ρ
    | .t, _ => trivial
    | .arr σ ρ, h =>
        ⟨protected_of_rank m σ ((Nat.le_max_left _ _).trans h),
          protectedArgs_of_rank m ρ ((Nat.le_max_right _ _).trans h)⟩
end

/-- A relational type needs small arguments, not a small output domain. -/
theorem rel_protected_of_args_rank (m : Nat) (ρ : RTy) (hρ : rankArgs ρ ≤ m) :
    Protected (cutoff m) Nat (.rel ρ) :=
  ⟨protectedArgs_of_rank m ρ hρ, small_args_of_rank m ρ hρ⟩

/-- Exact cardinality of the existing tower A₀=et, Aₙ₊₁=Aₙt. -/
theorem ground_tower_card : ∀ n,
    Cardinal.mk (ChoiceFirstOrder.Full.Dom Nat (.rel (ChoiceHierarchy.tower n))) =
      finiteBeth (n + 1)
  | 0 => by
      change Cardinal.mk (Set (Nat × PUnit)) = 2 ^ Cardinal.aleph0
      rw [Cardinal.mk_set]
      simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_nat,
        Cardinal.mk_punit, mul_one]
  | n + 1 => by
      change Cardinal.mk (Set (ChoiceFirstOrder.Full.Dom Nat
        (.rel (ChoiceHierarchy.tower n)) × PUnit)) = 2 ^ finiteBeth (n + 1)
      rw [Cardinal.mk_set]
      simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_punit,
        mul_one, ground_tower_card n]

theorem ground_tower_args_card : ∀ n,
    Cardinal.mk (ChoiceFirstOrder.Full.Tuple Nat (ChoiceHierarchy.tower n)) = finiteBeth n
  | 0 => by
      change Cardinal.mk (Nat × PUnit) = Cardinal.aleph0
      simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_nat,
        Cardinal.mk_punit, mul_one]
  | n + 1 => by
      change Cardinal.mk (ChoiceFirstOrder.Full.Dom Nat
        (.rel (ChoiceHierarchy.tower n)) × PUnit) = finiteBeth (n + 1)
      simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_punit,
        mul_one, ground_tower_card n]

theorem tower_args_rank : ∀ n, rankArgs (ChoiceHierarchy.tower n) = n
  | 0 => rfl
  | n + 1 => by
      simp only [ChoiceHierarchy.tower, rankArgs, rankTy, tower_args_rank n, Nat.max_zero]

/-- The next tower is covered even though its full ground domain is
already at least the cutoff cardinal. -/
theorem tower_protected (m : Nat) :
    Protected (cutoff m) Nat (.rel (ChoiceHierarchy.tower m)) :=
  rel_protected_of_args_rank m _ (tower_args_rank m).le

theorem cutoff_le_tower_card (m : Nat) :
    cutoff m ≤ Cardinal.mk (ChoiceFirstOrder.Full.Dom Nat (.rel (ChoiceHierarchy.tower m))) := by
  rw [ground_tower_card]
  exact Order.succ_le_of_lt (Cardinal.cantor (finiteBeth m))

theorem ground_injection_exists (m : Nat) :
    Nonempty ((cutoff m).out ↪ ChoiceFirstOrder.Full.Dom Nat (.rel (ChoiceHierarchy.tower m))) := by
  apply Cardinal.lift_mk_le'.mp
  rw [Cardinal.mk_out, ground_tower_card]
  simp only [cutoff, finiteBeth_eq_beth, Cardinal.lift_succ,
    Cardinal.lift_beth, Ordinal.lift_natCast]
  rw [Nat.cast_add, Nat.cast_one, Cardinal.beth_add_one]
  exact Order.succ_le_of_lt (Cardinal.cantor _)

/-- An actual external injection used to index the later higher family. -/
def groundInjection (m : Nat) :
    (cutoff m).out ↪ ChoiceFirstOrder.Full.Dom Nat (.rel (ChoiceHierarchy.tower m)) :=
  Classical.choice (ground_injection_exists m)

def finiteRank (Ω : Finset Ty) : Nat := Ω.sup rankTy

theorem finite_protected (Ω : Finset Ty) :
    ∀ σ ∈ Ω, Protected (cutoff (finiteRank Ω)) Nat σ := by
  intro σ hσ
  exact protected_of_rank _ σ (Finset.le_sup hσ)

/-- Every finite set of type requirements has a concrete regular cutoff,
protecting it and a larger closed relational tower with a ground injection. -/
theorem exists_regular_cutoff (Ω : Finset Ty) :
    ∃ κ : Cardinal, κ.IsRegular ∧
      (∀ σ ∈ Ω, Protected κ Nat σ) ∧
      ∃ ν : RTy, ν.Closed ∧ Protected κ Nat (.rel ν) ∧
        Nonempty (κ.out ↪ ChoiceFirstOrder.Full.Dom Nat (.rel ν)) :=
  ⟨cutoff (finiteRank Ω), cutoff_regular _, finite_protected Ω,
    ChoiceHierarchy.tower (finiteRank Ω), ChoiceHierarchy.tower_closed _,
    tower_protected _, ground_injection_exists _⟩

end

end Classicism.Meta.ChoiceBoolean.ChoiceCutoff
