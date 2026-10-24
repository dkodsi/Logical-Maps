import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Heyting.Regular
import Mathlib.Order.UpperLower.Principal

/-!
# Complete Boolean regularization and the completion of a poset

This is external metatheory. The complete Boolean algebra is constructed, not
assumed: start with a complete Heyting algebra, retain Mathlib's Boolean algebra
of its regular elements, and supply arbitrary bounds through the regularization
Galois insertion. For a preorder P, regular lower sets then give its Boolean
completion. The principal regularizations are nonzero and dense, and their
compatibility is precisely compatibility in P. Separativity makes the map order
reflecting. Incompatible refinements make the completion atomless.

Direct source: the original algebraic construction here (misc, 22 October 2026,
unpaginated), using Mathlib's `Heyting.Regular.gi` and
`GaloisInsertion.liftCompleteLattice`. The intended application is the Boolean
completion B of the tree forcing P in Jech--Shelah, Journal of Algebra 182
(1996), pp. 748--755, especially pp. 749--750 and 752--754.

No tree forcing, rigidity, constructibility, pure definition, or C-nontheorem is
postulated or established here. The final atomlessness result has the explicit
poset splitting premise; a concrete forcing must still satisfy that premise.
Source preparation is not a successful Lean check. The designated serial
checker owns compilation and the final axiom reports.
-/

namespace Classicism.Meta.Research.MaxAtomicityRegularCompletion

universe u v

set_option backward.isDefEq.respectTransparency false

section Regularization

variable {H : Type u} [Order.Frame H]

/-- Arbitrary joins and meets on regular elements, with exactly Mathlib's
existing Boolean operations. Completeness is derived from the Galois insertion. -/
instance regularCompleteBooleanAlgebra : CompleteBooleanAlgebra (Heyting.Regular H) where
  __ := (inferInstance : BooleanAlgebra (Heyting.Regular H))
  sSup := (Heyting.Regular.gi (α := H)).liftCompleteLattice.sSup
  sInf := (Heyting.Regular.gi (α := H)).liftCompleteLattice.sInf
  isLUB_sSup := (Heyting.Regular.gi (α := H)).liftCompleteLattice.isLUB_sSup
  isGLB_sInf := (Heyting.Regular.gi (α := H)).liftCompleteLattice.isGLB_sInf

/-- Regularization is left adjoint to the underlying-element map. -/
theorem regularize_le_iff (a : H) (b : Heyting.Regular H) :
    Heyting.Regular.toRegular a ≤ b ↔ a ≤ (b : H) :=
  Heyting.Regular.gi.gc a b

/-- Regularization does not annihilate a nonzero element. -/
theorem regularize_eq_bot_iff (a : H) :
    Heyting.Regular.toRegular a = ⊥ ↔ a = ⊥ := by
  constructor
  · intro h
    apply le_bot_iff.mp
    have ha : a ≤ (Heyting.Regular.toRegular a : H) := le_compl_compl
    rw [h, Heyting.Regular.coe_bot] at ha
    exact ha
  · rintro rfl
    apply Heyting.Regular.coe_injective
    simp only [Heyting.Regular.coe_toRegular, compl_bot, compl_top,
      Heyting.Regular.coe_bot]

/-- Double negation preserves finite meets. -/
theorem regularize_inf (a b : H) :
    Heyting.Regular.toRegular (a ⊓ b) =
      Heyting.Regular.toRegular a ⊓ Heyting.Regular.toRegular b := by
  apply Heyting.Regular.coe_injective
  change (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ
  exact compl_compl_inf_distrib a b

end Regularization

section PosetCompletion

variable (P : Type u) [Preorder P]

/-- The regular lower sets, equivalently the regular opens for the lower-set
Alexandrov topology. No separativity hypothesis is needed for this algebra. -/
abbrev Completion := Heyting.Regular (LowerSet P)

/-- Send a condition to the regularization of its principal lower set. -/
def condition (p : P) : Completion P :=
  Heyting.Regular.toRegular (LowerSet.Iic p)

variable {P}

/-- Every condition has nonzero Boolean value, including on a nonseparative poset. -/
theorem condition_ne_bot (p : P) : condition P p ≠ ⊥ := by
  intro h
  have hz : LowerSet.Iic p = ⊥ :=
    (regularize_eq_bot_iff (LowerSet.Iic p)).mp h
  exact LowerSet.Iic_ne_bot hz

/-- Strengthening a condition decreases its Boolean value. -/
theorem condition_mono {p q : P} (h : p ≤ q) : condition P p ≤ condition P q := by
  apply Heyting.Regular.toRegular.monotone
  intro r hr
  exact le_trans hr h

/-- A regular lower set contains the Boolean value of every condition it contains. -/
theorem condition_le_of_mem {b : Completion P} {p : P}
    (hp : p ∈ (b : LowerSet P)) : condition P p ≤ b := by
  exact (regularize_le_iff (LowerSet.Iic p) b).2 (LowerSet.Iic_le.mpr hp)

/-- The principal regularizations are order dense in the nonzero completion. -/
theorem condition_dense {b : Completion P} (hb : b ≠ ⊥) :
    ∃ p : P, condition P p ≤ b := by
  classical
  have hmem : ∃ p : P, p ∈ (b : LowerSet P) := by
    by_contra h
    apply hb
    apply Heyting.Regular.coe_injective
    apply LowerSet.ext
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact h ⟨p, hp⟩
  obtain ⟨p, hp⟩ := hmem
  exact ⟨p, condition_le_of_mem hp⟩

/-- Two conditions have nonzero Boolean meet exactly when they have a common
strengthening. This gives the forcing compatibility relation without assuming
that the original order was separative. -/
theorem condition_inf_ne_bot_iff (p q : P) :
    condition P p ⊓ condition P q ≠ ⊥ ↔ ∃ r : P, r ≤ p ∧ r ≤ q := by
  change Heyting.Regular.toRegular (LowerSet.Iic p) ⊓
    Heyting.Regular.toRegular (LowerSet.Iic q) ≠ ⊥ ↔ _
  rw [← regularize_inf, ne_eq, regularize_eq_bot_iff]
  constructor
  · intro h
    classical
    by_contra hn
    apply h
    apply LowerSet.ext
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    exact hn ⟨r, hr.1, hr.2⟩
  · rintro ⟨r, hrp, hrq⟩ h
    have hr : r ∈ LowerSet.Iic p ⊓ LowerSet.Iic q := ⟨hrp, hrq⟩
    rw [h] at hr
    exact hr

/-- Explicit separativity: failure of p ≤ q can be witnessed below p by a
condition incompatible with q. -/
def Separative (P : Type u) [Preorder P] : Prop :=
  ∀ p q : P, ¬ p ≤ q → ∃ r : P, r ≤ p ∧ ¬ ∃ s : P, s ≤ r ∧ s ≤ q

/-- On a separative poset the completion map reflects the original order. -/
theorem condition_le_iff (sep : Separative P) (p q : P) :
    condition P p ≤ condition P q ↔ p ≤ q := by
  constructor
  · intro hpq
    classical
    by_contra hn
    obtain ⟨r, hrp, hrq⟩ := sep p q hn
    apply hrq
    apply (condition_inf_ne_bot_iff r q).mp
    rw [inf_eq_left.mpr ((condition_mono hrp).trans hpq)]
    exact condition_ne_bot r
  · exact condition_mono

/-- The concrete condition needed to make a Boolean completion atomless. -/
def Splitting (P : Type u) [Preorder P] : Prop :=
  ∀ p : P, ∃ q r : P, q ≤ p ∧ r ≤ p ∧ ¬ ∃ s : P, s ≤ q ∧ s ≤ r

/-- Incompatible refinements below each condition provide a proper nonzero
Boolean part below every nonzero element of the completion. -/
theorem completion_atomless (splits : Splitting P) {b : Completion P} (hb : b ≠ ⊥) :
    ∃ c : Completion P, c ≠ ⊥ ∧ c ≤ b ∧ c ≠ b := by
  obtain ⟨p, hp⟩ := condition_dense hb
  obtain ⟨q, r, hqp, hrp, hqr⟩ := splits p
  refine ⟨condition P q, condition_ne_bot q, (condition_mono hqp).trans hp, ?_⟩
  intro hqb
  have hrq : condition P r ≤ condition P q := by
    rw [hqb]
    exact (condition_mono hrp).trans hp
  apply hqr
  apply (condition_inf_ne_bot_iff q r).mp
  rw [inf_eq_right.mpr hrq]
  exact condition_ne_bot r

end PosetCompletion

#print axioms regularCompleteBooleanAlgebra
#print axioms regularize_eq_bot_iff
#print axioms condition_ne_bot
#print axioms condition_dense
#print axioms condition_inf_ne_bot_iff
#print axioms condition_le_iff
#print axioms completion_atomless

end Classicism.Meta.Research.MaxAtomicityRegularCompletion
