import Mathlib.Order.Heyting.Regular
import Mathlib.Order.UpperLower.CompleteLattice

/-!
# A concrete Boolean completion of a condition preorder

Original formalization (misc), 23 October 2026. The construction is the
regular-element completion of the frame of downward-closed sets. It is a
concrete complete Boolean algebra, not an assumed forcing or model-existence
principle. Principal lower sets give a dense family of nonzero elements,
and their Boolean compatibility is exactly existence of a common stronger
condition. Cardinal closure, column actions, and the typed model are separate
obligations. Source: this file, unpaginated, and the construction in
`research/2026-10-23/boolean-valued-finite-choice.md` section 2.
-/

namespace Classicism.Meta.ChoiceBoolean.ConditionCompletion

universe u

/-- The existing Boolean algebra of regular elements also has all suprema
and infima, obtained from its concrete Galois insertion into the frame. -/
noncomputable instance regularCompleteBooleanAlgebra (A : Type u) [Order.Frame A] :
    CompleteBooleanAlgebra (Heyting.Regular A) :=
  let complete := Heyting.Regular.gi.liftCompleteLattice (α := A)
  { (inferInstance : BooleanAlgebra (Heyting.Regular A)) with
    sSup := @sSup _ complete.toSupSet
    sInf := @sInf _ complete.toInfSet
    isLUB_sSup := complete.isLUB_sSup
    isGLB_sInf := complete.isGLB_sInf }

variable (P : Type u) [Preorder P]

abbrev Algebra := Heyting.Regular (LowerSet P)

def principal (p : P) : LowerSet P :=
  ⟨Set.Iic p, fun _ _ h hp => le_trans h hp⟩

@[simp] theorem mem_principal (p q : P) : q ∈ principal P p ↔ q ≤ p := Iff.rfl

def cone (p : P) : Algebra P := Heyting.Regular.toRegular (principal P p)

theorem principal_le_of_mem (p : P) (a : LowerSet P) (hp : p ∈ a) :
    principal P p ≤ a := by
  intro q hq
  exact a.lower hq hp

theorem regularize_eq_bot (a : LowerSet P) :
    Heyting.Regular.toRegular a = (⊥ : Algebra P) ↔ a = ⊥ := by
  constructor
  · intro h
    have hc := congrArg (fun b : Algebra P => (b : LowerSet P)) h
    have ha : a ≤ (⊥ : LowerSet P) := by
      simpa only [Heyting.Regular.coe_toRegular, Heyting.Regular.coe_bot] using
        (le_compl_compl (a := a)).trans_eq hc
    exact bot_unique ha
  · intro h
    subst a
    apply Heyting.Regular.coe_injective
    simp

theorem regularize_inf (a b : LowerSet P) :
    Heyting.Regular.toRegular (a ⊓ b) =
      (Heyting.Regular.toRegular a ⊓ Heyting.Regular.toRegular b : Algebra P) := by
  apply Heyting.Regular.coe_injective
  simp only [Heyting.Regular.coe_toRegular, Heyting.Regular.coe_inf,
    compl_compl_inf_distrib]

theorem cone_ne_bot (p : P) : cone P p ≠ ⊥ := by
  intro h
  have hp : principal P p = ⊥ := (regularize_eq_bot P _).mp h
  have hm : p ∈ principal P p := le_rfl
  rw [hp] at hm
  exact hm

noncomputable instance algebraNontrivial [Nonempty P] : Nontrivial (Algebra P) :=
  ⟨⟨cone P (Classical.choice ‹Nonempty P›), ⊥, cone_ne_bot P _⟩⟩

theorem cone_mono {p q : P} (h : p ≤ q) : cone P p ≤ cone P q := by
  apply Heyting.Regular.toRegular.monotone
  intro r hr
  exact le_trans hr h

/-- Every nonzero Boolean value contains the regularized principal lower
set of an actual condition. -/
theorem dense_cone (b : Algebra P) (hb : b ≠ ⊥) :
    ∃ p : P, cone P p ≤ b := by
  have hval : (b : LowerSet P) ≠ ⊥ := by
    intro h
    apply hb
    apply Heyting.Regular.coe_injective
    exact h
  obtain ⟨p, hp⟩ := LowerSet.coe_nonempty.mpr hval
  refine ⟨p, ?_⟩
  exact (Heyting.Regular.gi.gc _ b).2 (principal_le_of_mem P p _ hp)

/-- The completion retains the precise common-extension relation. The
condition order is stronger-below-weaker. -/
theorem cone_compatible_iff (p q : P) :
    cone P p ⊓ cone P q ≠ ⊥ ↔ ∃ r : P, r ≤ p ∧ r ≤ q := by
  rw [cone, cone, ← regularize_inf P, ne_eq, regularize_eq_bot P]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := LowerSet.coe_nonempty.mpr h
    exact ⟨r, hr⟩
  · rintro ⟨r, hp, hq⟩ h
    have hr : r ∈ principal P p ⊓ principal P q := ⟨hp, hq⟩
    rw [h] at hr
    exact hr

end Classicism.Meta.ChoiceBoolean.ConditionCompletion
