import Classicism.Results.Research.InfinitaryComprehensionSupport

/-!
# The cardinal obstruction as an actual Comprehension instance

Direct source: `research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md`, section 5, misc, 23 October 2026, unpaginated.

This is the diagonal obstruction used after constructing a small Henkin
hierarchy. It does not assume an omitted support. Given an enumeration of
all admitted individual predicates by individuals, it constructs a concrete
infinitary matrix whose Comprehension instance fails. The elementary-hull
existence and small-syntax closure needed by the bounded-cardinal theorem
are separate obligations, not conclusions of this lemma.
-/

namespace Classicism.Research.InfinitaryComprehension.Henkin
open Classicism.Meta

universe u
variable (M : Model.{u})

/-- The names in this matrix receive ordinary simultaneous assignments.
There is no model predicate or truth predicate in the object formula. -/
def diagonalMatrix (w : M.World) (enumerate : M.Dom .e → M.Dom (Ty.e ⇒ RTy.t)) :
    Formula M.Dom [Ty.e] :=
  .iOr {a : M.Dom .e // ¬ M.truth (M.app (enumerate a) a) w}
    (fun a => .eq (.var .zero) (.param a.val))

theorem eval_diagonalMatrix (w : M.World)
    (enumerate : M.Dom .e → M.Dom (Ty.e ⇒ RTy.t)) (a : M.Dom .e) (v : M.World) :
    M.truth (eval M (selfAssignment M) (diagonalMatrix M w enumerate)
      (Env.cons a Env.nil)) v ↔ ¬ M.truth (M.app (enumerate a) a) w := by
  change M.truth (M.iOr {b : M.Dom .e // ¬ M.truth (M.app (enumerate b) b) w}
    (fun b => M.eq a b.val)) v ↔ _
  rw [M.iOr_spec]
  constructor
  · rintro ⟨b, hb⟩
    have hab : a = b.val := (M.eq_spec _ _ v).1 hb
    exact hab.symm ▸ b.property
  · intro ha
    exact ⟨⟨a, ha⟩, (M.eq_spec _ _ v).2 rfl⟩

/-- Cantor diagonalization refutes the displayed formula, not just an
informal fullness property. No Faithful or WorldSeparated premise is needed. -/
theorem diagonal_comprehension_fails (w : M.World)
    (enumerate : M.Dom .e → M.Dom (Ty.e ⇒ RTy.t))
    (surj : ∀ R, ∃ a, enumerate a = R) :
    ¬ M.truth (eval M (selfAssignment M)
      (diagonalMatrix M w enumerate).comprehension Env.nil) w := by
  intro h
  obtain ⟨R, hR⟩ := (eval_comprehension_iff M (selfAssignment M)
    (diagonalMatrix M w enumerate) w).1 h
  obtain ⟨a, ha⟩ := surj R
  have hd := (hR (Env.cons a Env.nil) w).trans
    (eval_diagonalMatrix M w enumerate a w)
  change M.truth (M.app R a) w ↔ ¬ M.truth (M.app (enumerate a) a) w at hd
  rw [ha] at hd
  have hn : ¬ M.truth (M.app R a) w := fun hp => (hd.1 hp) hp
  exact hn (hd.2 hn)

theorem no_comprehension_of_predicate_enumeration (w : M.World)
    (enumerate : M.Dom .e → M.Dom (Ty.e ⇒ RTy.t))
    (surj : ∀ R, ∃ a, enumerate a = R) : ¬ Comp M w := by
  intro hc
  exact diagonal_comprehension_fails M w enumerate surj
    (hc M.Dom (selfAssignment M) [Ty.e] (diagonalMatrix M w enumerate))

#print axioms eval_diagonalMatrix
#print axioms diagonal_comprehension_fails
#print axioms no_comprehension_of_predicate_enumeration

end Classicism.Research.InfinitaryComprehension.Henkin
