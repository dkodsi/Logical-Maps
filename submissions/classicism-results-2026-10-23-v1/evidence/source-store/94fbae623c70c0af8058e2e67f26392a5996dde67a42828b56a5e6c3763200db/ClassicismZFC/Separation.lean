import ClassicismZFC.SetLaws

/-!
# Finite-formula Separation from the actual collection scheme

First, collection of the constant value `a` over the inhabited `P(empty)`
constructs a singleton of `a`. For a finite formula `φ(p,x)`, the explicit
finite formula `∀ z, z ∈ y ↔ z = x ∧ φ(p,x)` then associates to each `x`
its singleton when `φ` holds, and the empty set otherwise. Collection of
these sets and their union gives Separation.

Only a syntactic `L.BoundedFormula Empty (n+1)` and a finite parameter tuple
are accepted. No arbitrary external predicate is assumed definable.
-/

open FirstOrder FirstOrder.Language
open Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.Separation

open SetLaws

universe u

variable {M : Type u} [L.Structure M]

/-- The finite formula `y = a`, with levels `a=0, x=1, y=2`. -/
def constantImageFormula : L.BoundedFormula Empty 3 :=
  Term.bdEqual (Term.var (Sum.inr ⟨2, by omega⟩))
    (Term.var (Sum.inr ⟨0, by omega⟩))

theorem realize_constantImageFormula (a x y : M) :
    constantImageFormula.Realize default (Fin.snoc (Fin.snoc ![a] x) y) ↔ y = a := by
  simp [constantImageFormula, Fin.snoc]

/-- An actual internal singleton, obtained from finite-formula Collection. -/
theorem singleton (hZFC : M ⊨ Erdos501.FOL.ZFC) (a : M) :
    ∃ S : M, ∀ z, memM z S ↔ z = a := by
  have hserial : ∀ x : M, memM x unitSet →
      ∃ y, constantImageFormula.Realize default (Fin.snoc (Fin.snoc ![a] x) y) := by
    intro x _
    exact ⟨a, (realize_constantImageFormula a x a).mpr rfl⟩
  obtain ⟨S, hforward, hback⟩ :=
    collectionWithParams hZFC 1 constantImageFormula ![a] unitSet hserial
  refine ⟨S, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, hxa⟩ := hback z hz
    exact (realize_constantImageFormula a x z).mp hxa
  · intro hza
    obtain ⟨y, hy, hya⟩ := hforward emptyM ((unit_mem hZFC emptyM).mpr rfl)
    have hy_eq : y = a := (realize_constantImageFormula a emptyM y).mp hya
    simpa only [hy_eq, hza] using hy

/-- Add two fresh final variables without changing the original parameters
or the distinguished variable `x`. -/
def liftLastTwo {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    L.BoundedFormula Empty (n + 3) :=
  (φ.liftAt 1 (n + 1)).liftAt 1 (n + 2)

theorem realize_liftLastTwo {n : ℕ} (φ : L.BoundedFormula Empty (n + 1))
    (p : Fin n → M) (x y z : M) :
    (liftLastTwo φ).Realize default (Fin.snoc (Fin.snoc (Fin.snoc p x) y) z) ↔
      φ.Realize default (Fin.snoc p x) := by
  simp only [liftLastTwo, BoundedFormula.realize_liftAt_one_self,
    Function.comp_def, Fin.snoc_castSucc]

/-- `∀ z, z ∈ y ↔ z = x ∧ φ(p,x)` at levels `p, x, y, z`. -/
def separationStep {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    L.BoundedFormula Empty (n + 2) :=
  BoundedFormula.all <|
    (Relations.boundedFormula₂ (Rel.mem : L.Relations 2)
      (Term.var (Sum.inr ⟨n + 2, by omega⟩))
      (Term.var (Sum.inr ⟨n + 1, by omega⟩))).iff
      ((Term.bdEqual
        (Term.var (Sum.inr ⟨n + 2, by omega⟩))
        (Term.var (Sum.inr ⟨n, by omega⟩))) ⊓ liftLastTwo φ)

theorem realize_separationStep {n : ℕ} (φ : L.BoundedFormula Empty (n + 1))
    (p : Fin n → M) (x y : M) :
    (separationStep φ).Realize default (Fin.snoc (Fin.snoc p x) y) ↔
      ∀ z, memM z y ↔ z = x ∧ φ.Realize default (Fin.snoc p x) := by
  simp only [separationStep, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_rel₂, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inr,
    realize_liftLastTwo]
  apply forall_congr'
  intro z
  let v : Fin (n + 3) → M := Fin.snoc (Fin.snoc (Fin.snoc p x) y) z
  -- These are precisely the existing levels z = n+2, y = n+1, x = n.
  -- Expose their structural forms so the fixed snoc equations apply directly.
  change
    (memM (v (Fin.last (n + 2))) (v ((Fin.last (n + 1)).castSucc)) ↔
      v (Fin.last (n + 2)) = v ((Fin.last n).castSucc.castSucc) ∧
        φ.Realize default (Fin.snoc p x)) ↔
      (memM z y ↔ z = x ∧ φ.Realize default (Fin.snoc p x))
  dsimp only [v]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

/-- Separation for an actual finite first-order formula with finite parameters. -/
theorem separation (hZFC : M ⊨ Erdos501.FOL.ZFC) (n : ℕ)
    (φ : L.BoundedFormula Empty (n + 1)) (p : Fin n → M) (A : M) :
    ∃ B : M, ∀ x, memM x B ↔ memM x A ∧ φ.Realize default (Fin.snoc p x) := by
  classical
  have hserial : ∀ x : M, memM x A →
      ∃ y, (separationStep φ).Realize default (Fin.snoc (Fin.snoc p x) y) := by
    intro x _
    by_cases hφ : φ.Realize default (Fin.snoc p x)
    · obtain ⟨y, hy⟩ := singleton hZFC x
      refine ⟨y, (realize_separationStep φ p x y).mpr ?_⟩
      intro z
      rw [hy z]
      exact ⟨fun hzx => ⟨hzx, hφ⟩, And.left⟩
    · refine ⟨emptyM, (realize_separationStep φ p x emptyM).mpr ?_⟩
      intro z
      exact ⟨fun hz => False.elim (empty_mem hZFC z hz),
        fun hz => False.elim (hφ hz.2)⟩
  obtain ⟨C, hforward, hback⟩ :=
    collectionWithParams hZFC n (separationStep φ) p A hserial
  refine ⟨unionM C, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨y, hyC, hzy⟩ := (union_mem hZFC C z).mp hz
    obtain ⟨x, hxA, hxy⟩ := hback y hyC
    obtain ⟨hzx, hφ⟩ := ((realize_separationStep φ p x y).mp hxy z).mp hzy
    subst z
    exact ⟨hxA, hφ⟩
  · rintro ⟨hzA, hφ⟩
    obtain ⟨y, hyC, hzy⟩ := hforward z hzA
    apply (union_mem hZFC C z).mpr
    exact ⟨y, hyC, ((realize_separationStep φ p z y).mp hzy z).mpr ⟨rfl, hφ⟩⟩

#print axioms realize_constantImageFormula
#print axioms singleton
#print axioms realize_liftLastTwo
#print axioms realize_separationStep
#print axioms separation

end ClassicismZFC.Separation
