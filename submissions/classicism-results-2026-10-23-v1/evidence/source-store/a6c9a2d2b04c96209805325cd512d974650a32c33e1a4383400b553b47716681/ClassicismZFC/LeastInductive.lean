import ClassicismZFC.Separation

/-!
# The least internally represented inductive subset of a domain

The addition graph uses precisely `Erdos501.FOL.app2F`: the graph entry for
`x + one = y` is `pair(pair(x,one),y)`. This is the source set-theory field
encoding, not a tuple code from the typed hierarchy.

The only structural premise needed here is `zero ∈ E`. Closure is explicitly
guarded by `x,y ∈ E`; a field's total-addition theorem can separately supply
the successor value and its membership in `E`.

Separation uses the explicit finite formula below. Its universal quantifier
ranges over elements of the membership model, hence over internally
represented candidate subsets, not arbitrary external subsets. The resulting
least set is not asserted to be externally standard or equipotent to the
model's omega. No identification with omega is assumed or proved here.
-/

open FirstOrder FirstOrder.Language
open Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.LeastInductive

open SetLaws

universe u

variable {M : Type u} [L.Structure M]

/-- An internal subset of `E` containing zero and closed under the represented
successor graph whenever its input and output lie in `E`. -/
def IsInductive (E zero one Add F : M) : Prop :=
  (∀ x, memM x F → memM x E) ∧
  memM zero F ∧
  ∀ x y, memM x E → memM y E → memM x F →
    memM (pairM (pairM x one) y) Add → memM y F

/-- The least such internal subset, with leastness against every internally
represented inductive subset. -/
def LeastInductive (E zero one Add N : M) : Prop :=
  IsInductive E zero one Add N ∧
  ∀ F, IsInductive E zero one Add F → ∀ x, memM x N → memM x F

/-- The domain itself is an internal inductive candidate. -/
theorem domain_inductive (E zero one Add : M) (hzero : memM zero E) :
    IsInductive E zero one Add E :=
  ⟨fun _ hx => hx, hzero, fun _ _ _ hy _ _ => hy⟩

/-- Finite first-order syntax for the three clauses of `IsInductive`. -/
def inductiveF (E zero one Add F : Tm) : Fm :=
  andF (subsetF F E)
    (andF (memF zero F)
      (allF fun x => allF fun y =>
        impF (memF (varT x) E)
          (impF (memF (varT y) E)
            (impF (memF (varT x) F)
              (impF (app2F Add (varT x) one (varT y))
                (memF (varT y) F))))))

/-- Bound levels are `E=0, zero=1, one=2, Add=3, F=4`. -/
def inductiveFormula : L.BoundedFormula Empty 5 :=
  inductiveF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) 5

theorem realize_inductiveFormula (E zero one Add F : M) :
    inductiveFormula.Realize default (Fin.snoc ![E, zero, one, Add] F) ↔
      IsInductive E zero one Add F := by
  simp [inductiveFormula, inductiveF, IsInductive, subsetF, andF, allF,
    impF, memF, app2F, varT, memM, Fin.snoc]

/-- At levels `E=0, zero=1, one=2, Add=3, x=4`, this is
`∀ F, IsInductive(E,zero,one,Add,F) → x ∈ F`. -/
def leastFilter : L.BoundedFormula Empty 5 :=
  (allF fun F =>
    impF (inductiveF (varT 0) (varT 1) (varT 2) (varT 3) (varT F))
      (memF (varT 4) (varT F))) 5

theorem realize_leastFilter (E zero one Add x : M) :
    leastFilter.Realize default (Fin.snoc ![E, zero, one, Add] x) ↔
      ∀ F, IsInductive E zero one Add F → memM x F := by
  simp [leastFilter, inductiveF, IsInductive, subsetF, andF, allF,
    impF, memF, app2F, varT, memM, Fin.snoc]

/-- The defining internal intersection exists by the actual finite-formula
Separation theorem. No structural field premises are needed for this step. -/
theorem exists_intersection (hZFC : M ⊨ Erdos501.FOL.ZFC) (E zero one Add : M) :
    ∃ N : M, ∀ x, memM x N ↔
      memM x E ∧ ∀ F, IsInductive E zero one Add F → memM x F := by
  obtain ⟨N, hN⟩ :=
    Separation.separation hZFC 4 leastFilter ![E, zero, one, Add] E
  refine ⟨N, ?_⟩
  intro x
  rw [hN x, realize_leastFilter]

/-- An actual least internal inductive subset exists once zero lies in `E`. -/
theorem exists_leastInductive (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (E zero one Add : M) (hzero : memM zero E) :
    ∃ N : M, LeastInductive E zero one Add N := by
  obtain ⟨N, hN⟩ := exists_intersection hZFC E zero one Add
  refine ⟨N, ?_⟩
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact ((hN x).mp hx).1
    · exact (hN zero).mpr ⟨hzero, fun F hF => hF.2.1⟩
    · intro x y hxE hyE hxN hAdd
      apply (hN y).mpr
      refine ⟨hyE, ?_⟩
      intro F hF
      exact hF.2.2 x y hxE hyE (((hN x).mp hxN).2 F hF) hAdd
  · intro F hF x hxN
    exact ((hN x).mp hxN).2 F hF

/-- A chosen least internal inductive subset, obtained from its proved existence. -/
noncomputable def leastSet (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (E zero one Add : M) (hzero : memM zero E) : M :=
  Classical.choose (exists_leastInductive hZFC E zero one Add hzero)

theorem leastSet_spec (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (E zero one Add : M) (hzero : memM zero E) :
    LeastInductive E zero one Add (leastSet hZFC E zero one Add hzero) :=
  Classical.choose_spec (exists_leastInductive hZFC E zero one Add hzero)

theorem leastSet_subset (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (E zero one Add : M) (hzero : memM zero E) :
    ∀ x, memM x (leastSet hZFC E zero one Add hzero) → memM x E :=
  (leastSet_spec hZFC E zero one Add hzero).1.1

theorem leastSet_mem_power (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (E zero one Add : M) (hzero : memM zero E) :
    memM (leastSet hZFC E zero one Add hzero) (powerM E) :=
  (power_mem hZFC E (leastSet hZFC E zero one Add hzero)).mpr
    (leastSet_subset hZFC E zero one Add hzero)

theorem leastSet_zero_mem (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (E zero one Add : M) (hzero : memM zero E) :
    memM zero (leastSet hZFC E zero one Add hzero) :=
  (leastSet_spec hZFC E zero one Add hzero).1.2.1

theorem leastSet_succ_closed (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (E zero one Add : M) (hzero : memM zero E) :
    ∀ x y, memM x E → memM y E →
      memM x (leastSet hZFC E zero one Add hzero) →
      memM (pairM (pairM x one) y) Add →
      memM y (leastSet hZFC E zero one Add hzero) :=
  (leastSet_spec hZFC E zero one Add hzero).1.2.2

theorem leastSet_least (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (E zero one Add : M) (hzero : memM zero E)
    (F : M) (hF : IsInductive E zero one Add F) :
    ∀ x, memM x (leastSet hZFC E zero one Add hzero) → memM x F :=
  (leastSet_spec hZFC E zero one Add hzero).2 F hF

#print axioms domain_inductive
#print axioms realize_inductiveFormula
#print axioms realize_leastFilter
#print axioms exists_intersection
#print axioms exists_leastInductive
#print axioms leastSet_spec
#print axioms leastSet_subset
#print axioms leastSet_mem_power
#print axioms leastSet_zero_mem
#print axioms leastSet_succ_closed
#print axioms leastSet_least

end ClassicismZFC.LeastInductive
