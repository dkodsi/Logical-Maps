import ClassicismZFC.RealFieldSentence
import ClassicismZFC.SetLaws

/-!
# The literal twenty clauses of an internal complete ordered field

The semantic record below has exactly the clauses of the upstream finite
formula. `of_isField` derives every field from actual first-order satisfaction;
the record is an intermediate decomposition, not an additional assumption.
Graph application retains the source's `((x,y),z)` convention. Quantifiers
over subsets in completeness range over internal powerset members.
-/

open FirstOrder FirstOrder.Language
open Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.SourceFieldSemantics

open SetLaws

universe u
variable {M : Type u} [L.Structure M]

def app2 (Op x y z : M) : Prop := memM (pairM (pairM x y) z) Op
def lt (Lt x y : M) : Prop := memM (pairM x y) Lt
def le (Lt x y : M) : Prop := lt Lt x y ∨ x = y

/-- A source operation is total on its domain and has a unique output even
when the competing output is not initially known to be in the domain. -/
def IsOp2 (E Op : M) : Prop :=
  ∀ x, memM x E → ∀ y, memM y E →
    ∃ z, memM z E ∧ app2 Op x y z ∧ ∀ z', app2 Op x y z' → z' = z

/-- The exact twenty semantic clauses, before changing strict order to
non-strict order or recoding any graph into the typed hierarchy. -/
structure Field (E Add Mul Lt zero one : M) : Prop where
  isOp2_plus : IsOp2 E Add
  isOp2_times : IsOp2 E Mul
  zero_mem : memM zero E
  one_mem : memM one E
  assoc_plus : ∀ x, memM x E → ∀ y, memM y E → ∀ z, memM z E →
    ∀ a b c d, app2 Add x y a → app2 Add a z b → app2 Add y z c →
      app2 Add x c d → b = d
  comm_plus : ∀ x, memM x E → ∀ y, memM y E →
    ∀ z, app2 Add x y z → app2 Add y x z
  ident_plus : ∀ x, memM x E → app2 Add x zero x
  addInv : ∀ x, memM x E → ∃ y, memM y E ∧ app2 Add x y zero
  assoc_times : ∀ x, memM x E → ∀ y, memM y E → ∀ z, memM z E →
    ∀ a b c d, app2 Mul x y a → app2 Mul a z b → app2 Mul y z c →
      app2 Mul x c d → b = d
  comm_times : ∀ x, memM x E → ∀ y, memM y E →
    ∀ z, app2 Mul x y z → app2 Mul y x z
  ident_times : ∀ x, memM x E → app2 Mul x one x
  mulInv : ∀ x, memM x E → x ≠ zero →
    ∃ y, memM y E ∧ app2 Mul x y one
  zero_ne_one : zero ≠ one
  distrib : ∀ x, memM x E → ∀ y, memM y E → ∀ z, memM z E →
    ∀ a b c d e, app2 Add y z a → app2 Mul x a b →
      app2 Mul x y c → app2 Mul x z d → app2 Add c d e → b = e
  irrefl : ∀ x, memM x E → ¬ lt Lt x x
  trans : ∀ x, memM x E → ∀ y, memM y E → ∀ z, memM z E →
    lt Lt x y → lt Lt y z → lt Lt x z
  total : ∀ x, memM x E → ∀ y, memM y E →
    lt Lt x y ∨ x = y ∨ lt Lt y x
  addCompat : ∀ x, memM x E → ∀ y, memM y E → ∀ z, memM z E →
    ∀ a b, lt Lt x y → app2 Add x z a → app2 Add y z b → lt Lt a b
  mulPos : ∀ x, memM x E → ∀ y, memM y E → ∀ z,
    lt Lt zero x → lt Lt zero y → app2 Mul x y z → lt Lt zero z
  complete : ∀ S, memM S (powerM E) → S ≠ emptyM →
    (∃ b, memM b E ∧ ∀ s, memM s S → le Lt s b) →
    ∃ a, memM a E ∧ (∀ s, memM s S → le Lt s a) ∧
      ∀ b, memM b E → (∀ s, memM s S → le Lt s b) → le Lt a b

/-- Every semantic field is obtained by evaluating the actual finite source
formula. This is a computation on its twenty clauses and de Bruijn levels. -/
theorem of_isField {E Add Mul Lt zero one : M}
    (h : RealFieldSentence.IsField E Add Mul Lt zero one) :
    Field E Add Mul Lt zero one := by
  unfold RealFieldSentence.IsField RealFieldSentence.fieldBody at h
  simp only [completeOrderedFieldF, andsF, isOp2F, allIn, exIn,
    allF, exF, andF, orF, impF, notF, app2F, ltF, leF, memF, eqF,
    BoundedFormula.realize_inf, BoundedFormula.realize_sup,
    BoundedFormula.realize_imp, BoundedFormula.realize_not,
    BoundedFormula.realize_all, BoundedFormula.realize_ex,
    BoundedFormula.realize_rel₂, BoundedFormula.realize_bdEqual,
    realize_pairT, realize_powT, realize_empT] at h
  simp [varT, Term.realize_var, Fin.snoc, memM] at h
  rcases h with ⟨hplus, htimes, hzero, hone, hassocPlus, hcommPlus,
    hidentPlus, haddInv, hassocTimes, hcommTimes, hidentTimes, hmulInv,
    hne, hdistrib, hirrefl, htrans, htotal, haddCompat, hmulPos, hcomplete⟩
  refine ⟨hplus, htimes, hzero, hone, hassocPlus, hcommPlus,
    hidentPlus, haddInv, hassocTimes, hcommTimes, hidentTimes, hmulInv,
    hne, hdistrib, hirrefl, htrans, htotal, haddCompat, hmulPos, ?_⟩
  intro S hS hnonempty hbounded
  rcases hbounded with ⟨b, hb, hupper⟩
  exact hcomplete S hS hnonempty b hb hupper

#print axioms of_isField

end ClassicismZFC.SourceFieldSemantics
