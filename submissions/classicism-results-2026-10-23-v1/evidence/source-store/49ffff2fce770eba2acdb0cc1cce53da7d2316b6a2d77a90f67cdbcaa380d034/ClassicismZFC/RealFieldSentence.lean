import ClassicismZFC.CHTranslation
import Flypitch4.Erdos501.Semantics

/-!
# A first-order existence sentence for an internal complete ordered field

The twenty field/completeness clauses are the actual finite formula of Elliot
Glazer's `Erdos501.FOL.Statement`, translated literally to the corresponding
Flypitch formula. Completeness quantifies over the model's powerset elements,
not over arbitrary external subsets of the carrier.

The semantic computation is adapted from the Flypitch Project's
`realize_Erdos501_ex_f`, pinned at commit
218d1c1e46f77d4db80e566d1721782e85b94a17 (Apache 2.0). The irrelevant Erdős
property is omitted. No field-existence or CH-transfer axiom is introduced.

This six-code field predicate is not yet the project's seven-parameter `Real`:
the internally least inductive predicate and the graph-support recoding are
separate, explicit obligations.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder Fol Flypitch

namespace ClassicismZFC.RealFieldSentence

/-- Existence of six set codes satisfying the actual field/completeness formula. -/
def ExistsRealField : L.Sentence := toSentence <|
  exF fun R => exF fun plus => exF fun times => exF fun lt =>
    exF fun zero => exF fun one =>
      completeOrderedFieldF (varT R) (varT plus) (varT times)
        (varT lt) (varT zero) (varT one)

/-- The same sentence in Flypitch's original first-order syntax. -/
def ExistsRealField_f : Fol.sentence L_ZFC :=
  Flypitch.Erdos501.toSentence <|
    Flypitch.Erdos501.exF fun R => Flypitch.Erdos501.exF fun plus =>
    Flypitch.Erdos501.exF fun times => Flypitch.Erdos501.exF fun lt =>
    Flypitch.Erdos501.exF fun zero => Flypitch.Erdos501.exF fun one =>
      Flypitch.Erdos501.CompleteOrderedFieldF
        (Flypitch.Erdos501.varT R) (Flypitch.Erdos501.varT plus)
        (Flypitch.Erdos501.varT times) (Flypitch.Erdos501.varT lt)
        (Flypitch.Erdos501.varT zero) (Flypitch.Erdos501.varT one)

-- This is structural reduction of one fixed twenty-clause formula, not proof
-- search. Scope the larger recursion-depth bound to this literal equality only.
set_option maxRecDepth 4096 in
/-- Literal syntax translation, rather than an assumed field correspondence. -/
theorem tr_ExistsRealField : tr ExistsRealField = ExistsRealField_f := rfl

/-- The conjunction retained through completeness on the positive side. -/
def Positive : L.Sentence := ExistsRealField ⊓ CHTranslation.CH

/-- The conjunction retained through completeness on the negative side. -/
def Negative : L.Sentence := ExistsRealField ⊓ CHTranslation.CH.not

/-- The six-code formula, with levels in the order `R,+,*,<,0,1`. -/
def fieldBody : L.BoundedFormula Empty 6 :=
  completeOrderedFieldF (varT 0) (varT 1) (varT 2)
    (varT 3) (varT 4) (varT 5) 6

/-- Actual satisfaction of the twenty field/completeness clauses at six codes. -/
def IsField {M : Type*} [L.Structure M]
    (R plus times lt zero one : M) : Prop :=
  fieldBody.Realize Empty.elim ![R, plus, times, lt, zero, one]

private def fieldContext {M : Type*} (R plus times lt zero one : M) : Fin 6 → M :=
  Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc
    Fin.elim0 R) plus) times) lt) zero) one

private theorem fieldContext_eq {M : Type*} (R plus times lt zero one : M) :
    fieldContext R plus times lt zero one = ![R, plus, times, lt, zero, one] := by
  funext i
  fin_cases i <;> rfl

theorem realize_ExistsRealField {M : Type*} [L.Structure M] :
    (M ⊨ ExistsRealField) ↔
      ∃ R plus times lt zero one : M, IsField R plus times lt zero one := by
  simp only [ExistsRealField, toSentence, exF, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_ex]
  have hfree : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  have hbound : (default : Fin 0 → M) = Fin.elim0 := Subsingleton.elim _ _
  simp only [hfree, hbound]
  change (∃ R plus times lt zero one : M,
    fieldBody.Realize Empty.elim (fieldContext R plus times lt zero one)) ↔ _
  simp only [fieldContext_eq, IsField]

theorem realize_Positive {M : Type*} [L.Structure M] :
    (M ⊨ Positive) ↔
      (∃ R plus times lt zero one : M, IsField R plus times lt zero one) ∧
      (M ⊨ CHTranslation.CH) := by
  rw [Positive, Sentence.realize_inf, realize_ExistsRealField]

theorem realize_Negative {M : Type*} [L.Structure M] :
    (M ⊨ Negative) ↔
      (∃ R plus times lt zero one : M, IsField R plus times lt zero one) ∧
      ¬ (M ⊨ CHTranslation.CH) := by
  rw [Negative, Sentence.realize_inf, realize_ExistsRealField, Sentence.realize_not]

section Boolean

open Fol bSet Flypitch.Erdos501

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

/-- Exact Boolean interpretation of the field-existence sentence. -/
theorem boolean_realize_ExistsRealField :
    ⟦ExistsRealField_f⟧[V β] =
      ⨆ R : bSet β, ⨆ plus : bSet β, ⨆ times : bSet β,
      ⨆ lt : bSet β, ⨆ zero : bSet β, ⨆ one : bSet β,
        Sem.completeOrderedField R plus times lt zero one := by
  simp only [ExistsRealField_f, Flypitch.Erdos501.toSentence,
    Flypitch.Erdos501.allF, Flypitch.Erdos501.exF,
    Flypitch.Erdos501.allIn, Flypitch.Erdos501.exIn,
    Flypitch.Erdos501.andF, Flypitch.Erdos501.orF, Flypitch.Erdos501.impF,
    Flypitch.Erdos501.iffF, Flypitch.Erdos501.notF, Flypitch.Erdos501.memF,
    Flypitch.Erdos501.eqF, Flypitch.Erdos501.varT, Flypitch.Erdos501.powT,
    Flypitch.Erdos501.pairT, Flypitch.Erdos501.empT,
    Flypitch.Erdos501.ltF, Flypitch.Erdos501.leF,
    Flypitch.Erdos501.appF, Flypitch.Erdos501.app2F,
    Flypitch.Erdos501.isOp2F, Flypitch.Erdos501.andsF,
    CompleteOrderedFieldF,
    boolean_realize_sentence, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_or,
    boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair', boolean_realize_bounded_term_Powerset',
    boolean_realize_bounded_term_emptyset',
    boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [Sem.completeOrderedField, Sem.isOp2, Sem.assoc, Sem.comm,
    Sem.ident, Sem.addInv, Sem.mulInv, Sem.distrib, Sem.irrefl, Sem.trans,
    Sem.total, Sem.addCompat, Sem.mulPos, Sem.complete,
    Sem.lt, Sem.le, Sem.app2]
  rfl

/-- Any actually constructed Boolean-valued complete field supplies the sentence. -/
theorem forced_exists_of_field (R plus times lt zero one : bSet β)
    (h : (⊤ : β) ≤ Sem.completeOrderedField R plus times lt zero one) :
    ⊤ ⊩[V β] tr ExistsRealField := by
  change (⊤ : β) ≤ ⟦tr ExistsRealField⟧[V β]
  rw [tr_ExistsRealField, boolean_realize_ExistsRealField]
  exact le_iSup_of_le R (le_iSup_of_le plus (le_iSup_of_le times
    (le_iSup_of_le lt (le_iSup_of_le zero (le_iSup_of_le one h)))))

end Boolean

end ClassicismZFC.RealFieldSentence
