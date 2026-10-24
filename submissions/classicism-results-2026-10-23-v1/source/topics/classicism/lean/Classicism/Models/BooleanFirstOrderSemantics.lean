import Classicism.Models.BooleanValuedEquality
import Mathlib.ModelTheory.Semantics

/-!
# Boolean evaluation of Mathlib's relational first-order syntax

Original supporting formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-model-extraction.md`, sections 1--2 and 5
(unpaginated), and `boolean-valued-finite-choice.md`, sections 3--4.

The syntax is Mathlib's actual `FirstOrder.Language.Term` and
`FirstOrder.Language.BoundedFormula`. Functions are absent. A structure has
an actual nonempty Boolean equality space and coherent atomic relations;
it has no model-existence, witness-attainment, or theory-verdict field.
Evaluation, all connective and quantifier clauses, and substitution at an
arbitrary Boolean degree are constructed below. Countable extraction and
the supported typed model remain separate obligations.
-/

namespace Classicism.Meta.ChoiceBoolean.FirstOrderSemantics

universe u v w uL vL uA

open FirstOrder

variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Boolean implication respects equivalence below a fixed condition. -/
private theorem himp_subst {q a a' b b' : B}
    (ha : q ⊓ a' ≤ a) (hb : q ⊓ b ≤ b') :
    q ⊓ (a ⇨ b) ≤ a' ⇨ b' := by
  apply le_himp_iff.mpr
  have hleft : (q ⊓ (a ⇨ b)) ⊓ a' ≤ q :=
    inf_le_left.trans inf_le_left
  have ha' : (q ⊓ (a ⇨ b)) ⊓ a' ≤ a :=
    (le_inf hleft inf_le_right).trans ha
  have hb' : (q ⊓ (a ⇨ b)) ⊓ a' ≤ b :=
    (le_inf (inf_le_left.trans inf_le_right) ha').trans himp_inf_le
  exact (le_inf hleft hb').trans hb

theorem himp_congr {q a a' b b' : B}
    (ha : q ≤ iffValue a a') (hb : q ≤ iffValue b b') :
    q ≤ iffValue (a ⇨ b) (a' ⇨ b') := by
  obtain ⟨haa', ha'a⟩ := le_iffValue_iff.mp ha
  obtain ⟨hbb', hb'b⟩ := le_iffValue_iff.mp hb
  exact le_iffValue_iff.mpr
    ⟨himp_subst ha'a hbb', himp_subst haa' hb'b⟩

/-- Arbitrary universal quantification preserves local equivalence. -/
theorem iInf_congr_value {I : Type w} {q : B} {f g : I → B}
    (h : ∀ i, q ≤ iffValue (f i) (g i)) :
    q ≤ iffValue (⨅ i, f i) (⨅ i, g i) := by
  apply le_iffValue_iff.mpr
  constructor
  · apply le_iInf
    intro i
    exact (inf_le_inf_left q (iInf_le f i)).trans
      (le_iffValue_iff.mp (h i)).1
  · apply le_iInf
    intro i
    exact (inf_le_inf_left q (iInf_le g i)).trans
      (le_iffValue_iff.mp (h i)).2

variable (X : EqualitySpace.{u, v} B)

/-- Equality is a coherent binary atomic relation. -/
theorem equality_subst {q : B} {a a' b b' : X.Carrier}
    (ha : q ≤ X.eqv a a') (hb : q ≤ X.eqv b b') :
    q ⊓ X.eqv a b ≤ X.eqv a' b' := by
  have haa : q ≤ X.eqv a' a := by
    simpa only [X.symm a' a] using ha
  have hab : q ⊓ X.eqv a b ≤ X.eqv a' b :=
    (inf_le_inf_right _ haa).trans (X.trans a' a b)
  exact (le_inf hab (inf_le_left.trans hb)).trans (X.trans a' b b')

theorem equality_congr {q : B} {a a' b b' : X.Carrier}
    (ha : q ≤ X.eqv a a') (hb : q ≤ X.eqv b b') :
    q ≤ iffValue (X.eqv a b) (X.eqv a' b') := by
  apply le_iffValue_iff.mpr
  refine ⟨equality_subst X ha hb, ?_⟩
  apply equality_subst X
  · simpa only [X.symm a' a] using ha
  · simpa only [X.symm b' b] using hb

/-- Equality of assignments is the meet of the component equalities. -/
def assignmentEq {I : Type w} (a b : I → X.Carrier) : B :=
  ⨅ i, X.eqv (a i) (b i)

theorem assignmentEq_le {I : Type w} (a b : I → X.Carrier) (i : I) :
    assignmentEq X a b ≤ X.eqv (a i) (b i) := iInf_le _ i

@[simp] theorem assignmentEq_refl {I : Type w} (a : I → X.Carrier) :
    assignmentEq X a a = ⊤ := by
  simp only [assignmentEq, X.refl, iInf_top]

variable (L : FirstOrder.Language.{uL, vL})

/-- Only atomic data and atomic coherence are inputs to Boolean semantics. -/
structure Structure where
  nonempty : Nonempty X.Carrier
  relMap : ∀ {n : Nat}, L.Relations n → (Fin n → X.Carrier) → B
  rel_subst : ∀ {n : Nat} (r : L.Relations n) (a b : Fin n → X.Carrier),
    assignmentEq X a b ⊓ relMap r a ≤ relMap r b

variable {L} [L.IsRelational]
variable {X} (M : Structure X L)

theorem relMap_congr {n : Nat} (r : L.Relations n)
    {q : B} {a b : Fin n → X.Carrier}
    (h : ∀ i, q ≤ X.eqv (a i) (b i)) :
    q ≤ iffValue (M.relMap r a) (M.relMap r b) := by
  apply le_iffValue_iff.mpr
  constructor
  · have hab : q ≤ assignmentEq X a b := le_iInf h
    exact (inf_le_inf_right _ hab).trans (M.rel_subst r a b)
  · have hba : q ≤ assignmentEq X b a := by
      apply le_iInf
      intro i
      simpa only [X.symm (b i) (a i)] using h i
    exact (inf_le_inf_right _ hba).trans (M.rel_subst r b a)

variable {α : Type uA}

/-- In a relational language every term is a variable. -/
def termValue {D : Type v} (v : α → D) : L.Term α → D
  | .var a => v a
  | .func f _ => isEmptyElim f

@[simp] theorem termValue_var (v : α → X.Carrier) (a : α) :
    termValue (L := L) v (.var a) = v a := rfl

theorem termValue_congr (t : L.Term α) {q : B}
    {v w : α → X.Carrier} (h : ∀ a, q ≤ X.eqv (v a) (w a)) :
    q ≤ X.eqv (termValue v t) (termValue w t) := by
  cases t with
  | var a => exact h a
  | func f _ => exact isEmptyElim f

/-- Actual recursive evaluation on Mathlib's bounded formulas. The bound
variable appended by `all` is the last de Bruijn level, as in Mathlib. -/
def value : ∀ {n : Nat}, L.BoundedFormula α n →
    (α → X.Carrier) → (Fin n → X.Carrier) → B
  | _, .falsum, _, _ => ⊥
  | _, .equal t s, v, xs =>
      X.eqv (termValue (Sum.elim v xs) t) (termValue (Sum.elim v xs) s)
  | _, .rel r ts, v, xs =>
      M.relMap r (fun i => termValue (Sum.elim v xs) (ts i))
  | _, .imp φ ψ, v, xs => value φ v xs ⇨ value ψ v xs
  | _, .all φ, v, xs => ⨅ x : X.Carrier, value φ v (Fin.snoc xs x)

@[simp] theorem value_falsum {n : Nat} (v : α → X.Carrier)
    (xs : Fin n → X.Carrier) : value M .falsum v xs = ⊥ := rfl

@[simp] theorem value_equal {n : Nat} (t s : L.Term (α ⊕ Fin n))
    (v : α → X.Carrier) (xs : Fin n → X.Carrier) :
    value M (.equal t s) v xs =
      X.eqv (termValue (Sum.elim v xs) t) (termValue (Sum.elim v xs) s) := rfl

@[simp] theorem value_rel {n k : Nat} (r : L.Relations k)
    (ts : Fin k → L.Term (α ⊕ Fin n))
    (v : α → X.Carrier) (xs : Fin n → X.Carrier) :
    value M (.rel r ts) v xs =
      M.relMap r (fun i => termValue (Sum.elim v xs) (ts i)) := rfl

@[simp] theorem value_imp {n : Nat} (φ ψ : L.BoundedFormula α n)
    (v : α → X.Carrier) (xs : Fin n → X.Carrier) :
    value M (.imp φ ψ) v xs = value M φ v xs ⇨ value M ψ v xs := rfl

@[simp] theorem value_all {n : Nat} (φ : L.BoundedFormula α (n + 1))
    (v : α → X.Carrier) (xs : Fin n → X.Carrier) :
    value M (.all φ) v xs = ⨅ x : X.Carrier, value M φ v (Fin.snoc xs x) := rfl

@[simp] theorem value_not {n : Nat} (φ : L.BoundedFormula α n)
    (v : α → X.Carrier) (xs : Fin n → X.Carrier) :
    value M φ.not v xs = (value M φ v xs)ᶜ := by
  change value M φ v xs ⇨ ⊥ = _
  exact himp_bot _

@[simp] theorem value_ex {n : Nat} (φ : L.BoundedFormula α (n + 1))
    (v : α → X.Carrier) (xs : Fin n → X.Carrier) :
    value M φ.ex v xs = ⨆ x : X.Carrier, value M φ v (Fin.snoc xs x) := by
  change ((⨅ x : X.Carrier, value M φ v (Fin.snoc xs x) ⇨ ⊥) ⇨ ⊥) = _
  simp only [himp_bot, compl_iInf, compl_compl]

@[simp] theorem value_top {n : Nat} (v : α → X.Carrier)
    (xs : Fin n → X.Carrier) :
    value M (⊤ : L.BoundedFormula α n) v xs = ⊤ := by
  change (⊥ : B) ⇨ ⊥ = ⊤
  exact himp_self

@[simp] theorem value_inf {n : Nat} (φ ψ : L.BoundedFormula α n)
    (v : α → X.Carrier) (xs : Fin n → X.Carrier) :
    value M (φ ⊓ ψ) v xs = value M φ v xs ⊓ value M ψ v xs := by
  change (value M φ v xs ⇨ (value M ψ v xs ⇨ ⊥)) ⇨ ⊥ = _
  simp only [himp_bot]
  simp only [himp_eq, compl_sup, compl_compl, inf_comm]

@[simp] theorem value_sup {n : Nat} (φ ψ : L.BoundedFormula α n)
    (v : α → X.Carrier) (xs : Fin n → X.Carrier) :
    value M (φ ⊔ ψ) v xs = value M φ v xs ⊔ value M ψ v xs := by
  change (value M φ v xs ⇨ ⊥) ⇨ value M ψ v xs = _
  simp only [himp_bot]
  simp only [himp_eq, compl_compl, sup_comm]

/-- Full formula substitution below any Boolean condition. No separated
equality, witness attainment, or countability assumption is used. -/
theorem value_congr : ∀ {n : Nat} (φ : L.BoundedFormula α n)
    (v w : α → X.Carrier) (xs ys : Fin n → X.Carrier) (q : B),
    (∀ a, q ≤ X.eqv (v a) (w a)) →
    (∀ i, q ≤ X.eqv (xs i) (ys i)) →
    q ≤ iffValue (value M φ v xs) (value M φ w ys) := by
  intro n φ
  induction φ with
  | falsum =>
      intro v w xs ys q hv hxs
      simp only [value_falsum, iffValue_refl]
      exact le_top
  | equal t s =>
      intro v w xs ys q hv hxs
      apply equality_congr X
      · apply termValue_congr (X := X) t
        intro a
        cases a with
        | inl a => exact hv a
        | inr i => exact hxs i
      · apply termValue_congr (X := X) s
        intro a
        cases a with
        | inl a => exact hv a
        | inr i => exact hxs i
  | rel r ts =>
      intro v w xs ys q hv hxs
      apply relMap_congr M r
      intro i
      apply termValue_congr (X := X) (ts i)
      intro a
      cases a with
      | inl a => exact hv a
      | inr j => exact hxs j
  | imp φ ψ ihφ ihψ =>
      intro v w xs ys q hv hxs
      exact himp_congr (ihφ v w xs ys q hv hxs) (ihψ v w xs ys q hv hxs)
  | all φ ih =>
      intro v w xs ys q hv hxs
      apply iInf_congr_value
      intro x
      apply ih v w (Fin.snoc xs x) (Fin.snoc ys x) q hv
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last, X.refl] using (le_top : q ≤ (⊤ : B))
      · simpa only [Fin.snoc_castSucc] using hxs j

/-- Full substitution with the actual Boolean equality of assignments. -/
theorem value_assignment_congr {n : Nat} (φ : L.BoundedFormula α n)
    (v w : α → X.Carrier) (xs ys : Fin n → X.Carrier) :
    assignmentEq X v w ⊓ assignmentEq X xs ys ≤
      iffValue (value M φ v xs) (value M φ w ys) := by
  apply value_congr M φ v w xs ys
  · intro a
    exact inf_le_left.trans (assignmentEq_le X v w a)
  · intro i
    exact inf_le_right.trans (assignmentEq_le X xs ys i)

theorem value_assignment_subst {n : Nat} (φ : L.BoundedFormula α n)
    (v w : α → X.Carrier) (xs ys : Fin n → X.Carrier) :
    (assignmentEq X v w ⊓ assignmentEq X xs ys) ⊓ value M φ v xs ≤
      value M φ w ys :=
  (le_iffValue_iff.mp (value_assignment_congr M φ v w xs ys)).1

/-- Formula and sentence truth are values, not assumed verdicts. -/
def formulaValue (φ : L.Formula α) (v : α → X.Carrier) : B :=
  value M φ v Fin.elim0

def sentenceValue (φ : L.Sentence) : B :=
  formulaValue M φ Empty.elim

/-- The exact finite-condition witness step needed by direct extraction.
It asserts a positive component, not a component attaining the whole join. -/
theorem exists_positive_witness {n : Nat}
    (φ : L.BoundedFormula α (n + 1)) (v : α → X.Carrier)
    (xs : Fin n → X.Carrier) {p : B}
    (h : p ⊓ value M φ.ex v xs ≠ ⊥) :
    ∃ x : X.Carrier, p ⊓ value M φ v (Fin.snoc xs x) ≠ ⊥ := by
  classical
  by_contra hn
  have hz : ∀ x : X.Carrier, p ⊓ value M φ v (Fin.snoc xs x) = ⊥ := by
    intro x
    by_contra hx
    exact hn ⟨x, hx⟩
  apply h
  rw [value_ex, inf_iSup_eq]
  simp only [hz, iSup_bot]

end Classicism.Meta.ChoiceBoolean.FirstOrderSemantics
