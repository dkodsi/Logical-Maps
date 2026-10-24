import Classicism.Models.BooleanWitnessChain
import Mathlib.Data.Quot

/-!
# An ordinary Mathlib model extracted from the Boolean witness chain

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-model-extraction.md`, sections 4--6
(unpaginated). The carrier is an actual quotient of Nat by secured Boolean
equality of the chain's permanent names. Atomic relations descend by their
proved equality substitution law. The full truth lemma is for Mathlib's
actual `BoundedFormula.Realize`, not an assumed satisfaction predicate.

The input has only Boolean equality and coherent atomic relations. There
is no ordinary-model, maximum-principle, or verdict field. No theorem here
asserts that the separate supported typed hierarchy has been assembled.
-/

noncomputable section

namespace Classicism.Meta.ChoiceBoolean.ModelExtraction

universe u v uL vL

open FirstOrder
open FirstOrderSemantics WitnessChain

variable {B : Type u} [CompleteBooleanAlgebra B]
variable {X : EqualitySpace.{u, v} B}
variable {L : FirstOrder.Language.{uL, vL}} [L.IsRelational] [Countable L.Symbols]
variable (M : FirstOrderSemantics.Structure X L) (p₀ : B) (hp₀ : p₀ ≠ ⊥)

/-- Finite families of secured values have a secured meet. The witnessing
stage is the maximum of their finitely many witnessing stages. -/
theorem secured_iInf {I : Type} [Fintype I] (f : I → B)
    (h : ∀ i, Secured M p₀ hp₀ (f i)) : Secured M p₀ hp₀ (⨅ i, f i) := by
  classical
  choose n hn using h
  refine ⟨Finset.univ.sup n, le_iInf (fun i => ?_)⟩
  exact (stage_condition_antitone M p₀ hp₀
    (Finset.le_sup (Finset.mem_univ i))).trans (hn i)

/-- Secured equality, on indices of actual permanent names. -/
def nameSetoid : Setoid Nat where
  r i j := Secured M p₀ hp₀ (X.eqv (name M p₀ hp₀ i) (name M p₀ hp₀ j))
  iseqv :=
    { refl := by
        intro i
        simpa only [X.refl] using secured_top M p₀ hp₀
      symm := by
        intro i j h
        simpa only [X.symm (name M p₀ hp₀ j) (name M p₀ hp₀ i)] using h
      trans := by
        intro i j k hij hjk
        exact secured_mono M p₀ hp₀ (secured_inf M p₀ hp₀ hij hjk)
          (X.trans (name M p₀ hp₀ i) (name M p₀ hp₀ j) (name M p₀ hp₀ k)) }

abbrev Carrier := Quotient (nameSetoid M p₀ hp₀)

def classOf (i : Nat) : Carrier M p₀ hp₀ := Quotient.mk _ i

instance carrierNonempty : Nonempty (Carrier M p₀ hp₀) := ⟨classOf M p₀ hp₀ 0⟩

theorem classOf_surjective : Function.Surjective (classOf M p₀ hp₀) :=
  Quotient.mk_surjective

instance carrierCountable : Countable (Carrier M p₀ hp₀) :=
  (classOf_surjective M p₀ hp₀).countable

theorem classOf_eq_iff (i j : Nat) :
    classOf M p₀ hp₀ i = classOf M p₀ hp₀ j ↔
      Secured M p₀ hp₀ (X.eqv (name M p₀ hp₀ i) (name M p₀ hp₀ j)) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

def representative (x : Carrier M p₀ hp₀) : Nat := x.out

theorem representative_spec (x : Carrier M p₀ hp₀) :
    classOf M p₀ hp₀ (representative M p₀ hp₀ x) = x := Quotient.out_eq x

/-- Atomic truth is independent of representatives. -/
theorem secured_rel_congr {n : Nat} (r : L.Relations n) (i j : Fin n → Nat)
    (h : ∀ k, Secured M p₀ hp₀
      (X.eqv (name M p₀ hp₀ (i k)) (name M p₀ hp₀ (j k)))) :
    Secured M p₀ hp₀ (M.relMap r (fun k => name M p₀ hp₀ (i k))) ↔
      Secured M p₀ hp₀ (M.relMap r (fun k => name M p₀ hp₀ (j k))) := by
  have he : Secured M p₀ hp₀
      (assignmentEq X (fun k => name M p₀ hp₀ (i k))
        (fun k => name M p₀ hp₀ (j k))) := secured_iInf M p₀ hp₀ _ h
  have he' : Secured M p₀ hp₀
      (assignmentEq X (fun k => name M p₀ hp₀ (j k))
        (fun k => name M p₀ hp₀ (i k))) := by
    apply secured_iInf M p₀ hp₀
    intro k
    simpa only [X.symm (name M p₀ hp₀ (j k)) (name M p₀ hp₀ (i k))] using h k
  constructor
  · intro hr
    exact secured_mono M p₀ hp₀ (secured_inf M p₀ hp₀ he hr) (M.rel_subst r _ _)
  · intro hr
    exact secured_mono M p₀ hp₀ (secured_inf M p₀ hp₀ he' hr) (M.rel_subst r _ _)

def ordinaryRelation {n : Nat} (r : L.Relations n) (xs : Fin n → Carrier M p₀ hp₀) : Prop :=
  Secured M p₀ hp₀
    (M.relMap r (fun i => name M p₀ hp₀ (representative M p₀ hp₀ (xs i))))

theorem ordinaryRelation_classOf {n : Nat} (r : L.Relations n) (i : Fin n → Nat) :
    ordinaryRelation M p₀ hp₀ r (fun k => classOf M p₀ hp₀ (i k)) ↔
      Secured M p₀ hp₀ (M.relMap r (fun k => name M p₀ hp₀ (i k))) := by
  apply secured_rel_congr M p₀ hp₀ r
  intro k
  exact (classOf_eq_iff M p₀ hp₀ _ _).mp
    (representative_spec M p₀ hp₀ (classOf M p₀ hp₀ (i k)))

/-- An actual ordinary structure on the quotient, using Mathlib's class. -/
instance ordinaryStructure : L.Structure (Carrier M p₀ hp₀) where
  funMap f := isEmptyElim f
  RelMap r xs := ordinaryRelation M p₀ hp₀ r xs

theorem term_realize {n : Nat} (t : L.Term (Empty ⊕ Fin n)) (i : Fin n → Nat) :
    t.realize (Sum.elim Empty.elim (fun k => classOf M p₀ hp₀ (i k))) =
      classOf M p₀ hp₀ (termValue (Sum.elim Empty.elim i) t) := by
  cases t with
  | var k => cases k with
    | inl e => exact e.elim
    | inr k => rfl
  | func f _ => exact isEmptyElim f

theorem term_value_name {n : Nat} (t : L.Term (Empty ⊕ Fin n)) (i : Fin n → Nat) :
    termValue (Sum.elim Empty.elim (fun k => name M p₀ hp₀ (i k))) t =
      name M p₀ hp₀ (termValue (Sum.elim Empty.elim i) t) := by
  cases t with
  | var k => cases k with
    | inl e => exact e.elim
    | inr k => rfl
  | func f _ => exact isEmptyElim f

private theorem map_snoc {D : Type v} (f : Nat → D) {n : Nat} (i : Fin n → Nat) (j : Nat) :
    (fun k : Fin (n + 1) => f (Fin.snoc (α := fun _ => Nat) i j k)) =
      Fin.snoc (α := fun _ : Fin (n + 1) => D) (fun k => f (i k)) (f j) :=
  Fin.comp_snoc f i j

/-- On decided antecedents, Boolean implication becomes ordinary implication. -/
theorem secured_himp_iff (a b : B)
    (hdec : Secured M p₀ hp₀ a ∨ Secured M p₀ hp₀ aᶜ) :
    Secured M p₀ hp₀ (a ⇨ b) ↔ (Secured M p₀ hp₀ a → Secured M p₀ hp₀ b) := by
  constructor
  · intro hab ha
    exact secured_mono M p₀ hp₀ (secured_inf M p₀ hp₀ hab ha) himp_inf_le
  · intro h
    rcases hdec with ha | ha
    · exact secured_mono M p₀ hp₀ (h ha) le_himp
    · apply secured_mono M p₀ hp₀ ha
      rw [le_himp_iff]
      exact compl_inf_eq_bot.le.trans bot_le

/-- The full truth lemma for actual Mathlib bounded-formula satisfaction. -/
theorem realize_iff_secured : ∀ {n : Nat} (φ : L.BoundedFormula Empty n) (i : Fin n → Nat),
    φ.Realize Empty.elim (fun k => classOf M p₀ hp₀ (i k)) ↔
      Secured M p₀ hp₀ (value M φ Empty.elim (fun k => name M p₀ hp₀ (i k))) := by
  intro n φ
  induction φ with
  | falsum =>
      intro i
      change False ↔ Secured M p₀ hp₀ ⊥
      exact ⟨False.elim, not_secured_bot M p₀ hp₀⟩
  | equal t s =>
      intro i
      change t.realize (Sum.elim Empty.elim (fun k => classOf M p₀ hp₀ (i k))) =
          s.realize (Sum.elim Empty.elim (fun k => classOf M p₀ hp₀ (i k))) ↔
        Secured M p₀ hp₀ (X.eqv
          (termValue (Sum.elim Empty.elim (fun k => name M p₀ hp₀ (i k))) t)
          (termValue (Sum.elim Empty.elim (fun k => name M p₀ hp₀ (i k))) s))
      rw [term_realize, term_realize, term_value_name, term_value_name]
      exact classOf_eq_iff M p₀ hp₀ _ _
  | rel r ts =>
      intro i
      change ordinaryRelation M p₀ hp₀ r
          (fun k => (ts k).realize (Sum.elim Empty.elim (fun j => classOf M p₀ hp₀ (i j)))) ↔
        Secured M p₀ hp₀ (M.relMap r
          (fun k => termValue (Sum.elim Empty.elim (fun j => name M p₀ hp₀ (i j))) (ts k)))
      simp only [term_realize, term_value_name]
      exact ordinaryRelation_classOf M p₀ hp₀ r _
  | imp φ ψ ihφ ihψ =>
      intro i
      change (φ.Realize Empty.elim (fun k => classOf M p₀ hp₀ (i k)) →
          ψ.Realize Empty.elim (fun k => classOf M p₀ hp₀ (i k))) ↔
        Secured M p₀ hp₀ (value M φ Empty.elim (fun k => name M p₀ hp₀ (i k)) ⇨
          value M ψ Empty.elim (fun k => name M p₀ hp₀ (i k)))
      rw [ihφ i, ihψ i]
      exact (secured_himp_iff M p₀ hp₀ _ _ (eventual_decision M p₀ hp₀ φ i)).symm
  | all φ ih =>
      intro i
      change (∀ x : Carrier M p₀ hp₀,
          φ.Realize Empty.elim (Fin.snoc (fun k => classOf M p₀ hp₀ (i k)) x)) ↔
        Secured M p₀ hp₀ (value M (.all φ) Empty.elim (fun k => name M p₀ hp₀ (i k)))
      constructor
      · intro hall
        classical
        by_contra hn
        have hneg : Secured M p₀ hp₀
            (value M (.all φ) Empty.elim (fun k => name M p₀ hp₀ (i k)))ᶜ :=
          (eventual_decision M p₀ hp₀ (.all φ) i).resolve_left hn
        obtain ⟨j, hj⟩ := secured_not_all_witness M p₀ hp₀ φ i hneg
        have hi := ih (Fin.snoc i j)
        simp only [map_snoc] at hi
        exact secured_not_both M p₀ hp₀ (hi.mp (hall (classOf M p₀ hp₀ j))) hj
      · intro hall x
        obtain ⟨j, rfl⟩ := classOf_surjective M p₀ hp₀ x
        have hi := ih (Fin.snoc i j)
        simp only [map_snoc] at hi
        apply hi.mpr
        exact secured_mono M p₀ hp₀ hall
          (iInf_le (fun y => value M φ Empty.elim
            (Fin.snoc (fun k => name M p₀ hp₀ (i k)) y)) (name M p₀ hp₀ j))

theorem sentence_iff_secured (φ : L.Sentence) :
    Carrier M p₀ hp₀ ⊨ φ ↔ Secured M p₀ hp₀ (sentenceValue M φ) := by
  have hvals (v : Empty → Carrier M p₀ hp₀) (xs : Fin 0 → Carrier M p₀ hp₀) :
      FirstOrder.Language.BoundedFormula.Realize φ v xs ↔
        Secured M p₀ hp₀ (sentenceValue M φ) := by
    rw [show v = Empty.elim from Subsingleton.elim _ _]
    rw [show xs = (fun k => classOf M p₀ hp₀ (Fin.elim0 k))
      from Subsingleton.elim _ _]
    have h := realize_iff_secured M p₀ hp₀ φ (Fin.elim0 : Fin 0 → Nat)
    simpa only [sentenceValue, formulaValue,
      show (fun k : Fin 0 => name M p₀ hp₀ (Fin.elim0 k)) = Fin.elim0
        from Subsingleton.elim _ _] using h
  unfold FirstOrder.Language.Sentence.Realize FirstOrder.Language.Formula.Realize
  exact hvals _ _

/-- Every sentence above the specified initial nonzero condition transfers. -/
theorem sentence_transfer (φ : L.Sentence) (h : p₀ ≤ sentenceValue M φ) :
    Carrier M p₀ hp₀ ⊨ φ :=
  (sentence_iff_secured M p₀ hp₀ φ).mpr
    (secured_mono M p₀ hp₀ (secured_initial M p₀ hp₀) h)

theorem sentence_transfer_one (φ : L.Sentence) (h : sentenceValue M φ = ⊤) :
    Carrier M p₀ hp₀ ⊨ φ :=
  sentence_transfer M p₀ hp₀ φ (h.symm ▸ le_top)

/-- An actual Mathlib theory-model proof, obtained from proved Boolean values. -/
theorem models_of_values_one (T : L.Theory)
    (h : ∀ φ ∈ T, sentenceValue M φ = ⊤) : Carrier M p₀ hp₀ ⊨ T :=
  ⟨fun φ hφ => sentence_transfer_one M p₀ hp₀ φ (h φ hφ)⟩

end Classicism.Meta.ChoiceBoolean.ModelExtraction
