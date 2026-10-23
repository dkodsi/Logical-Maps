import Classicism.Semantics.BooleanValuedSoundness

/-!
# Crisp identity, complete meets and explicit ND/BF formulas

Ordinary model metatheory. The formulas below are literal finite terms in the
existing object syntax. Their implication directions agree with
Principles/Coarse.lean. They are not generated schema identifiers and are not
claims that ND or BF is a theorem of C.

Source: full-boolean-valued-atom-and-atomless.md §3 (unpaginated); construction
provenance appears in BooleanValued.lean. New formalization (misc).
-/

namespace Classicism.Meta.BooleanValued
noncomputable section

variable {Sig : Signature} {B : Type} [CompleteBooleanAlgebra B]

/-- Meets of crisp tests for top give the crisp test for the meet being top. -/
theorem crisp_iInf {A : Type} (F : A → B) :
    (⨅ x, (crisp (F x) (⊤ : B) : B)) = crisp (⨅ x, F x) (⊤ : B) := by
  classical
  by_cases h : ∀ x, F x = ⊤
  · have hf : F = fun _ => ⊤ := funext h
    rw [hf]
    simp
  · obtain ⟨x, hx⟩ := not_forall.mp h
    have hm : (⨅ y, F y) ≠ ⊤ := by
      intro he
      have hl : (⊤ : B) ≤ F x := by
        rw [← he]
        exact iInf_le F x
      exact hx (le_antisymm le_top hl)
    rw [crisp_of_ne hm]
    apply le_antisymm _ bot_le
    calc
      (⨅ y, (crisp (F y) (⊤ : B) : B)) ≤ crisp (F x) (⊤ : B) := iInf_le _ x
      _ = ⊥ := crisp_of_ne hx

theorem crisp_crisp [Nontrivial B] {A : Type} (x y : A) :
    (crisp (crisp x y : B) (⊤ : B) : B) = crisp x y := by
  classical
  by_cases h : x = y <;> simp [crisp, h]

theorem crisp_neg_crisp [Nontrivial B] {A : Type} (x y : A) :
    (crisp ((crisp x y : B)ᶜ) (⊤ : B) : B) = (crisp x y : B)ᶜ := by
  classical
  by_cases h : x = y <;> simp [crisp, h]

/-- `∀xy : σ, x ≠ y → □(x ≠ y)` in the fixed relational syntax. -/
def distinctnessSentence (σ : Ty) : Sentence Sig :=
  Term.forall' (σ := σ) (Term.forall' (σ := σ)
    (Term.imp (Term.neg (Term.eq' Term.v1 Term.v0))
      (Term.box (Term.neg (Term.eq' Term.v1 Term.v0)))))

/-- `∀X : σ→t, (∀x, □Xx) → □∀x, Xx`. -/
def barcanSentence (σ : Ty) : Sentence Sig :=
  Term.forall' (σ := σ ⇒ RTy.t)
    (Term.imp
      (Term.forall' (σ := σ) (Term.box (Term.app Term.v1 Term.v0)))
      (Term.box (Term.app (Term.all σ) Term.v0)))

/-- `∀X : σ→t, □∀x, Xx → ∀x, □Xx`. -/
def converseBarcanSentence (σ : Ty) : Sentence Sig :=
  Term.forall' (σ := σ ⇒ RTy.t)
    (Term.imp
      (Term.box (Term.app (Term.all σ) Term.v0))
      (Term.forall' (σ := σ) (Term.box (Term.app Term.v1 Term.v0))))

theorem distinctness_value (I : Interpretation Sig B) [Nontrivial B] (σ : Ty) :
    eval I (distinctnessSentence σ) .nil = ⊤ := by
  change (⨅ x : Dom I.E B σ, ⨅ y : Dom I.E B σ,
    ((crisp x y : B)ᶜ)ᶜ ⊔ crisp ((crisp x y : B)ᶜ) (topValue : B)) = ⊤
  simp only [topValue_eq_top, crisp_neg_crisp]
  simp

theorem barcan_value (I : Interpretation Sig B) (σ : Ty) :
    eval I (barcanSentence σ) .nil = ⊤ := by
  change (⨅ F : Dom I.E B σ → B,
    (⨅ x, (crisp (F x) (topValue : B) : B))ᶜ ⊔
      crisp (⨅ x, F x) (topValue : B)) = ⊤
  simp only [topValue_eq_top, crisp_iInf]
  simp

theorem converseBarcan_value (I : Interpretation Sig B) (σ : Ty) :
    eval I (converseBarcanSentence σ) .nil = ⊤ := by
  change (⨅ F : Dom I.E B σ → B,
    (crisp (⨅ x, F x) (topValue : B) : B)ᶜ ⊔
      (⨅ x, (crisp (F x) (topValue : B) : B))) = ⊤
  simp only [topValue_eq_top, crisp_iInf]
  simp

theorem boxed_distinctness_value (I : Interpretation Sig B) [Nontrivial B] (σ : Ty) :
    eval I (Term.box (distinctnessSentence σ)) .nil = ⊤ := by
  rw [eval_box, distinctness_value, crisp_self]

theorem boxed_barcan_value (I : Interpretation Sig B) (σ : Ty) :
    eval I (Term.box (barcanSentence σ)) .nil = ⊤ := by
  rw [eval_box, barcan_value, crisp_self]

theorem boxed_converseBarcan_value (I : Interpretation Sig B) (σ : Ty) :
    eval I (Term.box (converseBarcanSentence σ)) .nil = ⊤ := by
  rw [eval_box, converseBarcan_value, crisp_self]

end
end Classicism.Meta.BooleanValued
