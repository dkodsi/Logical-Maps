import Classicism.Models.BooleanTaggedFirstOrder
import Classicism.Models.BooleanModelExtraction
import Classicism.Models.ChoiceFirstOrderAxiomTheory

/-!
# The explicit Henkin theory in the constructed Boolean hierarchy

Original formalization (misc), 23 October 2026, of sections 4 and 9 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
The actual individual-existence, extensionality and comprehension sentences
of `MathlibBridge.AxiomTheory` have Boolean value one. Countable extraction
therefore supplies an ordinary model of that exact theory, and its existing
recovery supplies an actual C-model. No comprehension or model-existence
certificate is assumed. Choice verdicts are separate downstream sentences.
-/

namespace Classicism.Meta.ChoiceBoolean.BooleanAxiomTheory

open ChoiceFirstOrder ChoiceFirstOrder.MathlibBridge
open ChoiceFirstOrder.MathlibBridge.AxiomTheory
open TypedHierarchy SmallFormulaSemantics

variable {K B : Type} [CompleteBooleanAlgebra B]
variable (a : BooleanAction K B) (E : Type)

noncomputable section

local instance language_relational : language.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

theorem value_imp {Γ : Ctx} (p q : SmallFormula Γ) (g : IEnv (Dom a E) Γ) :
    smallValue a E (smallImp p q) g = (smallValue a E p g ⇨ smallValue a E q g) := by
  simp only [smallImp, smallValue, himp_eq, sup_comm]

theorem value_iff {Γ : Ctx} (p q : SmallFormula Γ) (g : IEnv (Dom a E) Γ) :
    smallValue a E (smallIff p q) g = iffValue (smallValue a E p g) (smallValue a E q g) := by
  change smallValue a E (smallImp p q) g ⊓ smallValue a E (smallImp q p) g = _
  rw [value_imp, value_imp] <;> rfl

theorem value_allOne (σ : Ty) {Γ : Ctx} (φ : SmallFormula (σ :: Γ))
    (g : IEnv (Dom a E) Γ) :
    smallValue a E (allOne σ φ) g = ⨅ x : Dom a E σ, smallValue a E φ (.cons x g) := by
  change (⨅ p : Dom a E σ × PUnit, smallValue a E φ (.cons p.1 g)) = _
  apply le_antisymm
  · apply le_iInf
    intro x
    exact iInf_le _ (x, PUnit.unit)
  · apply le_iInf
    intro p
    exact iInf_le _ p.1

theorem value_exOne (σ : Ty) {Γ : Ctx} (φ : SmallFormula (σ :: Γ))
    (g : IEnv (Dom a E) Γ) :
    smallValue a E (exOne σ φ) g = ⨆ x : Dom a E σ, smallValue a E φ (.cons x g) := by
  change (⨆ p : Dom a E σ × PUnit, smallValue a E φ (.cons p.1 g)) = _
  apply le_antisymm
  · apply iSup_le
    intro p
    exact le_iSup (fun x : Dom a E σ => smallValue a E φ (IEnv.cons x g)) p.1
  · apply iSup_le
    intro x
    exact le_iSup
      (fun p : Dom a E σ × PUnit => smallValue a E φ (IEnv.cons p.1 g))
      (x, PUnit.unit)

theorem value_allContext : ∀ (Γ : Ctx) (φ : SmallFormula Γ),
    smallValue a E (allContext Γ φ) .nil =
      ⨅ g : IEnv (Dom a E) Γ, smallValue a E φ g
  | [], φ => by
    apply le_antisymm
    · apply le_iInf
      intro g
      cases g
      exact le_rfl
    · exact iInf_le (fun g : IEnv (Dom a E) [] => smallValue a E φ g) IEnv.nil
  | σ :: Γ, φ => by
    rw [allContext, value_allContext Γ]
    calc
      _ = ⨅ g : IEnv (Dom a E) Γ, ⨅ x : Dom a E σ,
          smallValue a E φ (.cons x g) := by
        apply iInf_congr
        intro g
        exact value_allOne a E σ φ g
      _ = _ := by
        apply le_antisymm
        · apply le_iInf
          intro g
          cases g with
          | cons x g => exact (iInf_le _ g).trans (iInf_le _ x)
        · apply le_iInf
          intro g
          apply le_iInf
          intro x
          exact iInf_le
            (fun h : IEnv (Dom a E) (σ :: Γ) => smallValue a E φ h) (IEnv.cons x g)

theorem value_rename : ∀ {Γ Δ : Ctx} (φ : SmallFormula Γ)
    (r : ∀ σ, Var Γ σ → Var Δ σ) (g : IEnv (Dom a E) Γ) (h : IEnv (Dom a E) Δ),
    (∀ σ v, h.get (r σ v) = g.get v) →
    smallValue a E (rename r φ) h = smallValue a E φ g
  | _, _, .equal x y, r, g, h, hg => by
    change (DomSpace a E _).space.eqv (h.get (r _ x)) (h.get (r _ y)) = _
    rw [hg, hg] <;> rfl
  | _, _, .rel ρ x xs, r, g, h, hg => by
    change profile a E ρ (h.get (r _ x))
      (mapArgs (fun _ v => h.get v) ρ (mapArgs r ρ xs)) = _
    rw [mapArgs_comp, hg]
    have hv : (fun σ v => h.get (r σ v)) = (fun σ v => g.get v) := by
      funext σ v
      exact hg σ v
    rw [hv] <;> rfl
  | _, _, .falsum, _, _, _, _ => rfl
  | _, _, .neg p, r, g, h, hg => congrArg (fun b : B => bᶜ) (value_rename p r g h hg)
  | _, _, .conj p q, r, g, h, hg =>
      congrArg₂ (fun b c : B => b ⊓ c) (value_rename p r g h hg) (value_rename q r g h hg)
  | _, _, .disj p q, r, g, h, hg =>
      congrArg₂ (fun b c : B => b ⊔ c) (value_rename p r g h hg) (value_rename q r g h hg)
  | _, _, .all ρ p, r, g, h, hg => by
    apply iInf_congr
    intro xs
    exact value_rename p (liftMany r ρ.args)
      (appendEnv (argsEnv ρ xs) g) (appendEnv (argsEnv ρ xs) h)
      (get_liftMany r g h hg (argsEnv ρ xs))
  | _, _, .ex ρ p, r, g, h, hg => by
    apply iSup_congr
    intro xs
    exact value_rename p (liftMany r ρ.args)
      (appendEnv (argsEnv ρ xs) g) (appendEnv (argsEnv ρ xs) h)
      (get_liftMany r g h hg (argsEnv ρ xs))

theorem value_profile_prefix {Γ : Ctx} (ρ : RTy) (v : Var Γ (.rel ρ))
    (xs : Args (Dom a E) ρ) (g : IEnv (Dom a E) Γ) :
    smallValue a E (.rel ρ (rightVar ρ.args v) (prefixArgs Γ ρ))
      (appendEnv (argsEnv ρ xs) g) = profile a E ρ (g.get v) xs := by
  change profile a E ρ ((appendEnv (argsEnv ρ xs) g).get (rightVar ρ.args v))
    (mapArgs (fun _ v => (appendEnv (argsEnv ρ xs) g).get v) ρ (prefixArgs Γ ρ)) = _
  rw [get_append_right, eval_prefixArgs]

theorem value_insertWitness {Γ : Ctx} (ρ : RTy)
    (φ : SmallFormula (ρ.args ++ Γ)) (F : Dom a E (.rel ρ))
    (xs : Args (Dom a E) ρ) (g : IEnv (Dom a E) Γ) :
    smallValue a E (insertWitness ρ φ) (appendEnv (argsEnv ρ xs) (.cons F g)) =
      smallValue a E φ (appendEnv (argsEnv ρ xs) g) :=
  value_rename a E φ (liftMany (fun _ v => Var.succ v) ρ.args)
    (appendEnv (argsEnv ρ xs) g) (appendEnv (argsEnv ρ xs) (.cons F g))
    (get_liftMany (fun _ v => Var.succ v) g (.cons F g)
      (fun _ _ => rfl) (argsEnv ρ xs))

theorem nonempty_value (hE : Nonempty E) : smallValue a E nonemptySmall .nil = ⊤ := by
  rw [nonemptySmall, value_exOne]
  obtain ⟨x⟩ := hE
  apply top_le_iff.mp
  exact le_iSup_of_le x (by simp [smallTrue, smallValue])

theorem extensionality_value (ρ : RTy) : smallValue a E (extensionalitySmall ρ) .nil = ⊤ := by
  rw [extensionalitySmall, value_allContext]
  apply top_le_iff.mp
  apply le_iInf
  intro g
  cases g with
  | cons F g =>
    cases g with
    | cons H g =>
      cases g
      rw [extBody, value_imp]
      have he : smallValue a E
          (.all ρ (smallIff
            (.rel ρ (rightVar ρ.args Var.zero) (prefixArgs [.rel ρ, .rel ρ] ρ))
            (.rel ρ (rightVar ρ.args (Var.succ Var.zero)) (prefixArgs [.rel ρ, .rel ρ] ρ))))
          (.cons F (.cons H .nil)) = (DomSpace a E (.rel ρ)).space.eqv F H := by
        rw [profile_eqv]
        apply iInf_congr
        intro xs
        rw [value_iff, value_profile_prefix, value_profile_prefix] <;> rfl
      rw [he]
      change ⊤ ≤ (DomSpace a E (.rel ρ)).space.eqv F H ⇨ (DomSpace a E (.rel ρ)).space.eqv F H
      simp

theorem comprehension_value (Γ : Ctx) (ρ : RTy) (φ : SmallFormula (ρ.args ++ Γ)) :
    smallValue a E (comprehensionSmall Γ ρ φ) .nil = ⊤ := by
  rw [comprehensionSmall, value_allContext]
  apply top_le_iff.mp
  apply le_iInf
  intro g
  obtain ⟨F, hF⟩ := small_comprehension a E Γ ρ φ g
  rw [comprehensionBody, value_exOne]
  apply le_iSup_of_le F
  apply le_iInf
  intro xs
  rw [value_iff, value_profile_prefix, value_insertWitness]
  change ⊤ ≤ iffValue (profile a E ρ F xs)
    (smallValue a E φ (appendEnv (argsEnv ρ xs) g))
  rw [hF xs, iffValue_refl]

theorem axioms_value_one (hE : Nonempty E) (i : AxiomIndex) :
    FirstOrderSemantics.sentenceValue (TaggedFirstOrder.booleanStructure a E hE)
      (axiomSentence i) = ⊤ := by
  rw [axiomSentence, TaggedFirstOrder.sentence_value]
  rcases i with u | ρ | ⟨Γ, ρ, φ⟩
  · exact nonempty_value a E hE
  · exact extensionality_value a E ρ
  · exact comprehension_value a E Γ ρ φ

theorem theory_value_one (hE : Nonempty E) :
    ∀ φ ∈ theory, FirstOrderSemantics.sentenceValue
      (TaggedFirstOrder.booleanStructure a E hE) φ = ⊤ := by
  rintro φ ⟨i, rfl⟩
  exact axioms_value_one a E hE i

/-- A concrete countable extracted model of the displayed first-order theory. -/
theorem extracted_theory (hE : Nonempty E) (p₀ : B) (hp₀ : p₀ ≠ ⊥) :
    letI : Countable language.Symbols := language_countable
    FirstOrder.Language.Theory.Model
      (ModelExtraction.Carrier (TaggedFirstOrder.booleanStructure a E hE) p₀ hp₀) theory := by
  letI : Countable language.Symbols := language_countable
  exact ModelExtraction.models_of_values_one (TaggedFirstOrder.booleanStructure a E hE)
    p₀ hp₀ theory (theory_value_one a E hE)

end

end Classicism.Meta.ChoiceBoolean.BooleanAxiomTheory
