import Classicism.Models.CoalescedInternalHierarchy

/-!
# Admission of arbitrary finite internal relation definitions

Original formalization (misc), 23 October 2026. A finite formula in the raw
membership-and-pairing language may quantify over the entire membership
universe. Its free argument variables are interpreted in their typed domains,
but its internal quantifiers are not required to be bounded by those domains.
Separation on the tuple-code set admits exactly the resulting relation.
-/

namespace Classicism.Meta.CoalescedInternalHierarchy

open ChoiceFirstOrder

variable (U : Universe)

abbrev eraseArgs (ρ : RTy) (a : Args (D U) ρ) : RawEnv U.Carrier ρ.args :=
  eraseEnv U (argsEnv ρ a)

/-- The existential decoder relates the separated element to the finite
tuple of arguments before evaluating the original raw formula. -/
def rawComprehensionBody (Γ : Ctx) (ρ : RTy)
    (φ : RawFormula U.Carrier (ρ.args ++ Γ)) :
    RawFormula U.Carrier (ρ.args ++ .e :: Γ) :=
  .conj (.equal (tupleTerm U ρ (prefixVars (.e :: Γ) ρ))
    (.var (rightVar ρ.args .zero)))
    (φ.rename (insertRen .e ρ.args))

def rawComprehensionFormula (Γ : Ctx) (ρ : RTy)
    (φ : RawFormula U.Carrier (ρ.args ++ Γ)) : RawFormula U.Carrier (.e :: Γ) :=
  exBlock U ρ (rawComprehensionBody U Γ ρ φ)

theorem rawComprehensionBody_correct (Γ : Ctx) (ρ : RTy)
    (φ : RawFormula U.Carrier (ρ.args ++ Γ)) (g : RawEnv U.Carrier Γ)
    (x : U.Carrier) (a : Args (D U) ρ) :
    (rawComprehensionBody U Γ ρ φ).Realize U.mem U.pair
      (appendEnv (eraseArgs U ρ a) (.cons x g)) ↔
    encode U ρ a = x ∧ φ.Realize U.mem U.pair (appendEnv (eraseArgs U ρ a) g) := by
  simp only [rawComprehensionBody, eraseArgs, RawFormula.Realize, RawTerm.eval]
  rw [tupleTerm_prefix_eval, get_append_right]
  apply and_congr Iff.rfl
  exact RawFormula.realize_rename U.mem U.pair φ (insertRen .e ρ.args)
    (appendEnv (eraseArgs U ρ a) g) (appendEnv (eraseArgs U ρ a) (.cons x g))
    (get_insertRen .e x g (eraseArgs U ρ a))

theorem rawComprehensionFormula_correct (Γ : Ctx) (ρ : RTy)
    (φ : RawFormula U.Carrier (ρ.args ++ Γ)) (g : RawEnv U.Carrier Γ)
    (x : U.Carrier) :
    (rawComprehensionFormula U Γ ρ φ).Realize U.mem U.pair (.cons x g) ↔
      ∃ a : Args (D U) ρ, encode U ρ a = x ∧
        φ.Realize U.mem U.pair (appendEnv (eraseArgs U ρ a) g) := by
  rw [rawComprehensionFormula, realize_exBlock]
  apply exists_congr
  intro a
  exact rawComprehensionBody_correct U Γ ρ φ g x a

/-- Actual admission for every externally finite raw formula. Quantifiers
inside `φ` retain their unrestricted membership-universe semantics. -/
theorem rawComprehension (Γ : Ctx) (ρ : RTy)
    (φ : RawFormula U.Carrier (ρ.args ++ Γ)) (g : RawEnv U.Carrier Γ) :
    ∃ X : D U (.rel ρ), ∀ a : Args (D U) ρ,
      rel U ρ X a ↔ φ.Realize U.mem U.pair (appendEnv (eraseArgs U ρ a) g) := by
  obtain ⟨B, hB⟩ := U.separation Γ (rawComprehensionFormula U Γ ρ φ) g (tupleCode U ρ)
  have hpower : U.mem B (U.power (tupleCode U ρ)) := by
    apply (U.power_mem _ _).mpr
    intro x hx
    exact ((hB x).mp hx).1
  refine ⟨⟨B, hpower⟩, ?_⟩
  intro a
  change U.mem (encode U ρ a) B ↔ _
  rw [hB, rawComprehensionFormula_correct]
  constructor
  · rintro ⟨_, b, hb, hφ⟩
    have he := encode_injective U ρ hb
    exact he ▸ hφ
  · intro hφ
    exact ⟨encode_mem U ρ a, a, rfl, hφ⟩

#print axioms rawComprehension

end Classicism.Meta.CoalescedInternalHierarchy
