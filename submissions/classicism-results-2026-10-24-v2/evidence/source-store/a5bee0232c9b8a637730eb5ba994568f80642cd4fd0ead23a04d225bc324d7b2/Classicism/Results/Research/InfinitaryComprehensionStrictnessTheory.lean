import Classicism.Results.Research.InfinitaryComprehensionStrictness
import Classicism.Models.ChoiceFirstOrderAxiomTheory

/-!
# The actual finite axiom theory in the elementary reduct

Original metatheoretic formalization (misc, 23 October 2026) of
`research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md`,
Theorem 5.1 (unpaginated).

We identify each recovered sort in the tagged full hierarchy with its
original full domain, transport the genuine application predicates, and
construct every arbitrary relational profile. This proves the actual
first-order axiom theory, including every finite comprehension instance,
in the ambient structure. Elementarity then transfers that theory to
every elementary reduct. No model-existence or comprehension premise is
assumed by `ambient_theory` or `reduct_theory`.
-/

namespace Classicism.Research.InfinitaryComprehension.Strictness

open Classicism.Meta
open Classicism.Meta.ChoiceFirstOrder
open Classicism.Meta.ChoiceFirstOrder.MathlibBridge

/-- Recovering a sort from the tagged full structure preserves its entire
original carrier; the proof is a literal dependent-pair equivalence. -/
def sortEquiv (σ : Ty) : Full.Dom Nat σ ≃ Recovery.D Ambient σ where
  toFun x := ⟨⟨σ, x⟩, rfl⟩
  invFun := by
    rintro ⟨⟨τ, x⟩, h⟩
    change τ = σ at h
    subst τ
    exact x
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨τ, x⟩, h⟩
    change τ = σ at h
    subst τ
    rfl

def recoverArgs (ρ : RTy) (a : Args (Full.Dom Nat) ρ) :
    Args (Recovery.D Ambient) ρ :=
  mapArgs (fun σ => sortEquiv σ) ρ a

def forgetArgs (ρ : RTy) (a : Args (Recovery.D Ambient) ρ) :
    Args (Full.Dom Nat) ρ :=
  mapArgs (fun σ => (sortEquiv σ).symm) ρ a

theorem recover_forget_args : ∀ (ρ : RTy) (a : Args (Recovery.D Ambient) ρ),
    recoverArgs ρ (forgetArgs ρ a) = a
  | .t, a => by cases a; rfl
  | .arr σ ρ, a => by
    change ((sortEquiv σ) ((sortEquiv σ).symm a.1),
      recoverArgs ρ (forgetArgs ρ a.2)) = a
    exact Prod.ext ((sortEquiv σ).apply_symm_apply
      (show Recovery.D Ambient σ from a.1)) (recover_forget_args ρ a.2)

theorem flatten_recoverArgs : ∀ (ρ : RTy) (a : Args (Full.Dom Nat) ρ),
    flatten (fun σ (x : Recovery.D Ambient σ) => x.val) ρ (recoverArgs ρ a) =
      flatten (fun σ x => (⟨σ, x⟩ : Ambient)) ρ a
  | .t, _ => rfl
  | .arr σ ρ, a => by
    change Fin.cons (α := fun _ => Ambient) (⟨σ, a.1⟩ : Ambient)
      (flatten (fun τ (x : Recovery.D Ambient τ) => x.val) ρ (recoverArgs ρ a.2)) =
      Fin.cons (α := fun _ => Ambient) (⟨σ, a.1⟩ : Ambient)
        (flatten (fun τ x => (⟨τ, x⟩ : Ambient)) ρ a.2)
    rw [flatten_recoverArgs ρ a.2]

/-- The guarded relational application agrees with the original full
hierarchy after the explicit sort and argument equivalences. -/
theorem recovered_profile (ρ : RTy) (X : Full.Dom Nat (.rel ρ))
    (a : Args (Full.Dom Nat) ρ) :
    Recovery.rel Ambient ρ (sortEquiv (.rel ρ) X) (recoverArgs ρ a) ↔
      ambient.rel ρ X a := by
  unfold Recovery.rel
  change FirstOrder.Language.Structure.RelMap (L := language) (Relation.profile ρ)
    (Fin.cons (⟨.rel ρ, X⟩ : Ambient)
      (flatten (fun σ (x : Recovery.D Ambient σ) => x.val) ρ (recoverArgs ρ a))) ↔ _
  rw [flatten_recoverArgs]
  exact profile_correct ambient ρ X a

theorem recovered_full_extensionality (ρ : RTy) :
    Function.Injective (Recovery.rel Ambient ρ) := by
  intro X Y hXY
  apply (sortEquiv (.rel ρ)).symm.injective
  apply ambient.rel_injective ρ
  funext a
  have hx := recovered_profile ρ ((sortEquiv (.rel ρ)).symm X) a
  have hy := recovered_profile ρ ((sortEquiv (.rel ρ)).symm Y) a
  rw [Equiv.apply_symm_apply] at hx hy
  exact propext (hx.symm.trans
    ((Iff.of_eq (congrFun hXY (recoverArgs ρ a))).trans hy))

/-- Every arbitrary support is represented in the recovered ambient sort.
The witness is an actual subset in the original full hierarchy. -/
theorem recovered_full_profiles (ρ : RTy)
    (P : Args (Recovery.D Ambient) ρ → Prop) :
    ∃ X : Recovery.D Ambient (.rel ρ), ∀ a, Recovery.rel Ambient ρ X a ↔ P a := by
  let X : Full.Dom Nat (.rel ρ) :=
    {a | P (recoverArgs ρ (Full.fromTuple Nat ρ a))}
  refine ⟨sortEquiv (.rel ρ) X, ?_⟩
  intro a
  have hp := recovered_profile ρ X (forgetArgs ρ a)
  rw [recover_forget_args] at hp
  have hX : ambient.rel ρ X (forgetArgs ρ a) ↔ P a := by
    change P (recoverArgs ρ (Full.fromTuple Nat ρ
      (Full.toTuple Nat ρ (forgetArgs ρ a)))) ↔ P a
    rw [Full.from_to, recover_forget_args]
  exact hp.trans hX

/-- The full tagged hierarchy satisfies the displayed sentence theory,
including every actual finite-context comprehension axiom. -/
theorem ambient_theory :
    FirstOrder.Language.Theory.Model Ambient AxiomTheory.theory := by
  constructor
  intro φ hφ
  obtain ⟨i, rfl⟩ := hφ
  cases i with
  | inl u =>
      cases u
      apply (AxiomTheory.nonempty_sentence_correct Ambient).2
      exact ⟨sortEquiv .e 0⟩
  | inr i =>
      cases i with
      | inl ρ =>
          exact (AxiomTheory.extensionality_sentence_correct Ambient ρ).2
            (recovered_full_extensionality ρ)
      | inr i =>
          rcases i with ⟨Γ, ρ, A⟩
          apply (AxiomTheory.comprehension_sentence_correct Ambient Γ ρ A).2
          intro g
          exact recovered_full_profiles ρ (fun a =>
            Recovery.RawRealize Ambient A (appendEnv (argsEnv ρ a) g))

/-- The promised assumption-free axiom certificate for every actual
elementary substructure constructed by downward Löwenheim--Skolem. -/
theorem reduct_theory (S : ElementaryReduct) :
    FirstOrder.Language.Theory.Model S AxiomTheory.theory :=
  (S.theory_model_iff AxiomTheory.theory).2 ambient_theory

#print axioms recovered_full_profiles
#print axioms ambient_theory
#print axioms reduct_theory

end Classicism.Research.InfinitaryComprehension.Strictness
