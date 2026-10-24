import Classicism.Results.Research.InfinitaryComprehensionFormation
import Classicism.Results.Research.InfinitaryComprehensionActionConsequences

/-!
# Closure and Comprehension only for the original object types

Source: Infinitary Comprehension, sections 1 and 4 (misc, original research,
23 October 2026, unpaginated). These premises concern only closed object
sorts actually occurring in the matrix and its finite argument context.
Unused entries of the parameter family impose no extra premise. The profile
witness below is extracted from the actual existential/boxed formula; it
is not a representation assumption. Source-only, awaiting compilation.
-/

namespace Classicism.Research.InfinitaryComprehension.Canonical

open Classicism.Meta Classicism.Meta.Intensional CategoryTheory Formation

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C)

def GroundClosed : Prop :=
  ∀ {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) {Γ σ W}
    (h : A.W₀ ⟶ W) (p : ITerm Param Γ σ) (g : IEnv (A.Dom W) Γ),
    ContextClosed Γ → formed p →
    ∃ a : A.Dom W σ, A.Incl σ W a = sem A η h p g

def GroundComp : Prop :=
  ∀ {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) {Γ}
    (p : ITerm Param Γ Ty.t), ContextClosed Γ → formed p →
      Holds A η (𝟙 A.W₀) p.comprehension .nil

theorem Closed.ground (hc : Closed A) : GroundClosed A := by
  intro Param η Γ σ W h p g _ _
  exact hc η h p g

theorem Comprehension.ground (hcomp : Comprehension A) : GroundComp A := by
  intro Param η Γ p _ _
  exact hcomp η p

/-- The box truth clause needs closure only for this particular matrix. -/
theorem ground_holds_box {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    (hc : GroundClosed A) {Γ W} (h : A.W₀ ⟶ W) (p : ITerm Param Γ Ty.t)
    (g : IEnv (A.Dom W) Γ) (hΓ : ContextClosed Γ) (hp : formed p) :
    Holds A η h p.box g ↔ ∀ z : Tuple A.inner .t W, z ∈ sem A η h p g := by
  obtain ⟨a, ha⟩ := hc η h p g hΓ hp
  change Intension.True A.inner (A.apply (A.boxRead .t W) (sem A η h p g)) ↔ _
  rw [← ha]
  exact box_read_true A a

theorem ground_comprehension_profile_iff {Param : Classicism.Meta.Ty → Type}
    (η : Assignment A Param) (hc : GroundClosed A) {Γ : Ctx}
    (p : ITerm Param Γ Ty.t) (hΓ : ContextClosed Γ) (hp : formed p) :
    Holds A η (𝟙 A.W₀) p.comprehension .nil ↔
      ∃ R : A.Dom A.W₀ (RTy.ofArgs Γ), A.incl _ A.W₀ R = formulaProfile A η p := by
  have hcxt : ContextClosed [Ty.rel (RTy.ofArgs Γ)] :=
    context_cons.mpr ⟨ofArgs_closed Γ hΓ, context_nil⟩
  have hbody : formed (Term.closeAll Γ p.compBody) :=
    formed_closeAll Γ hΓ p.compBody (formed_compBody p hΓ hp)
  rw [Term.comprehension, holds_ex]
  constructor
  · rintro ⟨R, hR⟩
    have hb := (ground_holds_box A η hc (𝟙 A.W₀) _ (.cons R .nil) hcxt hbody).1 hR
    refine ⟨R, Set.ext ?_⟩
    rintro ⟨V, xs, k⟩
    have hh := (mem_sem_iff A η (𝟙 A.W₀)
      (Term.closeAll Γ p.compBody) (.cons R .nil) k).1 (hb ⟨V, PUnit.unit, k⟩)
    rw [Category.id_comp] at hh
    have hx := (holds_closeAll A η Γ k p.compBody _).1 hh (argsEnv A Γ xs)
    have hy := (holds_compBody A η k p ((A.inner _).map k R) (argsEnv A Γ xs)).1 hx
    simpa only [formulaProfile, Set.mem_setOf_eq, envArgs_argsEnv, A.incl_map,
      Intension.mem_map, Category.comp_id] using hy
  · rintro ⟨R, hR⟩
    refine ⟨R, (ground_holds_box A η hc (𝟙 A.W₀) _ (.cons R .nil) hcxt hbody).2 ?_⟩
    rintro ⟨V, ⟨⟩, k⟩
    apply (mem_sem_iff A η (𝟙 A.W₀)
      (Term.closeAll Γ p.compBody) (.cons R .nil) k).2
    rw [Category.id_comp]
    apply (holds_closeAll A η Γ k p.compBody _).2
    intro xs
    apply (holds_compBody A η k p ((A.inner _).map k R) xs).2
    have hh := Set.ext_iff.mp hR ⟨V, envArgs A Γ xs, k⟩
    simpa only [formulaProfile, Set.mem_setOf_eq, argsEnv_envArgs, A.incl_map,
      Intension.mem_map, Category.comp_id] using hh

theorem ground_comprehension_profile {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    (hc : GroundClosed A) (hcomp : GroundComp A) {Γ : Ctx}
    (p : ITerm Param Γ Ty.t) (hΓ : ContextClosed Γ) (hp : formed p) :
    ∃ R : A.Dom A.W₀ (RTy.ofArgs Γ), A.incl _ A.W₀ R = formulaProfile A η p :=
  (ground_comprehension_profile_iff A η hc p hΓ hp).1 (hcomp η p hΓ hp)

#print axioms ground_comprehension_profile

end Classicism.Research.InfinitaryComprehension.Canonical
