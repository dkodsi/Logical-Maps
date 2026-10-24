import Classicism.Results.Research.InfinitaryComprehensionActionConsequences
import Classicism.Results.Research.InfinitaryComprehensionFullness

/-!
# Canonical fullness from the actual infinitary C5 model

Source: the main Infinitary Comprehension note, section 4 (misc, original
research, 23 October 2026, unpaginated).

The input is an actual intensional action model with its infinitary term
closure, the actual Comprehension schema, and the native closed-type C5
schema. Constant domains, faithfulness, world separation and full function
spaces are all conclusions of the construction. `Canonical` supplies the
actual interpretation and the canonical truth lemma; `ActionConsequences`
extracts relation profiles from the actual existential/boxed formula.

This assembly deliberately imports both directions after their common
semantic core, avoiding a circular import. Its proof transports the matrix's
profile witness, rather than assuming that Comprehension is preserved.
The input `Closed` and `Comprehension` predicates currently range over the
full infinitary datatype, including auxiliary type-variable codes. Native
C5 itself is used only at original closed types, and the output domains are
grounded root domains. The construction therefore applies to the explicitly
stated infinitary expansions. `OriginalLanguage` states closure/comprehension
only at occurring closed types, and `GroundedModel` constructs their concrete
grounding extension. This reusable assembly keeps the full-datatype premises;
it neither assumes nor substitutes for that separate extension proof.

All statements are ordinary classical metatheory. Compilation is held.
-/

namespace Classicism.Research.InfinitaryComprehension.Canonical

open Classicism.Meta Classicism.Meta.Intensional CategoryTheory Grounding

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C)

private def castDomain {σ τ : Classicism.Meta.Ty} (e : σ = τ) (a : A.Dom A.W₀ σ) :
    A.Dom A.W₀ τ := e ▸ a

private theorem castDomain_heq {σ τ : Classicism.Meta.Ty} (e : σ = τ) (a : A.Dom A.W₀ σ) :
    HEq (castDomain A e a) a := by
  cases e
  rfl

private theorem rootApp_heq (hc : Closed A) {σ : Classicism.Meta.Ty} {ρ τ : RTy}
    (e : ρ = τ) (R : A.Dom A.W₀ (σ ⇒ ρ)) (S : A.Dom A.W₀ (σ ⇒ τ))
    (h : HEq R S) (x : A.Dom A.W₀ σ) :
    HEq ((Canonical.rootApp A) hc R x) ((Canonical.rootApp A) hc S x) := by
  cases e
  cases h
  rfl

/-- Application in the grounded canonical presentation reads exactly the
original relation's outgoing-world profile on transported arguments. -/
theorem raw_uncurry_profile_of_injections (hc : Closed A) (hinj : RootInjective A) :
    ∀ (Γ : Ctx) (R : ((Canonical.rawModelOfInjections A) hc hinj).Dom (RTy.ofArgs Γ))
      (S : A.Dom A.W₀ (RTy.ofArgs (groundCtx Γ))), HEq R S →
      ∀ (xs : Henkin.Env ((Canonical.rawModelOfInjections A) hc hinj) Γ)
        (w : Tuple A.inner .t A.W₀),
        ((Canonical.rawModelOfInjections A) hc hinj).truth
          (Henkin.uncurry ((Canonical.rawModelOfInjections A) hc hinj) Γ R xs) w ↔
          (⟨w.1, envArgs A (groundCtx Γ) (A.push w.2.2 ((Canonical.groundEnv A) xs)),
            w.2.2⟩ : Tuple A.inner (RTy.ofArgs (groundCtx Γ)) A.W₀) ∈
              A.incl _ A.W₀ S := by
  intro Γ
  induction Γ with
  | nil =>
      intro R S h xs w
      cases h
      rcases w with ⟨V, ⟨⟩, k⟩
      rfl
  | cons σ Γ ih =>
      intro R S h xs w
      have happ := rootApp_heq A hc (groundRTy_ofArgs Γ) R S h (xs .zero)
      have hh := ih ((Canonical.rootApp A) hc R (xs .zero))
        ((Canonical.rootApp A) hc S (xs .zero)) happ (Henkin.Env.tail xs) w
      have hread := congrArg
        (fun F : Intension A.inner (RTy.ofArgs (groundCtx Γ)) A.W₀ =>
          (⟨w.1, envArgs A (groundCtx Γ)
            (A.push w.2.2 ((Canonical.groundEnv A) (Henkin.Env.tail xs))),
            w.2.2⟩ : Tuple A.inner (RTy.ofArgs (groundCtx Γ)) A.W₀) ∈ F)
        (Canonical.rootApp_spec A hc (σ := groundTy σ)
          (ρ := RTy.ofArgs (groundCtx Γ)) S (xs .zero))
      have hh' := hh.trans (Iff.of_eq hread)
      change _ ↔
        (⟨w.1, (((A.inner (groundTy σ)).map w.2.2) (xs .zero),
          envArgs A (groundCtx Γ)
            (A.push w.2.2 ((Canonical.groundEnv A) (Henkin.Env.tail xs)))),
          w.2.2⟩ : Tuple A.inner (groundTy σ ⇒ RTy.ofArgs (groundCtx Γ)) A.W₀) ∈
          A.incl (groundTy σ ⇒ RTy.ofArgs (groundCtx Γ)) A.W₀ S
      exact hh'.trans (Intension.mem_app A.inner
        (A.incl (groundTy σ ⇒ RTy.ofArgs (groundCtx Γ)) A.W₀ S) (xs .zero)
        ⟨w.1, envArgs A (groundCtx Γ)
          (A.push w.2.2 ((Canonical.groundEnv A) (Henkin.Env.tail xs))), w.2.2⟩)

/-- The actual infinitary Comprehension schema transfers to the constructed
constant-domain model. The representative comes from the source matrix's
Comprehension instance; no support or representation hypothesis is added. -/
theorem rawModel_comp_of_maps (hc : Closed A) (hcomp : Comprehension A)
    (hinj : RootInjective A) (hepi : RootSurjective A)
    (w₀ : ((Canonical.rawModelOfInjections A) hc hinj).World) : Henkin.Comp ((Canonical.rawModelOfInjections A) hc hinj) w₀ := by
  intro Param η Γ p
  apply (Henkin.eval_comprehension_iff ((Canonical.rawModelOfInjections A) hc hinj) η p w₀).2
  obtain ⟨S, hS⟩ := comprehension_profile A (Canonical.selfAssignment A) hc hcomp (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
  let e : Ty.rel (RTy.ofArgs (groundCtx Γ)) = Ty.rel (groundRTy (RTy.ofArgs Γ)) :=
    congrArg Ty.rel (groundRTy_ofArgs Γ).symm
  refine ⟨castDomain A e S, ?_⟩
  intro xs w
  rw [raw_uncurry_profile_of_injections A hc hinj Γ (castDomain A e S) S
    (castDomain_heq A e S) xs w, hS]
  change Holds A (Canonical.selfAssignment A) w.2.2 (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
    (argsEnv A (groundCtx Γ)
      (envArgs A (groundCtx Γ) (A.push w.2.2 ((Canonical.groundEnv A) xs)))) ↔ _
  rw [argsEnv_envArgs]
  exact ((Canonical.raw_truth_spec_of_surjections A) hc hinj hepi η p xs w).symm

/-- Application in the grounded canonical presentation reads exactly the
original relation's outgoing-world profile on transported arguments. -/
theorem raw_uncurry_profile (M : A.IsModel) (hc : Closed A) (hC5 : C5 A) :
    ∀ (Γ : Ctx) (R : ((Canonical.rawModel A) M hc hC5).Dom (RTy.ofArgs Γ))
      (S : A.Dom A.W₀ (RTy.ofArgs (groundCtx Γ))), HEq R S →
      ∀ (xs : Henkin.Env ((Canonical.rawModel A) M hc hC5) Γ)
        (w : Tuple A.inner .t A.W₀),
        ((Canonical.rawModel A) M hc hC5).truth
          (Henkin.uncurry ((Canonical.rawModel A) M hc hC5) Γ R xs) w ↔
          (⟨w.1, envArgs A (groundCtx Γ) (A.push w.2.2 ((Canonical.groundEnv A) xs)),
            w.2.2⟩ : Tuple A.inner (RTy.ofArgs (groundCtx Γ)) A.W₀) ∈
              A.incl _ A.W₀ S :=
  raw_uncurry_profile_of_injections A hc ((Canonical.c5_rootInjective A) M hC5)

/-- The actual infinitary Comprehension schema transfers to the constructed
constant-domain model. The representative comes from the source matrix's
Comprehension instance; no support or representation hypothesis is added. -/
theorem rawModel_comp (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A)
    (w₀ : ((Canonical.rawModel A) M hc hC5).World) : Henkin.Comp ((Canonical.rawModel A) M hc hC5) w₀ :=
  rawModel_comp_of_maps A hc hcomp ((Canonical.c5_rootInjective A) M hC5)
    (fun σ {_} h => (Canonical.ground_map_surjective A) M hc hcomp hC5 σ h) w₀

theorem model_comp (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A) :
    Henkin.Comp ((Canonical.model A) M hc hC5) ((Canonical.rootWorld A) M hc hC5) :=
  quotient_comp _ (rawModel_comp A M hc hcomp hC5 ⟨A.W₀, PUnit.unit, 𝟙 A.W₀⟩)

/-- Every world--argument support exists in the presentation of the actual
input model. Faithfulness and separation are proved, not premises here. -/
theorem model_full_profiles (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A) :
    Henkin.FullProfiles ((Canonical.model A) M hc hC5) :=
  (Henkin.comp_iff_full_profiles _ ((Canonical.rootWorld A) M hc hC5)
    ((Canonical.model_faithful A) M hc hcomp hC5) ((Canonical.model_worldSeparated A) M hc hC5)).1
      (model_comp A M hc hcomp hC5)

/-- Each allowed arrow is all of the external function space, uniquely. -/
theorem model_full_functions (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A) (σ : Classicism.Meta.Ty) (ρ : RTy)
    (f : ((Canonical.model A) M hc hC5).Dom σ → ((Canonical.model A) M hc hC5).Dom ρ) :
    ∃! R : ((Canonical.model A) M hc hC5).Dom (σ ⇒ ρ),
      ∀ x, ((Canonical.model A) M hc hC5).app R x = f x := by
  obtain ⟨R, hR⟩ := Henkin.functions_of_full_profiles _
    (model_full_profiles A M hc hcomp hC5) ((Canonical.model_faithful A) M hc hcomp hC5) σ ρ f
  refine ⟨R, hR, ?_⟩
  intro S hS
  exact Henkin.application_injective _ ((Canonical.model_faithful A) M hc hcomp hC5) σ ρ S R
    (fun x => (hS x).trans (hR x).symm)

/-- The proposition domain is precisely the power set of the constructed
world set, with no missing subsets or duplicate proposition profiles. -/
theorem model_full_propositions (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A)
    (U : ((Canonical.model A) M hc hC5).World → Prop) :
    ∃! p : ((Canonical.model A) M hc hC5).Dom Ty.t,
      ∀ w, ((Canonical.model A) M hc hC5).truth p w ↔ U w := by
  obtain ⟨p, hp⟩ := model_full_profiles A M hc hcomp hC5 [] (fun z => U z.1)
  refine ⟨p, fun w => hp Henkin.Env.nil w, ?_⟩
  intro q hq
  apply (Canonical.model_faithful A) M hc hcomp hC5 []
  intro xs w
  exact (hq w).trans (hp xs w).symm

/-- The reusable construction separates the elementary domain-map argument
from the profile representation argument. Its map premises will be discharged
by the actual lambda-free axioms in LambdaFreeCanonical. -/
noncomputable def modelOfMaps (hc : Closed A) (hinj : RootInjective A) : Henkin.Model :=
  quotientModel ((Canonical.rawModelOfInjections A) hc hinj)

noncomputable def rootWorldOfMaps (hc : Closed A) (hinj : RootInjective A) :
    ((Canonical.modelOfMaps A) hc hinj).World :=
  Quotient.mk _ ⟨A.W₀, PUnit.unit, 𝟙 A.W₀⟩

theorem modelOfMaps_faithful (hc : Closed A) (hinj : RootInjective A)
    (hepi : RootSurjective A) : Henkin.Faithful ((Canonical.modelOfMaps A) hc hinj) :=
  quotient_faithful _ ((Canonical.rawModel_faithful_of_surjections A) hc hinj hepi)

theorem modelOfMaps_worldSeparated (hc : Closed A) (hinj : RootInjective A) :
    Henkin.WorldSeparated ((Canonical.modelOfMaps A) hc hinj) := quotient_worldSeparated _

theorem modelOfMaps_comp (hc : Closed A) (hcomp : Comprehension A)
    (hinj : RootInjective A) (hepi : RootSurjective A) :
    Henkin.Comp ((Canonical.modelOfMaps A) hc hinj) ((Canonical.rootWorldOfMaps A) hc hinj) :=
  quotient_comp _ (rawModel_comp_of_maps A hc hcomp hinj hepi
    ⟨A.W₀, PUnit.unit, 𝟙 A.W₀⟩)

theorem modelOfMaps_full_profiles (hc : Closed A) (hcomp : Comprehension A)
    (hinj : RootInjective A) (hepi : RootSurjective A) :
    Henkin.FullProfiles ((Canonical.modelOfMaps A) hc hinj) :=
  (Henkin.comp_iff_full_profiles _ ((Canonical.rootWorldOfMaps A) hc hinj)
    ((Canonical.modelOfMaps_faithful A) hc hinj hepi) ((Canonical.modelOfMaps_worldSeparated A) hc hinj)).1
      (modelOfMaps_comp A hc hcomp hinj hepi)

theorem modelOfMaps_full_functions (hc : Closed A) (hcomp : Comprehension A)
    (hinj : RootInjective A) (hepi : RootSurjective A) (σ : Classicism.Meta.Ty) (ρ : RTy)
    (f : ((Canonical.modelOfMaps A) hc hinj).Dom σ → ((Canonical.modelOfMaps A) hc hinj).Dom ρ) :
    ∃! R : ((Canonical.modelOfMaps A) hc hinj).Dom (σ ⇒ ρ),
      ∀ x, ((Canonical.modelOfMaps A) hc hinj).app R x = f x := by
  obtain ⟨R, hR⟩ := Henkin.functions_of_full_profiles _
    (modelOfMaps_full_profiles A hc hcomp hinj hepi)
    ((Canonical.modelOfMaps_faithful A) hc hinj hepi) σ ρ f
  refine ⟨R, hR, ?_⟩
  intro S hS
  exact Henkin.application_injective _ ((Canonical.modelOfMaps_faithful A) hc hinj hepi) σ ρ S R
    (fun x => (hS x).trans (hR x).symm)

theorem modelOfMaps_full_propositions (hc : Closed A) (hcomp : Comprehension A)
    (hinj : RootInjective A) (hepi : RootSurjective A)
    (U : ((Canonical.modelOfMaps A) hc hinj).World → Prop) :
    ∃! p : ((Canonical.modelOfMaps A) hc hinj).Dom Ty.t,
      ∀ w, ((Canonical.modelOfMaps A) hc hinj).truth p w ↔ U w := by
  obtain ⟨p, hp⟩ := modelOfMaps_full_profiles A hc hcomp hinj hepi [] (fun z => U z.1)
  refine ⟨p, fun w => hp Henkin.Env.nil w, ?_⟩
  intro q hq
  apply (Canonical.modelOfMaps_faithful A) hc hinj hepi []
  intro xs w
  exact (hq w).trans (hp xs w).symm

#print axioms rawModel_comp_of_maps
#print axioms modelOfMaps_full_profiles
#print axioms modelOfMaps_full_functions
#print axioms modelOfMaps_full_propositions

#print axioms rawModel_comp
#print axioms model_full_profiles
#print axioms model_full_functions
#print axioms model_full_propositions

end Classicism.Research.InfinitaryComprehension.Canonical
