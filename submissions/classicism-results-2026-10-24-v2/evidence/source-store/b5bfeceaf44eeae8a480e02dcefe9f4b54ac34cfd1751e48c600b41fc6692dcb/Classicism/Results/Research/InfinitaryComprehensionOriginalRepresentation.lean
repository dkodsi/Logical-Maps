import Classicism.Results.Research.InfinitaryComprehensionGroundedModel

/-!
# Full standard representation from the original lambda-free infinitary axioms

Source: Infinitary Comprehension, section 4 (misc, original research,
23 October 2026, unpaginated).

The premises are actual closed-type term closure, actual closed-type
Comprehension and the actual boxed ND_t sentence. No finite C model,
Barcan principle, constant-domain condition, or full-support condition is
assumed. GroundedModel constructs the harmless auxiliary-type expansion;
LambdaFreeCanonical proves the domain-map bijections; Representation
constructs the full faithful model and its truth lemma.

These are semantic representation statements in ordinary classical
metatheory. They do not assert a recursive infinitary proof calculus.
Compilation is intentionally held; the source is not a certificate.
-/

namespace Classicism.Research.InfinitaryComprehension.Canonical

open Classicism.Meta Classicism.Meta.Intensional CategoryTheory Grounding

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C)

noncomputable def originalModel (hc : GroundClosed A) (hC5 : LambdaFreeC5 A) :
    Henkin.Model :=
  (Canonical.lambdaFreeModel (Canonical.groundedPremodel A)) ((Canonical.grounded_closed A) hc) ((Canonical.grounded_c5 A) hC5)

noncomputable def originalRootWorld (hc : GroundClosed A) (hC5 : LambdaFreeC5 A) :
    ((Canonical.originalModel A) hc hC5).World :=
  (Canonical.lambdaFreeRootWorld (Canonical.groundedPremodel A)) ((Canonical.grounded_closed A) hc) ((Canonical.grounded_c5 A) hC5)

/-- Every original closed-type domain is retained, rather than replaced by an
unrelated model merely satisfying the same axioms. -/
theorem originalModel_domain (hc : GroundClosed A) (hC5 : LambdaFreeC5 A)
    (σ : Classicism.Meta.Ty) (hσ : σ.Closed) : ((Canonical.originalModel A) hc hC5).Dom σ = A.Dom A.W₀ σ := by
  change A.Dom A.W₀ (groundTy (groundTy σ)) = A.Dom A.W₀ σ
  rw [groundTy_eq_of_closed σ hσ]
  rw [groundTy_eq_of_closed σ hσ]

theorem originalModel_nonempty_e (hc : GroundClosed A) (hC5 : LambdaFreeC5 A) :
    Nonempty (((Canonical.originalModel A) hc hC5).Dom Ty.e) := A.nonempty_e A.W₀

theorem originalModel_faithful (hc : GroundClosed A) (hcomp : GroundComp A)
    (hC5 : LambdaFreeC5 A) : Henkin.Faithful ((Canonical.originalModel A) hc hC5) :=
  (Canonical.lambdaFreeModel_faithful (Canonical.groundedPremodel A)) ((Canonical.grounded_closed A) hc)
    ((Canonical.grounded_comprehension A) hc hcomp) ((Canonical.grounded_c5 A) hC5)

theorem originalModel_worldSeparated (hc : GroundClosed A) (hC5 : LambdaFreeC5 A) :
    Henkin.WorldSeparated ((Canonical.originalModel A) hc hC5) :=
  (Canonical.lambdaFreeModel_worldSeparated (Canonical.groundedPremodel A)) ((Canonical.grounded_closed A) hc) ((Canonical.grounded_c5 A) hC5)

theorem originalModel_comp (hc : GroundClosed A) (hcomp : GroundComp A)
    (hC5 : LambdaFreeC5 A) :
    Henkin.Comp ((Canonical.originalModel A) hc hC5) ((Canonical.originalRootWorld A) hc hC5) :=
  (Canonical.lambdaFreeModel_comp (Canonical.groundedPremodel A)) ((Canonical.grounded_closed A) hc)
    ((Canonical.grounded_comprehension A) hc hcomp) ((Canonical.grounded_c5 A) hC5)

theorem originalModel_full_profiles (hc : GroundClosed A) (hcomp : GroundComp A)
    (hC5 : LambdaFreeC5 A) : Henkin.FullProfiles ((Canonical.originalModel A) hc hC5) :=
  (Canonical.lambdaFreeModel_full_profiles (Canonical.groundedPremodel A)) ((Canonical.grounded_closed A) hc)
    ((Canonical.grounded_comprehension A) hc hcomp) ((Canonical.grounded_c5 A) hC5)

theorem originalModel_full_functions (hc : GroundClosed A) (hcomp : GroundComp A)
    (hC5 : LambdaFreeC5 A) (σ : Classicism.Meta.Ty) (ρ : RTy)
    (f : ((Canonical.originalModel A) hc hC5).Dom σ → ((Canonical.originalModel A) hc hC5).Dom ρ) :
    ∃! R : ((Canonical.originalModel A) hc hC5).Dom (σ ⇒ ρ),
      ∀ x, ((Canonical.originalModel A) hc hC5).app R x = f x :=
  (Canonical.lambdaFreeModel_full_functions (Canonical.groundedPremodel A)) ((Canonical.grounded_closed A) hc)
    ((Canonical.grounded_comprehension A) hc hcomp) ((Canonical.grounded_c5 A) hC5) σ ρ f

theorem originalModel_full_propositions (hc : GroundClosed A) (hcomp : GroundComp A)
    (hC5 : LambdaFreeC5 A) (U : ((Canonical.originalModel A) hc hC5).World → Prop) :
    ∃! p : ((Canonical.originalModel A) hc hC5).Dom Ty.t,
      ∀ w, ((Canonical.originalModel A) hc hC5).truth p w ↔ U w :=
  (Canonical.lambdaFreeModel_full_propositions (Canonical.groundedPremodel A)) ((Canonical.grounded_closed A) hc)
    ((Canonical.grounded_comprehension A) hc hcomp) ((Canonical.grounded_c5 A) hC5) U

/-- The exact truth-preservation clause. The two explicit grounding maps only
remove auxiliary type codes; closed object sorts are retained by the domain
lemma above. The quotient identifies only observationally equal worlds. -/
theorem originalModel_truth (hc : GroundClosed A) (hcomp : GroundComp A)
    (hC5 : LambdaFreeC5 A) {Param : Classicism.Meta.Ty → Type}
    (η : Henkin.Assignment ((Canonical.originalModel A) hc hC5) Param) {Γ}
    (p : ITerm Param Γ Ty.t) (xs : Henkin.Env ((Canonical.originalModel A) hc hC5) Γ)
    (w : Tuple (Canonical.groundedPremodel A).inner .t A.W₀) :
    ((Canonical.originalModel A) hc hC5).truth (Henkin.eval _ η p xs) (Quotient.mk _ w) ↔
      Holds A (Canonical.selfAssignment A) w.2.2
        (groundTerm (Param := (Canonical.groundedPremodel A).Dom A.W₀) (Param' := A.Dom A.W₀) (Canonical.selfAssignment (Canonical.groundedPremodel A)) (groundTerm (Param := Param) (Param' := (Canonical.groundedPremodel A).Dom A.W₀) η p))
        (Grounding.groundEnv
          ((Canonical.groundedPremodel A).push w.2.2 ((Canonical.groundEnv (Canonical.groundedPremodel A)) xs))) := by
  let hc' : Closed (Canonical.groundedPremodel A) := (Canonical.grounded_closed A) hc
  let hC5' := (Canonical.grounded_c5 A) hC5
  let hinj := (Canonical.lambdaFree_rootInjective (Canonical.groundedPremodel A)) hc' hC5'
  let hepi := (Canonical.lambdaFree_rootSurjective (Canonical.groundedPremodel A)) hc'
    ((Canonical.grounded_comprehension A) hc hcomp) hC5'
  change ((Canonical.rawModelOfInjections (Canonical.groundedPremodel A)) hc' hinj).truth
    (Henkin.eval (quotientModel ((Canonical.rawModelOfInjections (Canonical.groundedPremodel A)) hc' hinj))
      η p xs) w ↔ _
  refine (Iff.of_eq (congrArg
    (fun q => ((Canonical.rawModelOfInjections (Canonical.groundedPremodel A)) hc' hinj).truth q w)
    (quotient_eval ((Canonical.rawModelOfInjections (Canonical.groundedPremodel A)) hc' hinj)
      (Param := Param) η p xs))).trans ?_
  exact ((Canonical.raw_truth_spec_of_surjections (Canonical.groundedPremodel A)) hc' hinj hepi η p xs w).trans
    ((Canonical.grounded_holds A) (Canonical.selfAssignment (Canonical.groundedPremodel A)) w.2.2 (groundTerm (Param := Param) (Param' := (Canonical.groundedPremodel A).Dom A.W₀) η p)
      ((Canonical.groundedPremodel A).push w.2.2 ((Canonical.groundEnv (Canonical.groundedPremodel A)) xs)))

/-- The complete intended forward representation endpoint from the original
language premises. Every structural property below is a conclusion. -/
theorem original_full_standard_representation (hc : GroundClosed A)
    (hcomp : GroundComp A) (hC5 : LambdaFreeC5 A) :
    Nonempty (((Canonical.originalModel A) hc hC5).Dom Ty.e) ∧
    Henkin.Faithful ((Canonical.originalModel A) hc hC5) ∧
    Henkin.WorldSeparated ((Canonical.originalModel A) hc hC5) ∧
    Henkin.Comp ((Canonical.originalModel A) hc hC5) ((Canonical.originalRootWorld A) hc hC5) ∧
    Henkin.FullProfiles ((Canonical.originalModel A) hc hC5) :=
  ⟨(Canonical.originalModel_nonempty_e A) hc hC5, (Canonical.originalModel_faithful A) hc hcomp hC5,
    (Canonical.originalModel_worldSeparated A) hc hC5, (Canonical.originalModel_comp A) hc hcomp hC5,
    (Canonical.originalModel_full_profiles A) hc hcomp hC5⟩

#print axioms originalModel_domain
#print axioms originalModel_truth
#print axioms original_full_standard_representation
#print axioms originalModel_full_functions
#print axioms originalModel_full_propositions

end Classicism.Research.InfinitaryComprehension.Canonical
