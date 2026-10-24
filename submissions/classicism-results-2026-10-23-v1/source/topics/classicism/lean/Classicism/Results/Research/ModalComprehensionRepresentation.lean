import Classicism.Syntax.Types

/-!
# The representation core of lambda-free modal comprehension

Original source: `research/2026-10-23/operator-characterizations/
modal-comprehension-abstraction-audit.txt`, §§3–7, misc, 23 October 2026.

This is a conditional metatheorem about an explicitly displayed lambda-free
proof interface. `Language.Term Γ τ` is ADMITTED SYNTAX, not an arbitrary
Lean function space. A body is a term in the extended variable context.
Object identity is `Language.eq`; it is never Lean equality. No C derivability,
lambda constructor, conversion rule, object Functionality, BF, or choice is
imported. Lean functions below manipulate syntax/proofs only.

The syntactic equations in `Language` are substitution/notation laws to be
discharged by a concrete syntax implementation. `allLift₂` in `Calculus` is
the ordinary derived Gen/UI rule lifting a closed binary implication under
one universal binder; it contains no modality. SC is restricted to admitted
bodies and its witnesses remain under OBJECT existential quantification.

Scope: NI/T/4, unique boxed representations, their beta/eta identities, and
the universal-quantifier operator law. This module does not certify the
conservative signature-extension metatheorem, a concrete syntax instance,
or the complete bidirectional translation between this base and C.
-/

namespace Classicism.Research.ModalComprehensionRepresentation
open Classicism.Meta

abbrev Ctx := List Ty

/-- A lambda-free syntax interface. All equalities in this structure concern
syntax substitution; none is an object-language equality axiom. -/
structure Language where
  Term : Ctx → Ty → Type
  var₀ {Γ σ} : Term (σ :: Γ) σ
  wk {Γ σ τ} : Term Γ τ → Term (σ :: Γ) τ
  app {Γ σ} {ρ : RTy} : Term Γ (σ ⇒ ρ) → Term Γ σ → Term Γ ρ
  top {Γ} : Term Γ Ty.t
  imp {Γ} : Term Γ Ty.t → Term Γ Ty.t → Term Γ Ty.t
  iff {Γ} : Term Γ Ty.t → Term Γ Ty.t → Term Γ Ty.t
  eq {Γ σ} : Term Γ σ → Term Γ σ → Term Γ Ty.t
  boxOp {Γ} : Term Γ (RTy.t ⇒ RTy.t)
  box {Γ} : Term Γ Ty.t → Term Γ Ty.t
  box_app {Γ} (p : Term Γ Ty.t) : app boxOp p = box p
  all {Γ σ} : Term (σ :: Γ) Ty.t → Term Γ Ty.t
  ex {Γ σ} : Term (σ :: Γ) Ty.t → Term Γ Ty.t
  inst {Γ σ τ} : Term (σ :: Γ) τ → Term Γ σ → Term Γ τ
  coext (ρ : RTy) {Γ} : Term Γ ρ → Term Γ ρ → Term Γ Ty.t
  coext_t {Γ} (p q : Term Γ Ty.t) : coext .t p q = iff p q
  coext_arr {Γ σ} {ρ : RTy} (f g : Term Γ (σ ⇒ ρ)) :
    coext (σ ⇒ ρ) f g =
      all (coext ρ (app (wk f) var₀) (app (wk g) var₀))
  inst_var {Γ σ} (a : Term Γ σ) : inst var₀ a = a
  inst_wk {Γ σ τ} (b : Term Γ τ) (a : Term Γ σ) : inst (wk b) a = b
  inst_app {Γ σ τ} {ρ : RTy} (f : Term (σ :: Γ) (τ ⇒ ρ))
      (b : Term (σ :: Γ) τ) (a : Term Γ σ) :
    inst (app f b) a = app (inst f a) (inst b a)
  inst_coext {Γ σ} {ρ : RTy} (p q : Term (σ :: Γ) ρ) (a : Term Γ σ) :
    inst (coext ρ p q) a = coext ρ (inst p a) (inst q a)
  /-- Code for the body, in the variable H, of
  `∃H. □∀x. coext (H x) M`. The equation specifies only substitution. -/
  representativeBody {Γ σ} {ρ : RTy} : Term (σ :: Γ) ρ → Term ((σ ⇒ ρ) :: Γ) Ty.t
  representativeBody_inst {Γ σ} {ρ : RTy} (M : Term (σ :: Γ) ρ)
      (H : Term Γ (σ ⇒ ρ)) :
    inst (representativeBody M) H =
      box (all (coext ρ (app (wk H) var₀) M))
  /-- The admitted body `∀x. F x`, with F as its only new free variable. -/
  universalBody {Γ} (σ : Ty) : Term ((σ ⇒ RTy.t) :: Γ) Ty.t
  universalBody_inst {Γ σ} (F : Term Γ (σ ⇒ RTy.t)) :
    inst (universalBody σ) F = all (app (wk F) var₀)
  existentialBody {Γ} (σ : Ty) : Term ((σ ⇒ RTy.t) :: Γ) Ty.t
  existentialBody_inst {Γ σ} (F : Term Γ (σ ⇒ RTy.t)) :
    inst (existentialBody σ) F = ex (app (wk F) var₀)

abbrev Formula (L : Language) (Γ : Ctx) := L.Term Γ Ty.t

/-- Explicit object proof rules. The only modal assumptions are K, theorem
necessitation, and typed Intensionality. SC is the stipulated strong schema,
written with its output tail included in `coext` under the single box. -/
structure Calculus (L : Language) where
  Derives (Γ : Ctx) : List (Formula L Γ) → Formula L Γ → Prop
  hyp {Γ Δ p} : p ∈ Δ → Derives Γ Δ p
  weaken {Γ Δ Δ' p} : (∀ q, q ∈ Δ → q ∈ Δ') →
    Derives Γ Δ p → Derives Γ Δ' p
  impI {Γ Δ p q} : Derives Γ (p :: Δ) q → Derives Γ Δ (L.imp p q)
  impE {Γ Δ p q} : Derives Γ Δ (L.imp p q) → Derives Γ Δ p → Derives Γ Δ q
  iffI {Γ Δ p q} : Derives Γ Δ (L.imp p q) → Derives Γ Δ (L.imp q p) →
    Derives Γ Δ (L.iff p q)
  iffE₁ {Γ Δ p q} : Derives Γ Δ (L.iff p q) → Derives Γ Δ p → Derives Γ Δ q
  iffE₂ {Γ Δ p q} : Derives Γ Δ (L.iff p q) → Derives Γ Δ q → Derives Γ Δ p
  topI {Γ Δ} : Derives Γ Δ L.top
  eqRefl {Γ Δ σ} (a : L.Term Γ σ) : Derives Γ Δ (L.eq a a)
  eqSymm {Γ Δ σ} {a b : L.Term Γ σ} :
    Derives Γ Δ (L.eq a b) → Derives Γ Δ (L.eq b a)
  eqTrans {Γ Δ σ} {a b c : L.Term Γ σ} :
    Derives Γ Δ (L.eq a b) → Derives Γ Δ (L.eq b c) → Derives Γ Δ (L.eq a c)
  eqApp {Γ Δ σ} {ρ : RTy} {f g : L.Term Γ (σ ⇒ ρ)} {a b : L.Term Γ σ} :
    Derives Γ Δ (L.eq f g) → Derives Γ Δ (L.eq a b) →
    Derives Γ Δ (L.eq (L.app f a) (L.app g b))
  eqRight {Γ Δ σ} (a : L.Term Γ σ) {b c : L.Term Γ σ} :
    Derives Γ Δ (L.eq b c) → Derives Γ Δ (L.eq (L.eq a b) (L.eq a c))
  eqTruth {Γ Δ p q} : Derives Γ Δ (L.eq p q) → Derives Γ Δ p → Derives Γ Δ q
  /-- Ordinary Leibniz substitution into an admitted one-variable formula. -/
  eqSubst {Γ Δ σ} (P : Formula L (σ :: Γ)) (a b : L.Term Γ σ) :
    Derives Γ Δ (L.eq a b) → Derives Γ Δ (L.inst P a) →
    Derives Γ Δ (L.inst P b)
  allI {Γ σ} {A : Formula L (σ :: Γ)} :
    Derives (σ :: Γ) [] A → Derives Γ [] (L.all A)
  allE {Γ σ} (A : Formula L (σ :: Γ)) (a : L.Term Γ σ) :
    Derives Γ [] (L.imp (L.all A) (L.inst A a))
  /-- Ordinary Gen/UI, with two universally quantified premises. The input
  proof has no hypotheses; this is not a family of proofs over named objects. -/
  allLift₂ {Γ σ} {A B C : Formula L (σ :: Γ)} :
    Derives (σ :: Γ) [] (L.imp A (L.imp B C)) →
    Derives Γ [] (L.imp (L.all A) (L.imp (L.all B) (L.all C)))
  nec {Γ p} : Derives Γ [] p → Derives Γ [] (L.box p)
  K {Γ Δ p q} : Derives Γ Δ (L.box (L.imp p q)) →
    Derives Γ Δ (L.box p) → Derives Γ Δ (L.box q)
  intensionality {Γ Δ} (ρ : RTy) (a b : L.Term Γ ρ) :
    Derives Γ Δ (L.box (L.coext ρ a b)) → Derives Γ Δ (L.eq a b)
  comprehension {Γ σ} {ρ : RTy} (M : L.Term (σ :: Γ) ρ) :
    Derives Γ [] (L.ex (L.representativeBody M))

variable {L : Language} (R : Calculus L)

abbrev Calculus.Theorem {Γ} (p : Formula L Γ) := R.Derives Γ [] p

theorem Calculus.lift {Γ Δ p} (h : R.Theorem p) : R.Derives Γ Δ p :=
  R.weaken (fun _ h => False.elim (List.not_mem_nil h)) h

theorem Calculus.hyp₀ {Γ Δ p} : R.Derives Γ (p :: Δ) p := R.hyp (List.mem_cons_self ..)

theorem Calculus.hyp₁ {Γ Δ p q} : R.Derives Γ (p :: q :: Δ) q :=
  R.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem Calculus.hyp₂ {Γ Δ p q r} : R.Derives Γ (p :: q :: r :: Δ) r :=
  R.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- Congruence through B follows from ordinary application congruence, since
B is a first-class primitive term of type tt. -/
theorem Calculus.eqBox {Γ Δ p q} (h : R.Derives Γ Δ (L.eq p q)) :
    R.Derives Γ Δ (L.eq (L.box p) (L.box q)) := by
  simpa only [L.box_app] using R.eqApp (R.eqRefl L.boxOp) h

/-- Necessity of identity, using only equality congruence through primitive B. -/
theorem Calculus.necessity_of_identity {Γ σ} (a b : L.Term Γ σ) :
    R.Theorem (L.imp (L.eq a b) (L.box (L.eq a b))) := by
  apply R.impI
  exact R.eqTruth (R.eqBox (R.eqRight a (R.hyp₀)))
    (R.lift (R.nec (R.eqRefl a)))

theorem Calculus.identity_necessitate {Γ Δ σ} {a b : L.Term Γ σ}
    (h : R.Derives Γ Δ (L.eq a b)) : R.Derives Γ Δ (L.box (L.eq a b)) :=
  R.impE (R.lift (R.necessity_of_identity a b)) h

theorem Calculus.implies_iff_top {Γ} (p : Formula L Γ) :
    R.Theorem (L.imp p (L.iff p L.top)) := by
  apply R.impI
  exact R.iffI (R.impI R.topI) (R.impI R.hyp₁)

theorem Calculus.box_implies_eq_top {Γ} (p : Formula L Γ) :
    R.Theorem (L.imp (L.box p) (L.eq p L.top)) := by
  apply R.impI
  apply R.intensionality .t p L.top
  rw [L.coext_t]
  exact R.K (R.lift (R.nec (R.implies_iff_top p))) R.hyp₀

theorem Calculus.eq_top_implies_box {Γ} (p : Formula L Γ) :
    R.Theorem (L.imp (L.eq p L.top) (L.box p)) := by
  apply R.impI
  exact R.eqTruth (R.eqSymm (R.eqBox R.hyp₀)) (R.lift (R.nec R.topI))

theorem Calculus.box_identity {Γ} (p : Formula L Γ) :
    R.Theorem (L.iff (L.box p) (L.eq p L.top)) :=
  R.iffI (R.box_implies_eq_top p) (R.eq_top_implies_box p)

/-- Reflexivity of the derived modality; no T axiom is assumed. -/
theorem Calculus.modal_T {Γ} (p : Formula L Γ) : R.Theorem (L.imp (L.box p) p) := by
  apply R.impI
  exact R.eqTruth (R.eqSymm (R.impE (R.lift (R.box_implies_eq_top p)) R.hyp₀)) R.topI

/-- Positive introspection; its only necessitated premise is an unconditional theorem. -/
theorem Calculus.modal_four {Γ} (p : Formula L Γ) :
    R.Theorem (L.imp (L.box p) (L.box (L.box p))) := by
  apply R.impI
  exact R.K (R.lift (R.nec (R.eq_top_implies_box p)))
    (R.identity_necessitate (R.impE (R.lift (R.box_implies_eq_top p)) R.hyp₀))

/-- Common-right transitivity of material biconditionals. -/
theorem Calculus.iff_common_right {Γ} (p q r : Formula L Γ) :
    R.Theorem (L.imp (L.iff p r) (L.imp (L.iff q r) (L.iff p q))) := by
  apply R.impI
  apply R.impI
  apply R.iffI
  · apply R.impI
    exact R.iffE₂ R.hyp₁ (R.iffE₁ R.hyp₂ R.hyp₀)
  · apply R.impI
    exact R.iffE₂ R.hyp₂ (R.iffE₁ R.hyp₁ R.hyp₀)

/-- Saturated coextension common-right transitivity, derived from ordinary
propositional and quantified logic by induction on the relational output type. -/
theorem Calculus.coext_common_right (ρ : RTy) : ∀ {Γ} (p q r : L.Term Γ ρ),
    R.Theorem (L.imp (L.coext ρ p r)
      (L.imp (L.coext ρ q r) (L.coext ρ p q))) := by
  induction ρ using RTy.induction with
  | t =>
    intro Γ p q r
    simp only [L.coext_t]
    exact R.iff_common_right p q r
  | arr σ ρ ih =>
    intro Γ p q r
    simp only [L.coext_arr]
    exact R.allLift₂ (ih (L.app (L.wk p) L.var₀)
      (L.app (L.wk q) L.var₀) (L.app (L.wk r) L.var₀))

theorem Calculus.coext_reflexive (ρ : RTy) : ∀ {Γ} (p : L.Term Γ ρ),
    R.Theorem (L.coext ρ p p) := by
  induction ρ using RTy.induction with
  | t =>
    intro Γ p
    rw [L.coext_t]
    exact R.iffI (R.impI R.hyp₀) (R.impI R.hyp₀)
  | arr σ ρ ih =>
    intro Γ p
    rw [L.coext_arr]
    exact R.allI (ih (L.app (L.wk p) L.var₀))

/-- This uses ordinary Leibniz substitution, not propositional extensionality. -/
theorem Calculus.identity_coextension {Γ Δ} (ρ : RTy) (p q : L.Term Γ ρ)
    (h : R.Derives Γ Δ (L.eq p q)) : R.Derives Γ Δ (L.coext ρ p q) := by
  have hp : R.Derives Γ Δ
      (L.inst (L.coext ρ (L.wk p) L.var₀) p) := by
    simpa only [L.inst_coext, L.inst_wk, L.inst_var] using
      (R.lift (R.coext_reflexive ρ p) : R.Derives Γ Δ (L.coext ρ p p))
  have hq := R.eqSubst (L.coext ρ (L.wk p) L.var₀) p q h hp
  simpa only [L.inst_coext, L.inst_wk, L.inst_var] using hq

/-- The theorem-level zeta rule needed by the separate contextual-conversion
argument. There is no open-hypothesis or pointwise-Functionality variant. -/
theorem Calculus.theorem_zeta {Γ σ} {ρ : RTy} (F G : L.Term Γ (σ ⇒ ρ))
    (h : R.Theorem (L.eq (L.app (L.wk F) L.var₀) (L.app (L.wk G) L.var₀))) :
    R.Theorem (L.eq F G) := by
  apply R.intensionality (σ ⇒ ρ) F G
  rw [L.coext_arr]
  exact R.nec (R.allI (R.identity_coextension ρ _ _ h))

def Represents {Γ σ} {ρ : RTy} (H : L.Term Γ (σ ⇒ ρ)) (M : L.Term (σ :: Γ) ρ) : Formula L Γ :=
  L.box (L.all (L.coext ρ (L.app (L.wk H) L.var₀) M))

/-- Existence is exactly the stipulated strong comprehension instance. No
metalogical witness is selected, and no host-function family is quantified. -/
theorem Calculus.representative_exists {Γ σ} {ρ : RTy} (M : L.Term (σ :: Γ) ρ) :
    R.Theorem (L.ex (L.representativeBody M)) := R.comprehension M

theorem Calculus.representative_persistent {Γ σ} {ρ : RTy}
    (H : L.Term Γ (σ ⇒ ρ)) (M : L.Term (σ :: Γ) ρ) :
    R.Theorem (L.imp (Represents H M) (L.box (Represents H M))) :=
  R.modal_four _

/-- The two boxed defining conditions force literal operation identity.
Only the unconditional quantified coextension theorem is necessitated. -/
theorem Calculus.representative_unique {Γ σ} {ρ : RTy} (M : L.Term (σ :: Γ) ρ)
    (H J : L.Term Γ (σ ⇒ ρ)) :
    R.Theorem (L.imp (Represents H M) (L.imp (Represents J M) (L.eq H J))) := by
  apply R.impI
  apply R.impI
  apply R.intensionality (σ ⇒ ρ) H J
  rw [L.coext_arr]
  exact R.K (R.K (R.lift (R.nec (R.allLift₂
    (R.coext_common_right ρ (L.app (L.wk H) L.var₀)
      (L.app (L.wk J) L.var₀) M)))) R.hyp₁) R.hyp₀

/-- Boxed universal elimination preserves the output-tail coextension. -/
theorem Calculus.representative_instance {Γ Δ σ} {ρ : RTy} (M : L.Term (σ :: Γ) ρ)
    (H : L.Term Γ (σ ⇒ ρ)) (a : L.Term Γ σ)
    (h : R.Derives Γ Δ (Represents H M)) :
    R.Derives Γ Δ (L.box (L.coext ρ (L.app H a) (L.inst M a))) := by
  have h' := R.K (R.lift (R.nec (R.allE
    (L.coext ρ (L.app (L.wk H) L.var₀) M) a))) h
  simpa only [L.inst_coext, L.inst_app, L.inst_wk, L.inst_var] using h'

/-- Beta is derived from the defining witness condition and Intensionality;
it is neither a syntax conversion nor an assumed representation law. -/
theorem Calculus.representative_beta {Γ Δ σ} {ρ : RTy} (M : L.Term (σ :: Γ) ρ)
    (H : L.Term Γ (σ ⇒ ρ)) (a : L.Term Γ σ)
    (h : R.Derives Γ Δ (Represents H M)) :
    R.Derives Γ Δ (L.eq (L.app H a) (L.inst M a)) :=
  R.intensionality ρ _ _ (R.representative_instance M H a h)

/-- Eta is full-type Intensionality applied to the boxed defining condition. -/
theorem Calculus.representative_eta {Γ Δ σ} {ρ : RTy} (H F : L.Term Γ (σ ⇒ ρ))
    (h : R.Derives Γ Δ (Represents H (L.app (L.wk F) L.var₀))) :
    R.Derives Γ Δ (L.eq H F) := by
  apply R.intensionality (σ ⇒ ρ) H F
  simpa only [L.coext_arr, Represents] using h

/-- The quantifier operator at sigma exists as a strong-comprehension witness. -/
theorem Calculus.universal_operator_exists {Γ} (σ : Ty) :
    R.Theorem (Γ := Γ) (L.ex (L.representativeBody (L.universalBody σ))) :=
  R.representative_exists _

/-- A selected quantifier representative agrees by LITERAL proposition
identity with the primitive universal binder at every current predicate. -/
theorem Calculus.universal_operator_law {Γ Δ σ}
    (Q : L.Term Γ ((σ ⇒ RTy.t) ⇒ RTy.t)) (F : L.Term Γ (σ ⇒ RTy.t))
    (h : R.Derives Γ Δ (Represents Q (L.universalBody σ))) :
    R.Derives Γ Δ (L.eq (L.app Q F) (L.all (L.app (L.wk F) L.var₀))) := by
  simpa only [L.universalBody_inst] using
    R.representative_beta (L.universalBody σ) Q F h

theorem Calculus.existential_operator_exists {Γ} (σ : Ty) :
    R.Theorem (Γ := Γ) (L.ex (L.representativeBody (L.existentialBody σ))) :=
  R.representative_exists _

theorem Calculus.existential_operator_law {Γ Δ σ}
    (Q : L.Term Γ ((σ ⇒ RTy.t) ⇒ RTy.t)) (F : L.Term Γ (σ ⇒ RTy.t))
    (h : R.Derives Γ Δ (Represents Q (L.existentialBody σ))) :
    R.Derives Γ Δ (L.eq (L.app Q F) (L.ex (L.app (L.wk F) L.var₀))) := by
  simpa only [L.existentialBody_inst] using
    R.representative_beta (L.existentialBody σ) Q F h

/-! ## Capture the complete finite parameter tuple at once

Unary pointwise witness existence does not suffice for conservative naming.
The following separate, explicit schema covers one finite syntactic binder
spine, which includes all free parameters of the abstraction to be named.
This is the full finite-tuple SC assumption of the ordinary proof.
-/

/-- An admitted formula and a finite spine of variables to be represented.
There is no constructor accepting an external Lean family of object values. -/
inductive AdmittedBody (L : Language) : Ctx → RTy → Type
  | atom {Γ} : Formula L Γ → AdmittedBody L Γ .t
  | bind {Γ σ} {ρ : RTy} : AdmittedBody L (σ :: Γ) ρ → AdmittedBody L Γ (σ ⇒ ρ)

def diagram : {Γ : Ctx} → {ρ : RTy} → AdmittedBody L Γ ρ →
    L.Term Γ ρ → Formula L Γ
  | _, .t, .atom p, H => L.iff H p
  | _, _ ⇒ _, .bind A, H => L.all (diagram A (L.app (L.wk H) L.var₀))

def UniformRepresents {Γ} {ρ : RTy} (A : AdmittedBody L Γ ρ)
    (H : L.Term Γ ρ) : Formula L Γ := L.box (diagram A H)

/-- Only syntax admission/substitution and the stipulated finite-tuple SC
are fields. Unique witnesses, persistence and identities are not fields. -/
structure UniformComprehension (L : Language) (R : Calculus L) where
  bodyCode {Γ} {ρ : RTy} : AdmittedBody L Γ ρ → Formula L (ρ :: Γ)
  bodyCode_inst {Γ} {ρ : RTy} (A : AdmittedBody L Γ ρ) (H : L.Term Γ ρ) :
    L.inst (bodyCode A) H = UniformRepresents A H
  comprehend {Γ} {ρ : RTy} (A : AdmittedBody L Γ ρ) : R.Theorem (L.ex (bodyCode A))

theorem Calculus.diagram_common_right {Γ} {ρ : RTy} (A : AdmittedBody L Γ ρ) :
    ∀ H J : L.Term Γ ρ, R.Theorem
      (L.imp (diagram A H) (L.imp (diagram A J) (L.coext ρ H J))) := by
  induction A with
  | atom p =>
    intro H J
    simp only [diagram, L.coext_t]
    exact R.iff_common_right H J p
  | bind A ih =>
    intro H J
    simp only [diagram, L.coext_arr]
    exact R.allLift₂ (ih (L.app (L.wk H) L.var₀) (L.app (L.wk J) L.var₀))

/-- Jointly captured witnesses are unique by a finite syntactic induction;
this does not choose witnesses separately for the current parameter values. -/
theorem Calculus.uniform_representative_unique {Γ} {ρ : RTy} (A : AdmittedBody L Γ ρ)
    (H J : L.Term Γ ρ) : R.Theorem
      (L.imp (UniformRepresents A H) (L.imp (UniformRepresents A J) (L.eq H J))) := by
  apply R.impI
  apply R.impI
  exact R.intensionality ρ H J
    (R.K (R.K (R.lift (R.nec (R.diagram_common_right A H J))) R.hyp₁) R.hyp₀)

theorem Calculus.uniform_representative_persistent {Γ} {ρ : RTy} (A : AdmittedBody L Γ ρ)
    (H : L.Term Γ ρ) : R.Theorem
      (L.imp (UniformRepresents A H) (L.box (UniformRepresents A H))) :=
  R.modal_four _

theorem Calculus.uniform_representative_exists (SC : UniformComprehension L R)
    {Γ} {ρ : RTy} (A : AdmittedBody L Γ ρ) : R.Theorem (L.ex (SC.bodyCode A)) :=
  SC.comprehend A

/-- Exact closed-witness entry point for the separate stable-naming argument.
All parameters have been captured by the finite binder spine of A. -/
theorem Calculus.closed_uniform_representation (SC : UniformComprehension L R)
    {ρ : RTy} (A : AdmittedBody L [] ρ) :
    R.Theorem (L.ex (SC.bodyCode A)) ∧
      (∀ H : L.Term [] ρ, R.Theorem (L.imp (UniformRepresents A H)
        (L.box (UniformRepresents A H)))) ∧
      (∀ H J : L.Term [] ρ, R.Theorem (L.imp (UniformRepresents A H)
        (L.imp (UniformRepresents A J) (L.eq H J)))) :=
  ⟨SC.comprehend A, R.uniform_representative_persistent A,
    R.uniform_representative_unique A⟩

-- Kernel checks of the central conditional derivations. No `sorryAx`,
-- `propext`, `Quot.sound`, or `Classical.choice` should appear.
#print axioms Calculus.necessity_of_identity
#print axioms Calculus.modal_four
#print axioms Calculus.representative_unique
#print axioms Calculus.representative_beta
#print axioms Calculus.representative_eta
#print axioms Calculus.theorem_zeta
#print axioms Calculus.universal_operator_law
#print axioms Calculus.uniform_representative_unique
#print axioms Calculus.closed_uniform_representation

end Classicism.Research.ModalComprehensionRepresentation
