import Classicism.Results.Research.ModalLogicalOperatorTransport
import Classicism.Results.Research.ModalLogicalOperatorLaws
import Classicism.Results.Research.ModalFiniteNameSupport
import Classicism.Results.Research.ModalConcreteToCSyntax

/-!
# Exact old-constant/new-name split for the reconstruction compiler

Original research, misc, 23 October 2026. Old constants retain arbitrary
types, including e and opaque type variables. Every newly introduced name
has a relational type and one independent closed old-language SC body.
The maps below are explicit inverse syntactic maps; no default constant,
representative selector or semantic choice is used.
-/

namespace Classicism.Research.ModalReconstructionNames
open Classicism.Meta (Ty RTy)
open ModalComprehensionConcreteSyntax
open ModalLogicalOperators (LogicalOperator Constants)
open ModalFiniteNameSupport
open RelationalBracketAbstraction (BasisConst)
open RelationalLambdaCompilation (Atoms)

inductive Name : RTy → Type
  | I (ρ : RTy) : Name (ρ ⇒ ρ)
  | K (σ : Ty) (ρ : RTy) : Name (ρ ⇒ σ ⇒ ρ)
  | S (σ : Ty) (τ ρ : RTy) : Name ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  | C (σ τ : Ty) (ρ : RTy) : Name ((σ ⇒ τ ⇒ ρ) ⇒ τ ⇒ σ ⇒ ρ)
  | W (σ : Ty) (ρ : RTy) : Name ((σ ⇒ σ ⇒ ρ) ⇒ σ ⇒ ρ)
  | logical {ρ : RTy} : LogicalOperator ρ → Name ρ

variable {C D : Ty → Type}

def Name.body {ρ : RTy} (n : Name ρ) (Γ : Ctx) : Body C Γ ρ :=
  match n with
  | .I ρ => CombinatorBody.I ρ Γ
  | .K σ ρ => CombinatorBody.K σ ρ Γ
  | .S σ τ ρ => CombinatorBody.S σ τ ρ Γ
  | .C σ τ ρ => CombinatorBody.C σ τ ρ Γ
  | .W σ ρ => CombinatorBody.W σ ρ Γ
  | .logical o => o.body Γ

def closedBody (C : Ty → Type) {ρ : RTy} (n : Name ρ) : Body C [] ρ := n.body []

/-- Flatten the compiler's nested signature into the finite-name API. -/
def split : ConstMap (Constants (ModalConcreteToC.signature C)) (NamedConst C Name)
  | _, .original (@Atoms.nonlogical (ModalConcreteToC.signature C) ⟨_, c⟩) => .old c
  | _, .original .and => .name (.logical .and)
  | _, .original .or => .name (.logical .or)
  | _, .original .not => .name (.logical .not)
  | _, .original (.all σ) => .name (.logical (.all σ))
  | _, .original (.ex σ) => .name (.logical (.ex σ))
  | _, .original (.eq σ) => .name (.logical (.eq σ))
  | _, .original (.constR ρ) => .name (.logical (.constR ρ))
  | _, .original (.negR ρ) => .name (.logical (.negR ρ))
  | _, .original (.andR ρ) => .name (.logical (.andR ρ))
  | _, .original (.orR ρ) => .name (.logical (.orR ρ))
  | _, .original (.coextR ρ) => .name (.logical (.coextR ρ))
  | _, .original (.boxR ρ) => .name (.logical (.boxR ρ))
  | _, .original (.inclR ρ) => .name (.logical (.inclR ρ))
  | _, .I ρ => .name (.I ρ)
  | _, .K σ ρ => .name (.K σ ρ)
  | _, .S σ τ ρ => .name (.S σ τ ρ)
  | _, .C σ τ ρ => .name (.C σ τ ρ)
  | _, .W σ ρ => .name (.W σ ρ)

def join : ConstMap (NamedConst C Name) (Constants (ModalConcreteToC.signature C))
  | σ, .old c => .original (Atoms.nonlogical (Sig := ModalConcreteToC.signature C) (Sigma.mk σ c))
  | _, .name (.I ρ) => .I ρ
  | _, .name (.K σ ρ) => .K σ ρ
  | _, .name (.S σ τ ρ) => .S σ τ ρ
  | _, .name (.C σ τ ρ) => .C σ τ ρ
  | _, .name (.W σ ρ) => .W σ ρ
  | _, .name (.logical o) => .original o.atom

theorem join_split {σ} (c : Constants (ModalConcreteToC.signature C) σ) :
    join (split c) = c := by
  cases c with
  | original c =>
      cases c with
      | nonlogical c => cases c; rfl
      | and => rfl
      | or => rfl
      | not => rfl
      | all => rfl
      | ex => rfl
      | eq σ => cases σ <;> simp only [split, join, LogicalOperator.atom] <;> rfl
      | constR => rfl
      | negR => rfl
      | andR => rfl
      | orR => rfl
      | coextR => rfl
      | boxR => rfl
      | inclR => rfl
  | I => rfl
  | K => rfl
  | S => rfl
  | C => rfl
  | W => rfl

theorem split_join {σ} (c : NamedConst C Name σ) : split (join c) = c := by
  cases c with
  | old c => rfl
  | name n =>
      cases n <;> try rfl
      case logical o =>
        cases o <;> try rfl
        case eq σ => cases σ <;> simp only [split, join, LogicalOperator.atom] <;> rfl

theorem mapTerm_join_split {Γ σ} (p : Term (Constants (ModalConcreteToC.signature C)) Γ σ) :
    mapTerm join (mapTerm split p) = p := by
  rw [mapTerm_comp]
  have hf : @Eq (ConstMap (Constants (ModalConcreteToC.signature C))
      (Constants (ModalConcreteToC.signature C))) (fun c => join (split c)) (fun c => c) := by
    funext σ c
    exact join_split c
  rw [hf, mapTerm_id]

theorem mapTerm_split_join {Γ σ} (p : Term (NamedConst C Name) Γ σ) :
    mapTerm split (mapTerm join p) = p := by
  rw [mapTerm_comp]
  have hf : @Eq (ConstMap (NamedConst C Name) (NamedConst C Name))
      (fun c => split (join c)) (fun c => c) := by
    funext σ c
    exact split_join c
  rw [hf, mapTerm_id]

theorem mapTerm_eq_translate (f : ConstMap C D) {Γ σ} (p : Term C Γ σ) :
    mapTerm f p = ModalFreshConstantSyntax.translate (fun c => .const (f c)) Sub.id p := by
  induction p <;>
    simp_all only [mapTerm, ModalFreshConstantSyntax.translate, Sub.lift_id] <;> rfl

theorem mapBody_eq_translate (f : ConstMap C D) {Γ} {ρ : RTy} (A : Body C Γ ρ) :
    mapBody f A = ModalFreshConstantSyntax.translateBody (fun c => .const (f c)) Sub.id A := by
  induction A with
  | atom p =>
      exact congrArg (ModalComprehensionRepresentation.AdmittedBody.atom (L := language D))
        (mapTerm_eq_translate f p)
  | bind A ih =>
      simp only [mapBody, ModalFreshConstantSyntax.translateBody, Sub.lift_id]
      exact congrArg (ModalComprehensionRepresentation.AdmittedBody.bind (L := language D)) ih

theorem mapBody_ofTerm (f : ConstMap C D) (ρ : RTy) : ∀ {Γ} (p : Term C Γ ρ),
    mapBody f (Body.ofTerm ρ p) = Body.ofTerm ρ (mapTerm f p) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [Body.ofTerm, mapBody, ih, mapTerm, mapTerm_wk]

/-- Signature maps cannot affect any of the independent defining bodies. -/
theorem Name.body_map {Γ} {ρ : RTy} (n : Name ρ) (f : ConstMap C D) :
    mapBody f (n.body (C := C) Γ) = n.body (C := D) Γ := by
  cases n with
  | I ρ => simp only [Name.body, CombinatorBody.I, mapBody, mapBody_ofTerm, mapTerm]
  | K σ ρ => simp only [Name.body, CombinatorBody.K, mapBody, mapBody_ofTerm, mapTerm]
  | S σ τ ρ => simp only [Name.body, CombinatorBody.S, mapBody, mapBody_ofTerm, mapTerm]
  | C σ τ ρ => simp only [Name.body, CombinatorBody.C, mapBody, mapBody_ofTerm, mapTerm]
  | W σ ρ => simp only [Name.body, CombinatorBody.W, mapBody, mapBody_ofTerm, mapTerm]
  | logical o =>
      rw [Name.body, mapBody_eq_translate, LogicalOperator.body_translate]
      rfl

theorem Name.body_subst {Γ Θ} {ρ : RTy} (n : Name ρ) (s : Sub C Γ Θ) :
    (n.body (C := C) Γ).subst s = n.body (C := C) Θ := by
  cases n with
  | I ρ => simp only [Name.body, CombinatorBody.I, Body.subst, Body.subst_ofTerm, Term.subst, Sub.lift]
  | K σ ρ => simp only [Name.body, CombinatorBody.K, Body.subst, Body.subst_ofTerm, Term.subst, Sub.lift]; rfl
  | S σ τ ρ => simp only [Name.body, CombinatorBody.S, Body.subst, Body.subst_ofTerm, Term.subst, Sub.lift]; rfl
  | C σ τ ρ => simp only [Name.body, CombinatorBody.C, Body.subst, Body.subst_ofTerm, Term.subst, Sub.lift]; rfl
  | W σ ρ => simp only [Name.body, CombinatorBody.W, Body.subst, Body.subst_ofTerm, Term.subst, Sub.lift]; rfl
  | logical o => exact o.body_subst s

theorem Name.body_rename {Γ Θ} {ρ : RTy} (n : Name ρ) (r : Ren Γ Θ) :
    (n.body (C := C) Γ).rename r = n.body (C := C) Θ := by
  have h := Body.subst_rename (Sub.id : Sub C Θ Θ) r (n.body (C := C) Γ)
  rw [Body.subst_id, Name.body_subst] at h
  exact h

/-- The open instances are exactly weakenings of the independent CLOSED
old-language body supplied to finite-name elimination. -/
theorem closedBody_at {ρ : RTy} (n : Name ρ) (Γ : Ctx) :
    (closedBody C n).rename (ModalFreshConstantSyntax.emptyRen Γ) = n.body (C := C) Γ :=
  n.body_rename _

#print axioms join_split
#print axioms split_join
#print axioms Name.body_map
#print axioms closedBody_at

end Classicism.Research.ModalReconstructionNames
