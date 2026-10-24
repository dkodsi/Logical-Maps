import Classicism.Results.Research.ModalReconstructionNames
import Classicism.Results.Research.ModalConstantMapDerivation
import Classicism.Results.Research.ModalIndependentNamedAxioms

/-!
# Exact proof adapter from compiler names to independent finite definitions

Original research, misc, 23 October 2026. The nested compiler signature is
split into old constants and relational names. Every named global axiom is
identified with precisely the closed SC definition used by the independent
finite-name erasure development. Both proof directions are actual fixed-map
constructor inductions. No conservativity claim is assumed here.
-/

namespace Classicism.Research.ModalReconstructionNames
open Classicism.Meta (Ty RTy)
open ModalComprehensionConcreteSyntax
open ModalComprehensionRepresentation (diagram UniformRepresents)
open ModalLogicalOperators (Constants ExpandedNamedAxiom)
open ModalFreshConstantSyntax (closedAt emptyRen)
open ModalFiniteNameSupport

variable {C : Ty → Type}

theorem diagram_rename {D : Ty → Type} {Γ Θ} {ρ : RTy}
    (r : Ren Γ Θ) (A : Body D Γ ρ) (H : Term D Γ ρ) :
    (diagram A H).rename r = diagram (A.rename r) (H.rename r) := by
  induction A generalizing Θ with
  | atom p => rfl
  | bind A ih =>
      change Term.all ((diagram A (.app H.wk (.var .zero))).rename (Ren.lift r)) =
        Term.all (diagram (Body.rename (Ren.lift r) A)
          (.app (H.rename r).wk (.var .zero)))
      apply congrArg Term.all
      rw [ih]
      simp only [Term.rename, Term.rename_wk, Ren.lift]
      rfl

/-- The erasure theorem's closed definition is literally the open uniform
definition used by the compiler, after ordinary context weakening. -/
theorem nameDefinition_at {ρ : RTy} (n : Name ρ) (Γ : Ctx) :
    closedAt (nameDefinition (closedBody C) n) Γ =
      UniformRepresents (n.body (C := NamedConst C Name) Γ) (.const (.name n)) := by
  simp only [nameDefinition, closedBody, Name.body_map, closedAt,
    Term.box, Term.rename, diagram_rename, Name.body_rename, UniformRepresents] <;> rfl

theorem split_definition {Γ} {ρ : RTy} (n : Name ρ) :
    mapTerm split
      (UniformRepresents (n.body (C := Constants (ModalConcreteToC.signature C)) Γ)
        (.const (join (.name n)))) =
      closedAt (nameDefinition (closedBody C) n) Γ := by
  rw [nameDefinition_at]
  change Term.box (mapTerm split (diagram
    (n.body (C := Constants (ModalConcreteToC.signature C)) Γ)
    (Term.const (join (NamedConst.name n))))) =
      Term.box (diagram (n.body (C := NamedConst C Name) Γ) (Term.const (NamedConst.name n)))
  have hd := mapTerm_diagram split
    (n.body (C := Constants (ModalConcreteToC.signature C)) Γ)
    (Term.const (join (NamedConst.name n)))
  have hb := congrArg (fun p : Formula (NamedConst C Name) Γ => Term.box p) hd
  simpa only [Name.body_map, mapTerm, split_join] using hb

theorem join_definition {Γ} {ρ : RTy} (n : Name ρ) :
    mapTerm join (closedAt (nameDefinition (closedBody C) n) Γ) =
      UniformRepresents (n.body (C := Constants (ModalConcreteToC.signature C)) Γ)
        (.const (join (.name n))) := by
  rw [nameDefinition_at]
  change Term.box (mapTerm join (diagram (n.body (C := NamedConst C Name) Γ)
    (Term.const (NamedConst.name n)))) =
      Term.box (diagram (n.body (C := Constants (ModalConcreteToC.signature C)) Γ)
        (Term.const (join (NamedConst.name n))))
  have hd := mapTerm_diagram join (n.body (C := NamedConst C Name) Γ)
    (Term.const (NamedConst.name n))
  have hb := congrArg (fun p : Formula (Constants (ModalConcreteToC.signature C)) Γ => Term.box p) hd
  simpa only [Name.body_map, mapTerm] using hb

theorem join_logical {ρ : RTy} (o : ModalLogicalOperators.LogicalOperator ρ) :
    join (C := C) (NamedConst.name (.logical o)) =
      RelationalBracketAbstraction.BasisConst.original o.atom := by
  cases o <;> try rfl
  case eq σ => cases σ <;> rfl

theorem expanded_definition {Γ Δ} {ρ : RTy} (n : Name ρ) :
    Derives (Constants (ModalConcreteToC.signature C))
      (ExpandedNamedAxiom (ModalConcreteToC.signature C)) Γ Δ
      (UniformRepresents (n.body Γ) (.const (join (.name n)))) := by
  cases n with
  | I ρ => exact .ax (.basis (.I ρ))
  | K σ ρ => exact .ax (.basis (.K σ ρ))
  | S σ τ ρ => exact .ax (.basis (.S σ τ ρ))
  | C σ τ ρ => exact .ax (.basis (.C σ τ ρ))
  | W σ ρ => exact .ax (.basis (.W σ ρ))
  | logical o =>
      simpa only [Name.body, join_logical, ModalLogicalOperators.named] using
        (Derives.ax (ExpandedNamedAxiom.logical (Sig := ModalConcreteToC.signature C) o)
          : Derives (Constants (ModalConcreteToC.signature C))
              (ExpandedNamedAxiom (ModalConcreteToC.signature C)) Γ Δ
              (UniformRepresents (o.body Γ) (ModalLogicalOperators.named o)))

theorem split_named_definition {Γ} {ρ : RTy} (n : Name ρ) :
    Derives (NamedConst C Name) (NamedAxioms (closedBody C)) Γ []
      (mapTerm split (UniformRepresents
        (n.body (C := Constants (ModalConcreteToC.signature C)) Γ)
        (.const (join (.name n))))) := by
  have h : Derives (NamedConst C Name) (NamedAxioms (closedBody C)) Γ []
      (closedAt (nameDefinition (closedBody C) n) Γ) := .ax (.definition n)
  exact (split_definition (C := C) (Γ := Γ) n).symm ▸ h

/-- Each individual source axiom has the required target derivation. -/
theorem split_axiom {Γ p}
    (h : ExpandedNamedAxiom (ModalConcreteToC.signature C) Γ p) :
    Derives (NamedConst C Name) (NamedAxioms (closedBody C)) Γ [] (mapTerm split p) := by
  cases h with
  | classical h => exact .ax (.classical (classical_map split h))
  | basis h =>
      cases h with
      | I ρ => exact split_named_definition (.I ρ)
      | K σ ρ => exact split_named_definition (.K σ ρ)
      | S σ τ ρ => exact split_named_definition (.S σ τ ρ)
      | C σ τ ρ => exact split_named_definition (.C σ τ ρ)
      | W σ ρ => exact split_named_definition (.W σ ρ)
  | logical o =>
      simpa only [Name.body, join_logical, ModalLogicalOperators.named] using
        (split_named_definition (C := C) (Γ := Γ) (.logical o))

theorem join_axiom {Γ p} (h : NamedAxioms (closedBody C) Γ p) :
    Derives (Constants (ModalConcreteToC.signature C))
      (ExpandedNamedAxiom (ModalConcreteToC.signature C)) Γ [] (mapTerm join p) := by
  cases h with
  | classical h => exact .ax (.classical (classical_map join h))
  | definition n =>
      rw [join_definition]
      exact expanded_definition n

/-- Actual transport into the exact global axiom package consumed by
independent finite-name erasure. Optional premises stay local. -/
theorem split_derives {Γ Δ p}
    (h : Derives (Constants (ModalConcreteToC.signature C))
      (ExpandedNamedAxiom (ModalConcreteToC.signature C)) Γ Δ p) :
    Derives (NamedConst C Name) (NamedAxioms (closedBody C)) Γ
      (Δ.map (mapTerm split)) (mapTerm split p) :=
  derives_map split (fun _ _ h => split_axiom h) h

theorem join_derives {Γ Δ p}
    (h : Derives (NamedConst C Name) (NamedAxioms (closedBody C)) Γ Δ p) :
    Derives (Constants (ModalConcreteToC.signature C))
      (ExpandedNamedAxiom (ModalConcreteToC.signature C)) Γ
      (Δ.map (mapTerm join)) (mapTerm join p) :=
  derives_map join (fun _ _ h => join_axiom h) h

/-- This is an equivalence of the two EXPLICIT naming presentations, not
the conservativity theorem that removes all names. -/
theorem expanded_derives_iff {Γ Δ p} :
    Derives (Constants (ModalConcreteToC.signature C))
      (ExpandedNamedAxiom (ModalConcreteToC.signature C)) Γ Δ p ↔
    Derives (NamedConst C Name) (NamedAxioms (closedBody C)) Γ
      (Δ.map (mapTerm split)) (mapTerm split p) := by
  constructor
  · exact split_derives
  · intro h
    have hj := join_derives h
    have hid : Δ.map (fun x => x) = Δ := by
      induction Δ <;> simp_all
    simpa only [List.map_map, Function.comp_def, mapTerm_join_split, hid] using hj

def oldCompiler : ConstMap C (Constants (ModalConcreteToC.signature C)) :=
  fun c => join (.old c)

theorem split_old {Γ σ} (p : Term C Γ σ) :
    mapTerm split (mapTerm oldCompiler p) = mapTerm NamedConst.old p := by
  rw [mapTerm_comp]
  rfl

#print axioms nameDefinition_at
#print axioms split_derives
#print axioms join_derives
#print axioms expanded_derives_iff

end Classicism.Research.ModalReconstructionNames
