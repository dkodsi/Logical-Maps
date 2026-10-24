import Classicism.Results.Research.ModalComprehensionConcreteCalculus

/-!
# The classical and existence boundary of the lambda-free base

Original research, misc, 23 October 2026. Falsity is the admitted formula
`∀p:t. p`; UI proves ex-falso. Classical double-negation elimination and
type-e existence are explicitly displayed uniform GLOBAL axioms, not silently
imported from Lean or C. Relational inhabitation follows from strong SC.

The primitive B identification below is independent of those extra axioms.
It identifies B with any named representation of `p = top`, using actual
object identity. It does not add lambda syntax or a conversion rule.

Negation, conjunction and disjunction have the usual classical definitions
in the implication/falsity basis. This file does not yet certify the full
translation of every H rule or the round-trip identities of C's independent
logical constants; those remain explicit integration work.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open ModalComprehensionRepresentation (Represents)

def bottom {Const Γ} : Formula Const Γ := .all (.var .zero)
def neg {Const Γ} (p : Formula Const Γ) : Formula Const Γ := .imp p bottom
def conjunction {Const Γ} (p q : Formula Const Γ) : Formula Const Γ :=
  neg (.imp p (neg q))
def disjunction {Const Γ} (p q : Formula Const Γ) : Formula Const Γ :=
  .imp (neg p) q

/-- These are object axiom instances, not Lean's classical axioms. -/
inductive ClassicalAxioms (Const : Ty → Type) : Axioms Const
  | dne {Γ} (p : Formula Const Γ) :
      ClassicalAxioms Const Γ (.imp (neg (neg p)) p)
  | exists_e {Γ} : ClassicalAxioms Const Γ
      (.ex (.eq (.var (.zero : Var (Ty.e :: Γ) Ty.e)) (.var .zero)))

theorem bottom_elimination {Const Ax Γ Δ} (p : Formula Const Γ)
    (h : Derives Const Ax Γ Δ bottom) : Derives Const Ax Γ Δ p :=
  Derives.allE p h

theorem double_negation_elimination {Const Γ Δ} (p : Formula Const Γ)
    (h : Derives Const (ClassicalAxioms Const) Γ Δ (neg (neg p))) :
    Derives Const (ClassicalAxioms Const) Γ Δ p :=
  .impE (.ax (.dne p)) h

/-- Excluded middle in the displayed implication/falsity definition of ∨. -/
theorem defined_excluded_middle {Const Ax Γ Δ} (p : Formula Const Γ) :
    Derives Const Ax Γ Δ (disjunction p (neg p)) := .impI .hyp₀

def Body.truth (Const : Ty → Type) : (ρ : RTy) → {Γ : Ctx} → Body Const Γ ρ
  | .t, _ => .atom .top
  | _ ⇒ ρ, _ => .bind (Body.truth Const ρ)

/-- Strong finite-body SC supplies inhabitation at every relational type.
The existential witness is eliminated only inside the object proof calculus. -/
theorem relational_inhabitation (Const : Ty → Type) (Ax : Axioms Const)
    (ρ : RTy) {Γ} : Derives Const Ax Γ []
      (.ex (.eq (.var (.zero : Var (ρ :: Γ) ρ)) (.var .zero))) := by
  apply Derives.exE (Derives.comprehension (Body.truth Const ρ))
  exact Derives.exI (.var .zero) (Derives.eqRefl (.var .zero))

theorem individual_inhabitation (Const : Ty → Type) {Γ} :
    Derives Const (ClassicalAxioms Const) Γ []
      (.ex (.eq (.var (.zero : Var (Ty.e :: Γ) Ty.e)) (.var .zero))) :=
  .ax .exists_e

def boxIdentityBody {Const Γ} : Term Const (Ty.t :: Γ) Ty.t :=
  .eq (.var .zero) .top

/-- The primitive operator B itself represents the admitted body `p = top`.
Its defining condition is proved, not added as a modal axiom. -/
theorem primitive_box_representation (Const : Ty → Type) (Ax : Axioms Const) {Γ} :
    Derives Const Ax Γ []
      (Represents (L := language Const) .boxOp boxIdentityBody) := by
  apply Derives.nec
  apply Derives.allI
  exact (calculus Const Ax).box_identity (.var .zero)

/-- Literal operation identity eliminates B in favor of a chosen
representation of `p = top`; no pointwise-to-operation extensionality. -/
theorem primitive_box_identification {Const Ax Γ Δ}
    (D : Term Const Γ (RTy.t ⇒ RTy.t))
    (h : Derives Const Ax Γ Δ (Represents (L := language Const) D boxIdentityBody)) :
    Derives Const Ax Γ Δ (.eq D .boxOp) :=
  Derives.impE
    (Derives.impE
      (Derives.lift ((calculus Const Ax).representative_unique boxIdentityBody D .boxOp)) h)
    (Derives.lift (primitive_box_representation Const Ax))

#print axioms bottom_elimination
#print axioms relational_inhabitation
#print axioms primitive_box_identification

end Classicism.Research.ModalComprehensionConcreteSyntax
