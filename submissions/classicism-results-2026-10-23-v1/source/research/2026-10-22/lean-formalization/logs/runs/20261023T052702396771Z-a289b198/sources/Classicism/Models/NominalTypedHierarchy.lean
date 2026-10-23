import Classicism.Models.NominalLogicalOperations
import Classicism.Syntax.Term

/-!
# The exact supported relational hierarchy and its term interpretation

The individual domain is the ordinary natural numbers with trivial action.
Every relational arrow contains ALL supported functions, recursively, and the
truth domain contains ALL supported world subsets. Contexts use finite products.
All actual Term constructors, including all seven recursive relational
operations and lambda abstraction, receive a closed interpretation. No typed
closure or equivariance obligation is a premise of the construction.

The evaluator here covers the pure signature and, more generally, signatures
whose specified constants are globally fixed. It is not yet the C soundness
theorem, nor a proof of the Choice/Infinity classifications.

Sources: nominal-choice-classification-20261022.md §§1–2 and
support-bounds-world-geometry-20261022.md construction; original local research,
unpaginated, misc. Ordinary classical metatheory, uncompiled candidate.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

namespace Hierarchy
variable (W : Nom A I)

mutual
  def dom : Ty → Nom A I
    | .e => trivialNom A I Nat
    | .var _ => trivialNom A I Nat
    | .rel ρ => rdom ρ
  def rdom : RTy → Nom A I
    | .t => propositions W
    | .arr σ ρ => exponential (dom σ) (rdom ρ)
end

def env : Ctx → Nom A I
  | [] => trivialNom A I Unit
  | σ :: Γ => productNom (dom W σ) (env Γ)

def lookup : ∀ {Γ σ}, Var Γ σ → Hom (env W Γ) (dom W σ)
  | _, _, .zero => first _ _
  | _, _, .succ v => (lookup v).comp (second _ _)

def constRel : (ρ : RTy) → Hom (propositions W) (rdom W ρ)
  | .t => Hom.id _
  | .arr σ ρ => (constantFunction (dom W σ) (rdom W ρ)).comp (constRel ρ)

def negRel : (ρ : RTy) → Hom (rdom W ρ) (rdom W ρ)
  | .t => truthUnary W Not
  | .arr _ ρ => postcompose (negRel ρ)

def andRel : (ρ : RTy) → Hom (productNom (rdom W ρ) (rdom W ρ)) (rdom W ρ)
  | .t => truthBinary W And
  | .arr _ ρ => pointwise₂ (andRel ρ)

def orRel : (ρ : RTy) → Hom (productNom (rdom W ρ) (rdom W ρ)) (rdom W ρ)
  | .t => truthBinary W Or
  | .arr _ ρ => pointwise₂ (orRel ρ)

def coextRel : (ρ : RTy) → Hom (productNom (rdom W ρ) (rdom W ρ)) (propositions W)
  | .t => truthBinary W (fun p q => (¬p ∨ q) ∧ (¬q ∨ p))
  | .arr σ ρ => (forallOp W (dom W σ)).comp (pointwise₂ (coextRel ρ))

def boxRel : (ρ : RTy) → Hom (rdom W ρ) (rdom W ρ)
  | .t => boxOp W
  | .arr _ ρ => postcompose (boxRel ρ)

def inclRel : (ρ : RTy) → Hom (productNom (rdom W ρ) (rdom W ρ)) (propositions W)
  | .t => truthBinary W (fun p q => ¬p ∨ q)
  | .arr σ ρ => (forallOp W (dom W σ)).comp (pointwise₂ (inclRel ρ))

/-- An explicit interpretation of nonlogical constants, with its stated scope. -/
structure FixedConstants (Sig : Signature) where
  value : ∀ c : Sig.Const, dom W (Sig.typeOf c)
  fixed : ∀ (c : Sig.Const) (g : G), (dom W (Sig.typeOf c)).obj.act g (value c) = value c

def pureConstants : FixedConstants W Signature.pure where
  value c := nomatch c
  fixed c := nomatch c

def constantTerm (Γ : Ctx) {X Y : Nom A I} (f : Hom X Y) :
    Hom (env W Γ) (exponential X Y) :=
  constant _ _ (element f) (element_fixed f)

/-- All typed syntax constructors are interpreted by admitted maps. -/
def denote {Sig : Signature} (C : FixedConstants W Sig) :
    ∀ {Γ σ}, Term Sig Γ σ → Hom (env W Γ) (dom W σ)
  | _, _, .var v => lookup W v
  | _, _, .const c => constant _ _ (C.value c) (C.fixed c)
  | _, _, .app f x => (evaluation _ _).comp ((denote C f).pair (denote C x))
  | _, _, .lam b => curry ((denote C b).comp (exchange _ _))
  | Γ, _, .and => constantTerm W Γ (curry (truthBinary W And))
  | Γ, _, .or => constantTerm W Γ (curry (truthBinary W Or))
  | Γ, _, .not => constantTerm W Γ (truthUnary W Not)
  | Γ, _, .all σ => constantTerm W Γ (forallOp W (dom W σ))
  | Γ, _, .ex σ => constantTerm W Γ (existsOp W (dom W σ))
  | Γ, _, .eq σ => constantTerm W Γ (curry (equality W (dom W σ)))
  | Γ, _, .constR ρ => constantTerm W Γ (constRel W ρ)
  | Γ, _, .negR ρ => constantTerm W Γ (negRel W ρ)
  | Γ, _, .andR ρ => constantTerm W Γ (curry (andRel W ρ))
  | Γ, _, .orR ρ => constantTerm W Γ (curry (orRel W ρ))
  | Γ, _, .coextR ρ => constantTerm W Γ (curry (coextRel W ρ))
  | Γ, _, .boxR ρ => constantTerm W Γ (boxRel W ρ)
  | Γ, _, .inclR ρ => constantTerm W Γ (curry (inclRel W ρ))

def pureDenote {Γ σ} (t : Term Signature.pure Γ σ) : Hom (env W Γ) (dom W σ) :=
  denote W (pureConstants W) t

/-- The value is in the exact supported domain, for every assignment. -/
theorem denote_supported {Sig : Signature} (C : FixedConstants W Sig)
    {Γ σ} (t : Term Sig Γ σ) (η : env W Γ) :
    Supported A (dom W σ).obj I ((denote W C t).fn η) :=
  (dom W σ).supported _

theorem denote_equivariant {Sig : Signature} (C : FixedConstants W Sig)
    {Γ σ} (t : Term Sig Γ σ) (η : env W Γ) (g : G) :
    (denote W C t).fn ((env W Γ).obj.act g η) =
      (dom W σ).obj.act g ((denote W C t).fn η) :=
  (denote W C t).comm g η

/-- Closed pure denotations are fixed under every atom permutation. -/
theorem closed_pure_fixed {σ} (t : Term Signature.pure [] σ) (g : G) :
    (dom W σ).obj.act g ((pureDenote W t).fn ()) = (pureDenote W t).fn () :=
  ((pureDenote W t).comm g ()).symm

@[simp] theorem denote_app {Sig : Signature} (C : FixedConstants W Sig)
    {Γ σ ρ} (f : Term Sig Γ (σ ⇒ ρ)) (x : Term Sig Γ σ) (η : env W Γ) :
    (denote W C (.app f x)).fn η = ((denote W C f).fn η).val ((denote W C x).fn η) := rfl

@[simp] theorem denote_lam {Sig : Signature} (C : FixedConstants W Sig)
    {Γ : Ctx} {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) (η : env W Γ) (x : dom W σ) :
    ((denote W C (.lam b)).fn η).val x = (denote W C b).fn (x, η) := rfl

/-- Satisfaction at a specified world of the constructed hierarchy. -/
def Holds {Sig : Signature} (C : FixedConstants W Sig) {Γ}
    (η : env W Γ) (w : W) (p : Formula Sig Γ) : Prop :=
  ((denote W C p).fn η).val w

@[simp] theorem holds_and {Sig : Signature} (C : FixedConstants W Sig) {Γ}
    (η : env W Γ) (w : W) (p q : Formula Sig Γ) :
    Holds W C η w (Term.conj p q) ↔ Holds W C η w p ∧ Holds W C η w q := Iff.rfl

@[simp] theorem holds_or {Sig : Signature} (C : FixedConstants W Sig) {Γ}
    (η : env W Γ) (w : W) (p q : Formula Sig Γ) :
    Holds W C η w (Term.disj p q) ↔ Holds W C η w p ∨ Holds W C η w q := Iff.rfl

@[simp] theorem holds_not {Sig : Signature} (C : FixedConstants W Sig) {Γ}
    (η : env W Γ) (w : W) (p : Formula Sig Γ) :
    Holds W C η w (Term.neg p) ↔ ¬Holds W C η w p := Iff.rfl

@[simp] theorem holds_all {Sig : Signature} (C : FixedConstants W Sig) {Γ σ}
    (η : env W Γ) (w : W) (p : Formula Sig (σ :: Γ)) :
    Holds W C η w (Term.forall' p) ↔
      ∀ x : dom W σ, Holds W C (Γ := σ :: Γ) (x, η) w p := Iff.rfl

@[simp] theorem holds_exists {Sig : Signature} (C : FixedConstants W Sig) {Γ σ}
    (η : env W Γ) (w : W) (p : Formula Sig (σ :: Γ)) :
    Holds W C η w (Term.exists' p) ↔
      ∃ x : dom W σ, Holds W C (Γ := σ :: Γ) (x, η) w p := Iff.rfl

@[simp] theorem holds_eq {Sig : Signature} (C : FixedConstants W Sig) {Γ σ}
    (η : env W Γ) (w : W) (a b : Term Sig Γ σ) :
    Holds W C η w (Term.eq' a b) ↔ (denote W C a).fn η = (denote W C b).fn η := Iff.rfl

end Hierarchy
end
end Classicism.Meta.Nominal
