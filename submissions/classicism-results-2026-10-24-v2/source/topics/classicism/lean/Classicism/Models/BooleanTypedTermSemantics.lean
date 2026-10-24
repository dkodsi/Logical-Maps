import Classicism.Models.BooleanTypedHierarchy
import Classicism.Models.BooleanFirstOrderSemantics
import Mathlib.Order.Hom.BoundedLattice

/-!
# Actual typed term interpretation in the supported Boolean hierarchy

Original supporting formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md`, sections 3--4
(unpaginated). Open pure terms denote equivariant maps preserving Boolean
equality. Abstraction constructs a coherent predicate and derives its finite
support from the finite environment. The logical constants are actual
empty-supported profiles, with quantifiers ranging over the constructed
typed domains.

This is a syntax interpretation and a term-comprehension construction. It
does not assume or assert a C-model certificate, proof-system soundness,
Boolean model extraction, mixing, or any Choice/separation verdict.
-/

namespace Classicism.Meta.ChoiceBoolean.TypedTermSemantics

variable {K B : Type} [CompleteBooleanAlgebra B]
variable {a : BooleanAction K B}

noncomputable section

/-- A coherent equivariant map between the actual action spaces. -/
structure Map (X Y : ActionSpace a) where
  toFun : X.space.Carrier → Y.space.Carrier
  congr : ∀ x y, X.space.eqv x y ≤ Y.space.eqv (toFun x) (toFun y)
  equivariant : ∀ π x, toFun (X.action.act π x) = Y.action.act π (toFun x)

instance {X Y : ActionSpace a} : CoeFun (Map X Y)
    (fun _ => X.space.Carrier → Y.space.Carrier) := ⟨Map.toFun⟩

namespace Map

variable {X Y Z W : ActionSpace a}

def id (X : ActionSpace a) : Map X X where
  toFun x := x
  congr _ _ := le_rfl
  equivariant _ _ := rfl

def comp (g : Map Y Z) (f : Map X Y) : Map X Z where
  toFun x := g (f x)
  congr x y := (f.congr x y).trans (g.congr (f x) (f y))
  equivariant π x := by rw [f.equivariant, g.equivariant]

def fst (X Y : ActionSpace a) : Map (ActionSpace.product X Y) X where
  toFun := Prod.fst
  congr _ _ := inf_le_left
  equivariant _ _ := rfl

def snd (X Y : ActionSpace a) : Map (ActionSpace.product X Y) Y where
  toFun := Prod.snd
  congr _ _ := inf_le_right
  equivariant _ _ := rfl

def pair (f : Map X Y) (g : Map X Z) : Map X (ActionSpace.product Y Z) where
  toFun x := (f x, g x)
  congr x y := le_inf (f.congr x y) (g.congr x y)
  equivariant π x := Prod.ext (f.equivariant π x) (g.equivariant π x)

def const (X : ActionSpace a) (y : Y.space.Carrier)
    (hy : ∀ π, Y.action.act π y = y) : Map X Y where
  toFun _ := y
  congr _ _ := by rw [Y.space.refl]; exact le_top
  equivariant π _ := (hy π).symm

def unit (X : ActionSpace a) : Map X (ActionSpace.crisp a PUnit) :=
  const X PUnit.unit (fun _ => rfl)

theorem supports (f : Map X Y) {S : Set K} {x : X.space.Carrier}
    (hx : X.action.Supports S x) : Y.action.Supports S (f x) := by
  intro π hπ
  rw [← f.equivariant, hx π hπ]

theorem finitelySupported (f : Map X Y) {x : X.space.Carrier}
    (hx : X.action.FinitelySupported x) : Y.action.FinitelySupported (f x) := by
  obtain ⟨S, hS, hx⟩ := hx
  exact ⟨S, hS, f.supports hx⟩

end Map

/-- A coherent scalar expression which is semilinear under permutations. -/
structure Form (X : ActionSpace a) where
  pred : Predicate X.space
  equivariant : ∀ π x, pred (X.action.act π x) = a.map π (pred x)

instance {X : ActionSpace a} : CoeFun (Form X) (fun _ => X.space.Carrier → B) :=
  ⟨fun f => f.pred.toFun⟩

namespace Form

variable {X Y Z : ActionSpace a}

def pullback (p : Form Y) (f : Map X Y) : Form X where
  pred :=
    { toFun x := p (f x)
      coherent x y :=
        (inf_le_inf_right _ (f.congr x y)).trans (p.pred.coherent (f x) (f y)) }
  equivariant π x := by
    change p (f (X.action.act π x)) = a.map π (p (f x))
    rw [f.equivariant, p.equivariant]

def neg (p : Form X) : Form X where
  pred := p.pred.neg
  equivariant π x := by
    change (p (X.action.act π x))ᶜ = a.map π (p x)ᶜ
    rw [p.equivariant, map_compl']

def inf (p q : Form X) : Form X where
  pred :=
    { toFun x := p x ⊓ q x
      coherent x y :=
        le_inf
          ((inf_le_inf_left _ inf_le_left).trans (p.pred.coherent x y))
          ((inf_le_inf_left _ inf_le_right).trans (q.pred.coherent x y)) }
  equivariant π x := by
    change p (X.action.act π x) ⊓ q (X.action.act π x) = a.map π (p x ⊓ q x)
    rw [p.equivariant, q.equivariant, (a.map π).map_inf]

def sup (p q : Form X) : Form X where
  pred :=
    { toFun x := p x ⊔ q x
      coherent x y := by
        rw [inf_sup_left]
        exact sup_le_sup (p.pred.coherent x y) (q.pred.coherent x y) }
  equivariant π x := by
    change p (X.action.act π x) ⊔ q (X.action.act π x) = a.map π (p x ⊔ q x)
    rw [p.equivariant, q.equivariant, (a.map π).map_sup]

/-- Material implication, with the ordinary Boolean meaning. -/
def imp (p q : Form X) : Form X := p.neg.sup q

theorem imp_apply (p q : Form X) (x : X.space.Carrier) :
    p.imp q x = p x ⇨ q x := by
  change (p x)ᶜ ⊔ q x = p x ⇨ q x
  rw [himp_eq, sup_comm]

/-- Actual evaluation is a coherent equivariant scalar expression. -/
def evaluation (X : ActionSpace a) :
    Form (ActionSpace.product (supportedPredicateSpace X) X) where
  pred :=
    { toFun p := Predicate.toFun (X := X.space) p.1.val p.2
      coherent p q := eval_subst p.1.val q.1.val p.2 q.2 }
  equivariant π p := actPredicate_eval X π p.1.val p.2

/-- Equality at every Boolean degree, rather than crisp meta-level equality. -/
def equality (X : ActionSpace a) : Form (ActionSpace.product X X) where
  pred :=
    { toFun p := X.space.eqv p.1 p.2
      coherent p q := FirstOrderSemantics.equality_subst X.space inf_le_left inf_le_right }
  equivariant π p := X.semilinear π p.1 p.2

/-- Quantifying all actual elements preserves semilinearity by reindexing. -/
def allRight (p : Form (ActionSpace.product X Y)) : Form X where
  pred := p.pred.forallRight
  equivariant π x := by
    change (⨅ y, p (X.action.act π x, y)) = a.map π (⨅ y, p (x, y))
    calc
      _ = ⨅ y, p (X.action.act π x, Y.action.act π y) :=
        (Y.action.actEquiv π).iInf_comp.symm
      _ = ⨅ y, a.map π (p (x, y)) := by
        apply iInf_congr
        intro y
        exact p.equivariant π (x, y)
      _ = a.map π (⨅ y, p (x, y)) := ((a.map π).map_iInf _).symm

def exRight (p : Form (ActionSpace.product X Y)) : Form X where
  pred := p.pred.existsRight
  equivariant π x := by
    change (⨆ y, p (X.action.act π x, y)) = a.map π (⨆ y, p (x, y))
    calc
      _ = ⨆ y, p (X.action.act π x, Y.action.act π y) :=
        (Y.action.actEquiv π).iSup_comp.symm
      _ = ⨆ y, a.map π (p (x, y)) := by
        apply iSup_congr
        intro y
        exact p.equivariant π (x, y)
      _ = a.map π (⨆ y, p (x, y)) := ((a.map π).map_iSup _).symm

theorem fixed (p : Form X) (π : Equiv.Perm K) :
    actPredicate X π p.pred = p.pred := by
  apply Predicate.ext
  intro x
  change a.map π (p (X.action.act π⁻¹ x)) = p x
  rw [← p.equivariant, X.action.act_inv_act]

/-- Every closed scalar expression gives an admitted empty-supported profile. -/
def entity (p : Form X) : SupportedPredicate X :=
  ⟨p.pred, ∅, Set.finite_empty, fun π _ => p.fixed π⟩

theorem entity_fixed (p : Form X) (π : Equiv.Perm K) :
    (supportedPredicateSpace X).action.act π p.entity = p.entity := by
  apply Subtype.ext
  exact p.fixed π

/-- Currying constructs the actual supported profile from a parameter value.
Its support is any finite support of that parameter, not an assumed closure law. -/
def curry (p : Form (ActionSpace.product X Y))
    (hX : ∀ x, X.action.FinitelySupported x) : Map X (supportedPredicateSpace Y) where
  toFun x :=
    ⟨p.pred.sectionLeft x, by
      obtain ⟨S, hS, hx⟩ := hX x
      refine ⟨S, hS, ?_⟩
      intro π hπ
      apply Predicate.ext
      intro y
      change a.map π (p (x, Y.action.act π⁻¹ y)) = p (x, y)
      have h := p.equivariant π (x, Y.action.act π⁻¹ y)
      change p (X.action.act π x, Y.action.act π (Y.action.act π⁻¹ y)) =
        a.map π (p (x, Y.action.act π⁻¹ y)) at h
      rw [hx π hπ, Y.action.act_inv_act] at h
      exact h.symm⟩
  congr x y := Predicate.sectionLeft_congr p.pred x y
  equivariant π x := by
    apply Subtype.ext
    apply Predicate.ext
    intro y
    change p (X.action.act π x, y) = a.map π (p (x, Y.action.act π⁻¹ y))
    have h := p.equivariant π (x, Y.action.act π⁻¹ y)
    change p (X.action.act π x, Y.action.act π (Y.action.act π⁻¹ y)) =
      a.map π (p (x, Y.action.act π⁻¹ y)) at h
    rw [Y.action.act_inv_act] at h
    exact h

theorem curry_apply (p : Form (ActionSpace.product X Y))
    (hX : ∀ x, X.action.FinitelySupported x) (x : X.space.Carrier) (y : Y.space.Carrier) :
    Predicate.toFun (X := Y.space) (p.curry hX x).val y = p (x, y) := rfl

end Form

open TypedHierarchy

variable (a : BooleanAction K B) (E : Type)

/-- Finite environments, with the same innermost-first order as actual Term. -/
def EnvSpace : Ctx → ActionSpace a
  | [] => ActionSpace.crisp a PUnit
  | σ :: Γ => ActionSpace.product (DomSpace a E σ) (EnvSpace Γ)

abbrev Env (Γ : Ctx) := (EnvSpace a E Γ).space.Carrier

theorem env_finitelySupported : ∀ Γ (g : Env a E Γ),
    (EnvSpace a E Γ).action.FinitelySupported g
  | [], g => ActionSpace.crisp_finitelySupported a PUnit g
  | σ :: Γ, g => ActionSpace.product_finitelySupported (DomSpace a E σ)
      (EnvSpace a E Γ) (dom_finitelySupported a E σ g.1)
      (env_finitelySupported Γ g.2)

def varMap : ∀ {Γ σ}, Var Γ σ → Map (EnvSpace a E Γ) (DomSpace a E σ)
  | _ :: Γ, σ, .zero => Map.fst (DomSpace a E σ) (EnvSpace a E Γ)
  | τ :: Γ, σ, .succ v =>
      (varMap v).comp (Map.snd (DomSpace a E τ) (EnvSpace a E Γ))

/-- Typed application, with both equal-degree substitution and equivariance proved. -/
def application (σ : Ty) (ρ : RTy) :
    Map (ActionSpace.product (DomSpace a E (.rel (σ ⇒ ρ))) (DomSpace a E σ))
      (DomSpace a E (.rel ρ)) where
  toFun p := app a E σ ρ p.1 p.2
  congr p q := app_congr a E σ ρ p.1 q.1 p.2 q.2
  equivariant π p := (app_semilinear a E π σ ρ p.1 p.2).symm

/-- Scalar evaluation for an arbitrary tuple expression. -/
def applyForm {X : ActionSpace a} (ρ : RTy)
    (f : Map X (DomSpace a E (.rel ρ))) (xs : Map X (TupleSpace a E ρ)) : Form X :=
  (Form.evaluation (TupleSpace a E ρ)).pullback (f.pair xs)

def truthForm {X : ActionSpace a} (p : Map X (DomSpace a E .t)) : Form X :=
  applyForm a E .t p (Map.unit X)

/-- Lambda is derived by coherent uncurrying and the actual finite-environment support. -/
def abstraction {Γ : Ctx} (σ : Ty) (ρ : RTy)
    (body : Map (EnvSpace a E (σ :: Γ)) (DomSpace a E (.rel ρ))) :
    Map (EnvSpace a E Γ) (DomSpace a E (.rel (σ ⇒ ρ))) :=
  let X := EnvSpace a E Γ
  let Y := DomSpace a E σ
  let Z := TupleSpace a E ρ
  let outer := Map.fst X (ActionSpace.product Y Z)
  let arg := (Map.fst Y Z).comp (Map.snd X (ActionSpace.product Y Z))
  let rest := (Map.snd Y Z).comp (Map.snd X (ActionSpace.product Y Z))
  (applyForm a E ρ (body.comp (arg.pair outer)) rest).curry
    (env_finitelySupported a E Γ)

theorem abstraction_profile {Γ : Ctx} (σ : Ty) (ρ : RTy)
    (body : Map (EnvSpace a E (σ :: Γ)) (DomSpace a E (.rel ρ)))
    (g : Env a E Γ) (x : Dom a E σ) (xs : Tuple a E ρ) :
    Predicate.toFun (X := (TupleSpace a E (σ ⇒ ρ)).space)
        (abstraction a E σ ρ body g).val (x, xs) =
      Predicate.toFun (X := (TupleSpace a E ρ).space) (body (x, g)).val xs := rfl

theorem abstraction_beta {Γ : Ctx} (σ : Ty) (ρ : RTy)
    (body : Map (EnvSpace a E (σ :: Γ)) (DomSpace a E (.rel ρ)))
    (g : Env a E Γ) (x : Dom a E σ) :
    app a E σ ρ (abstraction a E σ ρ body g) x = body (x, g) := by
  apply Subtype.ext
  apply Predicate.ext
  intro xs
  rfl

/-! The actual logical profiles. All binders below range over actual Dom/Tuple carriers. -/

def constProfile (ρ : RTy) : Form (TupleSpace a E (RTy.t ⇒ ρ)) :=
  truthForm a E (Map.fst (DomSpace a E .t) (TupleSpace a E ρ))

def negProfile (ρ : RTy) : Form (TupleSpace a E (ρ ⇒ ρ)) :=
  (applyForm a E ρ (Map.fst _ _) (Map.snd _ _)).neg

def andProfile (ρ : RTy) : Form (TupleSpace a E (ρ ⇒ ρ ⇒ ρ)) :=
  let X := DomSpace a E (.rel ρ)
  let T := TupleSpace a E ρ
  let first := Map.fst X (ActionSpace.product X T)
  let second := (Map.fst X T).comp (Map.snd X (ActionSpace.product X T))
  let rest := (Map.snd X T).comp (Map.snd X (ActionSpace.product X T))
  (applyForm a E ρ first rest).inf (applyForm a E ρ second rest)

def orProfile (ρ : RTy) : Form (TupleSpace a E (ρ ⇒ ρ ⇒ ρ)) :=
  let X := DomSpace a E (.rel ρ)
  let T := TupleSpace a E ρ
  let first := Map.fst X (ActionSpace.product X T)
  let second := (Map.fst X T).comp (Map.snd X (ActionSpace.product X T))
  let rest := (Map.snd X T).comp (Map.snd X (ActionSpace.product X T))
  (applyForm a E ρ first rest).sup (applyForm a E ρ second rest)

def eqProfile (σ : Ty) : Form (TupleSpace a E (σ ⇒ σ ⇒ RTy.t)) :=
  let X := DomSpace a E σ
  let U := TupleSpace a E .t
  (Form.equality X).pullback
    ((Map.fst X (ActionSpace.product X U)).pair
      ((Map.fst X U).comp (Map.snd X (ActionSpace.product X U))))

private def quantifierBody (σ : Ty) :
    Form (ActionSpace.product (DomSpace a E (.rel (σ ⇒ RTy.t))) (DomSpace a E σ)) :=
  applyForm a E (σ ⇒ RTy.t) (Map.fst _ _)
    ((Map.snd _ _).pair (Map.unit _))

def allProfile (σ : Ty) : Form (TupleSpace a E ((σ ⇒ RTy.t) ⇒ RTy.t)) :=
  (quantifierBody a E σ).allRight.pullback (Map.fst _ _)

def exProfile (σ : Ty) : Form (TupleSpace a E ((σ ⇒ RTy.t) ⇒ RTy.t)) :=
  (quantifierBody a E σ).exRight.pullback (Map.fst _ _)

/-- Pointwise box is the identity in this Boolean-valued E₂ interpretation. -/
def boxProfile (ρ : RTy) : Form (TupleSpace a E (ρ ⇒ ρ)) :=
  applyForm a E ρ (Map.fst _ _) (Map.snd _ _)

def inclProfile (ρ : RTy) : Form (TupleSpace a E (ρ ⇒ ρ ⇒ RTy.t)) :=
  let X := DomSpace a E (.rel ρ)
  let T := TupleSpace a E ρ
  let U := TupleSpace a E .t
  let XX := ActionSpace.product X X
  let first := (Map.fst X X).comp (Map.fst XX T)
  let second := (Map.snd X X).comp (Map.fst XX T)
  let rest := Map.snd XX T
  let body := (applyForm a E ρ first rest).imp (applyForm a E ρ second rest)
  body.allRight.pullback
    ((Map.fst X (ActionSpace.product X U)).pair
      ((Map.fst X U).comp (Map.snd X (ActionSpace.product X U))))

/-- Use a proved empty-supported profile as a constant in any finite context. -/
def logical {Γ : Ctx} {ρ : RTy} (p : Form (TupleSpace a E ρ)) :
    Map (EnvSpace a E Γ) (DomSpace a E (.rel ρ)) :=
  Map.const (EnvSpace a E Γ) p.entity p.entity_fixed

/-- Interpretation of the actual pure Term syntax; no semantic closure hypothesis. -/
def denote : ∀ {Γ σ}, Term Signature.pure Γ σ → Map (EnvSpace a E Γ) (DomSpace a E σ)
  | _, _, .var v => varMap a E v
  | _, _, .const c => nomatch c
  | _, _, .app (σ := σ) (ρ := ρ) f x =>
      (application a E σ ρ).comp ((denote f).pair (denote x))
  | _, _, .lam (σ := σ) (ρ := ρ) body => abstraction a E σ ρ (denote body)
  | _, _, .and => logical a E (andProfile a E .t)
  | _, _, .or => logical a E (orProfile a E .t)
  | _, _, .not => logical a E (negProfile a E .t)
  | _, _, .all σ => logical a E (allProfile a E σ)
  | _, _, .ex σ => logical a E (exProfile a E σ)
  | _, _, .eq σ => logical a E (eqProfile a E σ)
  | _, _, .constR ρ => logical a E (constProfile a E ρ)
  | _, _, .negR ρ => logical a E (negProfile a E ρ)
  | _, _, .andR ρ => logical a E (andProfile a E ρ)
  | _, _, .orR ρ => logical a E (orProfile a E ρ)
  | _, _, .coextR ρ => logical a E (eqProfile a E (.rel ρ))
  | _, _, .boxR ρ => logical a E (boxProfile a E ρ)
  | _, _, .inclR ρ => logical a E (inclProfile a E ρ)

def value {Γ : Ctx} (p : Formula Signature.pure Γ) (g : Env a E Γ) : B :=
  Predicate.toFun (X := (TupleSpace a E .t).space) (denote a E p g).val PUnit.unit

theorem denote_congr {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ)
    (g h : Env a E Γ) :
    (EnvSpace a E Γ).space.eqv g h ≤
      (DomSpace a E σ).space.eqv (denote a E t g) (denote a E t h) :=
  (denote a E t).congr g h

theorem denote_semilinear {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ)
    (π : Equiv.Perm K) (g : Env a E Γ) :
    denote a E t ((EnvSpace a E Γ).action.act π g) =
      (DomSpace a E σ).action.act π (denote a E t g) :=
  (denote a E t).equivariant π g

theorem denote_supports {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ)
    {S : Set K} {g : Env a E Γ} (hg : (EnvSpace a E Γ).action.Supports S g) :
    (DomSpace a E σ).action.Supports S (denote a E t g) :=
  (denote a E t).supports hg

/-- Every interpreted term is admitted, with finite support derived from its parameters. -/
theorem denote_finitelySupported {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ)
    (g : Env a E Γ) : (DomSpace a E σ).action.FinitelySupported (denote a E t g) :=
  (denote a E t).finitelySupported (env_finitelySupported a E Γ g)

theorem denote_lam_profile {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (body : Term Signature.pure (σ :: Γ) ρ) (g : Env a E Γ)
    (x : Dom a E σ) (xs : Tuple a E ρ) :
    Predicate.toFun (X := (TupleSpace a E (σ ⇒ ρ)).space)
        (denote a E (.lam body) g).val (x, xs) =
      Predicate.toFun (X := (TupleSpace a E ρ).space)
        (denote a E body (x, g)).val xs := rfl

theorem denote_beta {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (body : Term Signature.pure (σ :: Γ) ρ) (g : Env a E Γ) (x : Dom a E σ) :
    app a E σ ρ (denote a E (.lam body) g) x = denote a E body (x, g) :=
  abstraction_beta a E σ ρ (denote a E body) g x

theorem value_neg {Γ : Ctx} (p : Formula Signature.pure Γ) (g : Env a E Γ) :
    value a E (Term.neg p) g = (value a E p g)ᶜ := rfl

theorem value_conj {Γ : Ctx} (p q : Formula Signature.pure Γ) (g : Env a E Γ) :
    value a E (Term.conj p q) g = value a E p g ⊓ value a E q g := rfl

theorem value_disj {Γ : Ctx} (p q : Formula Signature.pure Γ) (g : Env a E Γ) :
    value a E (Term.disj p q) g = value a E p g ⊔ value a E q g := rfl

theorem value_all {Γ : Ctx} {σ : Ty} (p : Formula Signature.pure (σ :: Γ))
    (g : Env a E Γ) :
    value a E (Term.forall' p) g = ⨅ x : Dom a E σ, value a E p (x, g) := rfl

theorem value_ex {Γ : Ctx} {σ : Ty} (p : Formula Signature.pure (σ :: Γ))
    (g : Env a E Γ) :
    value a E (Term.exists' p) g = ⨆ x : Dom a E σ, value a E p (x, g) := rfl

theorem value_eq {Γ : Ctx} {σ : Ty} (s t : Term Signature.pure Γ σ)
    (g : Env a E Γ) : value a E (Term.eq' s t) g =
      (DomSpace a E σ).space.eqv (denote a E s g) (denote a E t g) := rfl

theorem value_congr {Γ : Ctx} (p : Formula Signature.pure Γ) (g h : Env a E Γ) :
    (EnvSpace a E Γ).space.eqv g h ≤ iffValue (value a E p g) (value a E p h) := by
  have hp := denote_congr a E p g h
  rw [truth_eqv] at hp
  exact hp

theorem value_semilinear {Γ : Ctx} (p : Formula Signature.pure Γ)
    (π : Equiv.Perm K) (g : Env a E Γ) :
    value a E p ((EnvSpace a E Γ).action.act π g) = a.map π (value a E p g) := by
  exact (congrArg
    (fun F : Dom a E .t =>
      Predicate.toFun (X := (TupleSpace a E .t).space) F.val PUnit.unit)
    (denote_semilinear a E p π g)).trans
      (actPredicate_eval (TupleSpace a E .t) π (denote a E p g).val PUnit.unit)

/-- Unary term comprehension is witnessed by the actual interpreted lambda.
Iterated actual lambdas provide the corresponding finite-tuple instances. -/
theorem term_comprehension {Γ : Ctx} {σ : Ty}
    (p : Formula Signature.pure (σ :: Γ)) (g : Env a E Γ) :
    ∃ F : Dom a E (.rel (σ ⇒ RTy.t)),
      ∀ x : Dom a E σ,
        Predicate.toFun (X := (TupleSpace a E (σ ⇒ RTy.t)).space)
          F.val (x, PUnit.unit) = value a E p (x, g) :=
  ⟨denote a E (.lam p) g, fun _ => rfl⟩

end

end Classicism.Meta.ChoiceBoolean.TypedTermSemantics
