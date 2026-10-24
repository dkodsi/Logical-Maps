import Classicism.Models.NominalSupportCore
import Classicism.Results.Research.InfinitaryComprehensionSupport
import Classicism.Results.Research.InfinitaryComprehensionStandardLaws

/-!
# Infinitary formulas in the full supported-function hierarchy

The individual object is a parameter of this construction. In particular it
need not carry the trivial action used in the earlier nominal hierarchy.
Truth values are propositions with trivial action, every relational arrow
contains exactly all supported external functions, and the sole world is Unit.
The actual infinitary grammar, including first-class necessity and arbitrary
set-sized conjunctions, is interpreted. Its evaluation is equivariant even
for parameter assignments which have no common support. Comprehension then
holds for every assignment which does have a common small support.

Source: research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md,
fixed-bound strictness construction (misc, 23 October 2026, unpaginated).
Ordinary semantic metatheory; source-only until the shared compiler accepts it.
-/

namespace Classicism.Research.InfinitaryComprehension.Nominal

open Classicism.Meta
open Classicism.Meta.Nominal

noncomputable section

variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

/-- Literal pointwise order on admitted world--argument profiles. -/
def ProfileLe (M : Henkin.Model.{0}) (Γ : Ctx)
    (R S : M.Dom (RTy.ofArgs Γ)) : Prop :=
  ∀ xs w, M.truth (Henkin.uncurry M Γ R xs) w →
    M.truth (Henkin.uncurry M Γ S xs) w

def ProfileNonzero (M : Henkin.Model.{0}) (Γ : Ctx)
    (R : M.Dom (RTy.ofArgs Γ)) : Prop :=
  ∃ xs w, M.truth (Henkin.uncurry M Γ R xs) w

def ProfileZero (M : Henkin.Model.{0}) (Γ : Ctx)
    (R : M.Dom (RTy.ofArgs Γ)) : Prop :=
  ∀ xs w, ¬ M.truth (Henkin.uncurry M Γ R xs) w

def ProfileAtom (M : Henkin.Model.{0}) (Γ : Ctx)
    (R : M.Dom (RTy.ofArgs Γ)) : Prop :=
  ProfileNonzero M Γ R ∧ ∀ B, ProfileLe M Γ B R → ProfileZero M Γ B ∨ B = R

/-- Semantic all-relational Atomicity, with its order and atoms explicit. -/
def AtomicProfiles (M : Henkin.Model.{0}) : Prop :=
  ∀ Γ R, ProfileNonzero M Γ R →
    ∃ T, ProfileAtom M Γ T ∧ ProfileLe M Γ T R

/-- Truth of every actual boxed-ND formula, not a formal model-of-C field. -/
def C5Valid (M : Henkin.Model.{0}) : Prop :=
  ∀ (Param : Ty → Type) (η : Henkin.Assignment M Param) (Γ) (σ)
    (xs : Henkin.Env M Γ) (w : M.World),
    M.truth (Henkin.eval M η
      (.box (Term.necessaryDistinctness (Param := Param) σ)) xs) w

def IntensionalityValid (M : Henkin.Model.{0}) : Prop :=
  ∀ (Param : Ty → Type) (η : Henkin.Assignment M Param) (Γ) (ρ : RTy)
    (f h : Term Param Γ ρ) (xs : Henkin.Env M Γ) (w : M.World),
    M.truth (Henkin.eval M η (.imp (.box (Term.coext ρ f h)) (.eq f h)) xs) w

namespace Hierarchy

variable (E : Nom A I)

mutual
  def dom : Ty → Nom A I
    | .e => E
    | .var _ => E
    | .rel ρ => rdom ρ
  def rdom : RTy → Nom A I
    | .t => trivialNom A I Prop
    | .arr σ ρ => exponential (dom σ) (rdom ρ)
end

/-- An actual interpretation on the unchanged supported carriers. -/
def model : Henkin.Model where
  Dom σ := dom E σ
  World := Unit
  truth p _ := p
  app f x := f.val x
  top := True
  bot := False
  neg := Not
  conj := And
  disj := Or
  imp p q := p → q
  iff := Iff
  eq a b := a = b
  boxObj := element (Hom.id (trivialNom A I Prop))
  iAnd _ p := ∀ i, p i
  iOr _ p := ∃ i, p i
  top_spec _ := True.intro
  bot_spec _ := id
  neg_spec _ _ := Iff.rfl
  conj_spec _ _ _ := Iff.rfl
  disj_spec _ _ _ := Iff.rfl
  imp_spec _ _ _ := Iff.rfl
  iff_spec _ _ _ := Iff.rfl
  eq_spec _ _ _ := Iff.rfl
  box_spec p _ := ⟨fun h _ => h, fun h => h ()⟩
  iAnd_spec _ _ _ := Iff.rfl
  iOr_spec _ _ _ := Iff.rfl

@[simp] theorem box_eq (p : (model E).Dom Ty.t) :
    (model E).app (model E).boxObj p = p := rfl

/-- Pointwise action on arbitrary parameter assignments; no common support
is assumed or needed for this action or for the evaluation theorem below. -/
def assignmentAction (Param : Ty → Type) : Action G where
  Carrier := Henkin.Assignment (model E) Param
  act g η := fun {σ} p => (dom E σ).obj.act g (η p)
  one_act η := by funext σ p; exact (dom E σ).obj.one_act (η p)
  mul_act g h η := by funext σ p; exact (dom E σ).obj.mul_act g h (η p)

def actEnv {Γ : Ctx} (g : G) (xs : Henkin.Env (model E) Γ) :
    Henkin.Env (model E) Γ := fun {σ} v => (dom E σ).obj.act g (xs v)

theorem actEnv_cons {Γ σ} (g : G) (x : (model E).Dom σ)
    (xs : Henkin.Env (model E) Γ) :
    @Eq (Henkin.Env (model E) (σ :: Γ))
      (actEnv E g (Henkin.Env.cons x xs))
      (Henkin.Env.cons ((dom E σ).obj.act g x) (actEnv E g xs)) := by
  funext τ v
  cases v <;> rfl

theorem app_act {σ : Ty} {ρ : RTy} (g : G)
    (f : (model E).Dom (σ ⇒ ρ)) (x : (model E).Dom σ) :
    (model E).app ((dom E (σ ⇒ ρ)).obj.act g f)
        ((dom E σ).obj.act g x) =
      (dom E ρ).obj.act g ((model E).app f x) := by
  exact (evaluation (dom E σ) (rdom E ρ)).comm g (f, x)

/-- Structural induction covers the actual infinitary syntax. In particular,
the branching index has no cardinal bound and is not counted as a parameter. -/
theorem eval_equivariant {Param : Ty → Type} {Γ σ}
    (a : Term Param Γ σ) (g : G)
    (η : Henkin.Assignment (model E) Param) (xs : Henkin.Env (model E) Γ) :
    Henkin.eval (model E) ((assignmentAction E Param).act g η) a
        (actEnv E g xs) =
      (dom E σ).obj.act g (Henkin.eval (model E) η a xs) := by
  induction a generalizing η with
  | var v => rfl
  | param p => rfl
  | app f a ihf iha =>
      change (model E).app _ _ = _
      rw [ihf, iha]
      exact app_act E g _ _
  | top => rfl
  | bot => rfl
  | neg p ih => exact congrArg Not (ih η xs)
  | conj p q ihp ihq => exact congrArg₂ And (ihp η xs) (ihq η xs)
  | disj p q ihp ihq => exact congrArg₂ Or (ihp η xs) (ihq η xs)
  | imp p q ihp ihq => exact congrArg₂ (fun p q : Prop => p → q) (ihp η xs) (ihq η xs)
  | iff p q ihp ihq => exact congrArg₂ Iff (ihp η xs) (ihq η xs)
  | eq a b iha ihb =>
      change (_ = _) = (_ = _)
      rw [iha, ihb]
      exact propext ((act_injective (dom E _).obj g).eq_iff)
  | boxOp =>
      exact (element_fixed (Hom.id (trivialNom A I Prop)) g).symm
  | @all Γ σ p ih =>
      change (∀ x, Henkin.eval (model E) _ p (Henkin.Env.cons x _)) =
        (∀ x, Henkin.eval (model E) η p (Henkin.Env.cons x xs))
      apply propext
      constructor
      · intro h x
        have hx := h ((dom E σ).obj.act g x)
        rw [← actEnv_cons, ih] at hx
        exact hx
      · intro h x
        have hx := ih η (xs := Henkin.Env.cons ((dom E σ).obj.act g⁻¹ x) xs)
        rw [actEnv_cons E (σ := σ) g ((dom E σ).obj.act g⁻¹ x) xs] at hx
        have hc := congrArg (fun y : (model E).Dom σ =>
          Henkin.eval (model E) ((assignmentAction E Param).act g η) p
            (Henkin.Env.cons y (actEnv E g xs))) (act_inv (dom E σ).obj g x)
        exact Eq.mpr (hc.symm.trans hx) (h ((dom E σ).obj.act g⁻¹ x))
  | @ex Γ σ p ih =>
      change (∃ x, Henkin.eval (model E) _ p (Henkin.Env.cons x _)) =
        (∃ x, Henkin.eval (model E) η p (Henkin.Env.cons x xs))
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨(dom E σ).obj.act g⁻¹ x, ?_⟩
        have he := ih η (xs := Henkin.Env.cons ((dom E σ).obj.act g⁻¹ x) xs)
        rw [actEnv_cons E (σ := σ) g ((dom E σ).obj.act g⁻¹ x) xs] at he
        have hc := congrArg (fun y : (model E).Dom σ =>
          Henkin.eval (model E) ((assignmentAction E Param).act g η) p
            (Henkin.Env.cons y (actEnv E g xs))) (act_inv (dom E σ).obj g x)
        exact Eq.mp (hc.symm.trans he) hx
      · rintro ⟨x, hx⟩
        refine ⟨(dom E σ).obj.act g x, ?_⟩
        rw [← actEnv_cons, ih]
        exact hx
  | iAnd J p ih =>
      change (∀ j, Henkin.eval (model E) _ (p j) _) =
        (∀ j, Henkin.eval (model E) η (p j) xs)
      exact congrArg (fun f : J → Prop => ∀ j, f j) (funext (fun j => ih j η xs))
  | iOr J p ih =>
      change (∃ j, Henkin.eval (model E) _ (p j) _) =
        (∃ j, Henkin.eval (model E) η (p j) xs)
      exact congrArg (fun f : J → Prop => ∃ j, f j) (funext (fun j => ih j η xs))

@[reducible] def env : Ctx → Nom A I
  | [] => trivialNom A I Unit
  | σ :: Γ => productNom (dom E σ) (env Γ)

def toEnv : (Γ : Ctx) → env E Γ → Henkin.Env (model E) Γ
  | [], _ => Henkin.Env.nil
  | _ :: Γ, z => Henkin.Env.cons z.1 (toEnv Γ z.2)

def ofEnv : (Γ : Ctx) → Henkin.Env (model E) Γ → env E Γ
  | [], _ => ()
  | _ :: Γ, xs => (xs .zero, ofEnv Γ (Henkin.Env.tail xs))

theorem toEnv_ofEnv (Γ : Ctx) (xs : Henkin.Env (model E) Γ) :
    @Eq (Henkin.Env (model E) Γ) (toEnv E Γ (ofEnv E Γ xs)) xs := by
  induction Γ with
  | nil => exact (Henkin.Env.nil_eta xs).symm
  | cons σ Γ ih =>
      funext τ v
      cases v with
      | zero => rfl
      | succ v =>
          exact congrArg (fun ys : Henkin.Env (model E) Γ => ys v)
            (ih (Henkin.Env.tail xs))

theorem toEnv_act (Γ : Ctx) (g : G) (xs : env E Γ) :
    @Eq (Henkin.Env (model E) Γ) (toEnv E Γ ((env E Γ).obj.act g xs))
      (actEnv E g (toEnv E Γ xs)) := by
  induction Γ with
  | nil =>
      funext σ v
      cases v
  | cons σ Γ ih =>
      funext τ v
      cases v with
      | zero => rfl
      | succ v =>
          exact congrArg (fun ys : Henkin.Env (model E) Γ => ys v) (ih xs.2)

/-- Simultaneous finite currying in the actual supported-function domains. -/
def curryMany {Z : Nom A I} : (Γ : Ctx) →
    Hom (productNom Z (env E Γ)) (rdom E .t) → Hom Z (rdom E (RTy.ofArgs Γ))
  | [], f =>
      ⟨fun z => f.fn (z, ()), fun g z => f.comm g (z, ())⟩
  | σ :: Γ, f =>
      Classicism.Meta.Nominal.curry (curryMany (Z := productNom Z (dom E σ)) Γ
        { fn := fun z => f.fn (z.1.1, (z.1.2, z.2))
          comm := fun g z => f.comm g (z.1.1, (z.1.2, z.2)) })

theorem curryMany_spec {Z : Nom A I} (Γ : Ctx)
    (f : Hom (productNom Z (env E Γ)) (rdom E .t)) (z : Z) (xs : env E Γ) :
    Henkin.uncurry (model E) Γ ((curryMany E Γ f).fn z) (toEnv E Γ xs) =
      f.fn (z, xs) := by
  induction Γ generalizing Z with
  | nil => cases xs; rfl
  | cons σ Γ ih =>
      change Henkin.uncurry (model E) Γ
        ((curryMany E (Z := productNom Z (dom E σ)) Γ _).fn (z, xs.1))
        (toEnv E Γ xs.2) = _
      exact ih (Z := productNom Z (dom E σ)) _ (z, xs.1) xs.2

def assignments (Param : Ty → Type) : Nom A I :=
  part A (assignmentAction E Param) I

def evalHom {Param : Ty → Type} {Γ} (a : Formula Param Γ) :
    Hom (productNom (assignments E Param) (env E Γ)) (rdom E .t) where
  fn z := Henkin.eval (model E) z.1.val a (toEnv E Γ z.2)
  comm g z := by
    change Henkin.eval (model E) ((assignmentAction E Param).act g z.1.val) a
      (toEnv E Γ ((env E Γ).obj.act g z.2)) = _
    rw [toEnv_act]
    exact eval_equivariant E a g z.1.val _

/-- The actual formula-level schema, for every supported assignment and every
arbitrary-set-branching matrix. No representation hypothesis is supplied. -/
theorem comprehension_of_supported {Param : Ty → Type}
    (η : Henkin.Assignment (model E) Param)
    (hη : Supported A (assignmentAction E Param) I η)
    {Γ} (a : Formula Param Γ) (w : (model E).World) :
    (model E).truth (Henkin.eval (model E) η a.comprehension Henkin.Env.nil) w := by
  apply (Henkin.eval_comprehension_iff (model E) η a w).2
  refine ⟨(curryMany E Γ (evalHom E a)).fn ⟨η, hη⟩, ?_⟩
  intro xs v
  have h := curryMany_spec E Γ (evalHom E a) ⟨η, hη⟩ (ofEnv E Γ xs)
  change Henkin.uncurry (model E) Γ ((curryMany E Γ (evalHom E a)).fn ⟨η, hη⟩)
      (toEnv E Γ (ofEnv E Γ xs)) =
    Henkin.eval (model E) η a (toEnv E Γ (ofEnv E Γ xs)) at h
  simp only [toEnv_ofEnv E Γ xs] at h
  exact Iff.of_eq h

/-- All relational objects are determined by their fully saturated profiles. -/
theorem faithful : Henkin.Faithful (model E) := by
  intro Γ
  induction Γ with
  | nil =>
      intro R S h
      exact propext (h Henkin.Env.nil ())
  | cons σ Γ ih =>
      intro R S h
      apply Subtype.ext
      funext x
      apply ih
      intro xs w
      exact h (Henkin.Env.cons x xs) w

/-- Coextension is read on the actual supported domains at every argument. -/
def Coext : (ρ : RTy) → rdom E ρ → rdom E ρ → Prop
  | .t, p, q => p ↔ q
  | .arr _ ρ, f, h => ∀ x, Coext ρ (f.val x) (h.val x)

theorem coext_ext (ρ : RTy) (f h : rdom E ρ) (hc : Coext E ρ f h) : f = h := by
  induction ρ using RTy.induction with
  | t => exact propext hc
  | arr σ ρ ih =>
      apply Subtype.ext
      funext x
      exact ih _ _ (hc x)

theorem eval_coext {Param : Ty → Type} (η : Henkin.Assignment (model E) Param)
    (ρ : RTy) : ∀ {Γ} (f h : Term Param Γ ρ) (xs : Henkin.Env (model E) Γ),
      Henkin.eval (model E) η (Term.coext ρ f h) xs ↔
        Coext E ρ (Henkin.eval (model E) η f xs) (Henkin.eval (model E) η h xs) := by
  induction ρ using RTy.induction with
  | t => intros; exact Iff.rfl
  | arr σ ρ ih =>
      intro Γ f h xs
      change (∀ x, Henkin.eval (model E) η
        (Term.coext ρ
          (.app (f.rename (fun v => .succ v)) (.var .zero))
          (.app (h.rename (fun v => .succ v)) (.var .zero)))
        (Henkin.Env.cons x xs)) ↔ _
      have happ (k : Term Param Γ (σ ⇒ ρ)) (x : (model E).Dom σ) :
          Henkin.eval (model E) η
            (.app (k.rename (fun v => .succ v)) (.var .zero))
            (Henkin.Env.cons (M := model E) (σ := σ) x xs) =
          (Henkin.eval (model E) η k xs).val x := by
        change (Henkin.eval (model E) η (k.rename (fun v => .succ v))
          (Henkin.Env.cons (M := model E) (σ := σ) x xs)).val x = _
        exact congrArg (fun z : (model E).Dom (σ ⇒ ρ) => z.val x)
          (Henkin.eval_rename (model E) η k (fun v => .succ v) xs
            (Henkin.Env.cons (M := model E) (σ := σ) x xs) (fun _ => rfl))
      constructor
      · intro hc x
        have hx := (ih
          (.app (f.rename (fun v => .succ v)) (.var .zero))
          (.app (h.rename (fun v => .succ v)) (.var .zero))
          (Henkin.Env.cons (M := model E) (σ := σ) x xs)).1 (hc x)
        exact Eq.mp (congrArg₂ (Coext E ρ) (happ f x) (happ h x)) hx
      · intro hc x
        apply (ih
          (.app (f.rename (fun v => .succ v)) (.var .zero))
          (.app (h.rename (fun v => .succ v)) (.var .zero))
          (Henkin.Env.cons (M := model E) (σ := σ) x xs)).2
        exact Eq.mpr (congrArg₂ (Coext E ρ) (happ f x) (happ h x)) (hc x)

/-- Literal all-relational Intensionality, including the propositional type. -/
theorem eval_intensionality {Param : Ty → Type}
    (η : Henkin.Assignment (model E) Param) {Γ} (ρ : RTy)
    (f h : Term Param Γ ρ) (xs : Henkin.Env (model E) Γ) (w : (model E).World) :
    (model E).truth (Henkin.eval (model E) η
      (.imp (.box (Term.coext ρ f h)) (.eq f h)) xs) w := by
  change Henkin.eval (model E) η (Term.coext ρ f h) xs → _ = _
  intro hc
  exact coext_ext E ρ _ _ ((eval_coext E η ρ f h xs).1 hc)

/-- The actual boxed Necessity-of-Distinctness formula, at every type. -/
theorem eval_C5 {Param : Ty → Type}
    (η : Henkin.Assignment (model E) Param) {Γ} (σ : Ty)
    (xs : Henkin.Env (model E) Γ) (w : (model E).World) :
    (model E).truth (Henkin.eval (model E) η
      (.box (Term.necessaryDistinctness (Param := Param) σ)) xs) w := by
  change ∀ x y : dom E σ, x ≠ y → x ≠ y
  exact fun _ _ h => h

theorem eval_box_eq_top {Param : Ty → Type}
    (η : Henkin.Assignment (model E) Param) {Γ} (p : Formula Param Γ)
    (xs : Henkin.Env (model E) Γ) (w : (model E).World) :
    (model E).truth (Henkin.eval (model E) η (.iff p.box (.eq p .top)) xs) w := by
  change Henkin.eval (model E) η p xs ↔ (Henkin.eval (model E) η p xs = True)
  exact ⟨fun hp => propext ⟨fun _ => trivial, fun _ => hp⟩,
    fun hp => Eq.mpr hp True.intro⟩

theorem eval_K {Param : Ty → Type}
    (η : Henkin.Assignment (model E) Param) {Γ} (p q : Formula Param Γ)
    (xs : Henkin.Env (model E) Γ) (w : (model E).World) :
    (model E).truth (Henkin.eval (model E) η
      (.imp (.box (.imp p q)) (.imp p.box q.box)) xs) w := by
  change (_ → _) → _ → _
  exact fun h hp => h hp

theorem eval_T {Param : Ty → Type}
    (η : Henkin.Assignment (model E) Param) {Γ} (p : Formula Param Γ)
    (xs : Henkin.Env (model E) Γ) (w : (model E).World) :
    (model E).truth (Henkin.eval (model E) η (.imp p.box p) xs) w := by
  exact id

def singletonHom (Γ : Ctx) : Hom (env E Γ) (rdom E (RTy.ofArgs Γ)) :=
  curryMany E Γ
    { fn := fun z => z.1 = z.2
      comm := fun g z => propext ((act_injective (env E Γ).obj g).eq_iff) }

def singletonRelation (Γ : Ctx) (xs : Henkin.Env (model E) Γ) :
    (model E).Dom (RTy.ofArgs Γ) := (singletonHom E Γ).fn (ofEnv E Γ xs)

theorem singletonRelation_spec (Γ : Ctx) (xs ys : Henkin.Env (model E) Γ) :
    Henkin.uncurry (model E) Γ (singletonRelation E Γ xs) ys ↔
      @Eq (Henkin.Env (model E) Γ) xs ys := by
  have h := curryMany_spec E Γ
    ({ fn := fun z : env E Γ × env E Γ => z.1 = z.2
       comm := fun g z => propext ((act_injective (env E Γ).obj g).eq_iff) } :
      Hom (productNom (env E Γ) (env E Γ)) (rdom E .t))
    (ofEnv E Γ xs) (ofEnv E Γ ys)
  rw [toEnv_ofEnv] at h
  change Henkin.uncurry (model E) Γ (singletonRelation E Γ xs) ys =
    (ofEnv E Γ xs = ofEnv E Γ ys) at h
  rw [h]
  constructor
  · intro he
    have he' := congrArg (fun z => (toEnv E Γ z : Henkin.Env (model E) Γ)) he
    simpa only [toEnv_ofEnv] using he'
  · intro he
    exact congrArg (ofEnv E Γ) he

/-- Every nonempty admitted profile has an admitted singleton subprofile.
The statement includes nullary propositions and every finite relational type. -/
theorem profile_atomic :
    ∀ (Γ : Ctx) (R : (model E).Dom (RTy.ofArgs Γ)),
      (∃ xs, Henkin.uncurry (model E) Γ R xs) →
      ∃ T : (model E).Dom (RTy.ofArgs Γ),
        (∃ xs, Henkin.uncurry (model E) Γ T xs) ∧
        (∀ xs, Henkin.uncurry (model E) Γ T xs → Henkin.uncurry (model E) Γ R xs) ∧
        ∀ B : (model E).Dom (RTy.ofArgs Γ),
          (∀ xs, Henkin.uncurry (model E) Γ B xs → Henkin.uncurry (model E) Γ T xs) →
          (∀ xs, ¬ Henkin.uncurry (model E) Γ B xs) ∨ B = T := by
  classical
  intro Γ R hR
  obtain ⟨xs, hxs⟩ := hR
  refine ⟨singletonRelation E Γ xs, ⟨xs, (singletonRelation_spec E Γ xs xs).2 rfl⟩,
    ?_, ?_⟩
  · intro ys hy
    have he := (singletonRelation_spec E Γ xs ys).1 hy
    exact Eq.mp (congrArg (fun zs : Henkin.Env (model E) Γ =>
      Henkin.uncurry (model E) Γ R zs) he) hxs
  · intro B hBT
    by_cases hB : ∃ ys, Henkin.uncurry (model E) Γ B ys
    · right
      obtain ⟨ys, hys⟩ := hB
      have he := (singletonRelation_spec E Γ xs ys).1 (hBT ys hys)
      have hxsB : Henkin.uncurry (model E) Γ B xs :=
        Eq.mpr (congrArg (fun zs : Henkin.Env (model E) Γ =>
          Henkin.uncurry (model E) Γ B zs) he) hys
      apply faithful E Γ
      intro zs _
      constructor
      · exact hBT zs
      · intro hz
        exact Eq.mp (congrArg (fun ts : Henkin.Env (model E) Γ =>
          Henkin.uncurry (model E) Γ B ts) ((singletonRelation_spec E Γ xs zs).1 hz)) hxsB
    · left
      intro ys hy
      exact hB ⟨ys, hy⟩

theorem atomic_profiles : AtomicProfiles (model E) := by
  intro Γ R hR
  obtain ⟨xs, w, hxs⟩ := hR
  obtain ⟨T, ⟨ys, hys⟩, hTR, hatom⟩ := profile_atomic E Γ R ⟨xs, hxs⟩
  refine ⟨T, ⟨⟨ys, (), hys⟩, ?_⟩, ?_⟩
  · intro B hBT
    rcases hatom B (fun zs hz => hBT zs () hz) with hz | he
    · exact Or.inl (fun zs _ => hz zs)
    · exact Or.inr he
  · exact fun zs _ => hTR zs

theorem c5_valid : C5Valid (model E) := by
  intro Param η Γ σ xs w
  exact eval_C5 E η σ xs w

theorem intensionality_valid : IntensionalityValid (model E) := by
  intro Param η Γ ρ f h xs w
  exact eval_intensionality E η ρ f h xs w

end Hierarchy

#print axioms Hierarchy.eval_equivariant
#print axioms Hierarchy.comprehension_of_supported
#print axioms Hierarchy.faithful
#print axioms Hierarchy.atomic_profiles
#print axioms Hierarchy.c5_valid
#print axioms Hierarchy.intensionality_valid

end
end Classicism.Research.InfinitaryComprehension.Nominal
