import Classicism.Results.Research.InfinitaryComprehensionSyntax
import Classicism.Results.Research.InfinitaryComprehensionAtomicity

/-!
# Concrete Comprehension and faithful Henkin supports

Ordinary Lean metatheory, not a shallow proof of C. This module supplies an
explicit canonical, constant-domain interpretation of the actual infinitary
syntax. Its box ranges over every world and its equality is rigid literal
identity. Those semantic conditions are assumptions of this interpretation;
this file does not prove that abstract C5 models have such a representation.

Arrow domains are arbitrary carriers with an application operation. No full
function-space, atomicity, singleton-support, or Comprehension field is built
into `Model`. Comprehension is separately the truth of the actual formula
`Term.comprehension A` at a designated point, under every parameter assignment.
Its semantic witness theorem is proved by interpreting that formula.

From this schema and faithful relation profiles we derive arbitrary support
intersections and complements, and then Atomicity and Actuality using the
independent support theorem. With the additional, explicit assumption that
represented propositions distinguish different worlds, we derive singleton
world propositions and representation of every world--argument support.

Source: `research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md`,
sections 2--4 (misc, 23 October 2026, unpaginated). The missing abstract-C5
representation bridge remains separate from the conditional theorem here.
-/

namespace Classicism.Research.InfinitaryComprehension.Henkin

open Classicism.Meta

universe u

/-- Canonical constant-domain Henkin semantics; arrow carriers need not be full. -/
structure Model where
  Dom : Ty → Type u
  World : Type u
  truth : Dom Ty.t → World → Prop
  app : ∀ {σ : Ty} {ρ : RTy}, Dom (σ ⇒ ρ) → Dom σ → Dom ρ
  top : Dom Ty.t
  bot : Dom Ty.t
  neg : Dom Ty.t → Dom Ty.t
  conj : Dom Ty.t → Dom Ty.t → Dom Ty.t
  disj : Dom Ty.t → Dom Ty.t → Dom Ty.t
  imp : Dom Ty.t → Dom Ty.t → Dom Ty.t
  iff : Dom Ty.t → Dom Ty.t → Dom Ty.t
  eq : ∀ {σ}, Dom σ → Dom σ → Dom Ty.t
  boxObj : Dom (RTy.t ⇒ RTy.t)
  iAnd : (I : Type u) → (I → Dom Ty.t) → Dom Ty.t
  iOr : (I : Type u) → (I → Dom Ty.t) → Dom Ty.t
  top_spec : ∀ w, truth top w
  bot_spec : ∀ w, ¬ truth bot w
  neg_spec : ∀ p w, truth (neg p) w ↔ ¬ truth p w
  conj_spec : ∀ p q w, truth (conj p q) w ↔ truth p w ∧ truth q w
  disj_spec : ∀ p q w, truth (disj p q) w ↔ truth p w ∨ truth q w
  imp_spec : ∀ p q w, truth (imp p q) w ↔ (truth p w → truth q w)
  iff_spec : ∀ p q w, truth (iff p q) w ↔ (truth p w ↔ truth q w)
  eq_spec : ∀ {σ} (a b : Dom σ) w, truth (eq a b) w ↔ a = b
  box_spec : ∀ p w, truth (app boxObj p) w ↔ ∀ v, truth p v
  iAnd_spec : ∀ I p w, truth (iAnd I p) w ↔ ∀ i, truth (p i) w
  iOr_spec : ∀ I p w, truth (iOr I p) w ↔ ∃ i, truth (p i) w

abbrev Env (M : Model.{u}) (Γ : Ctx) := ∀ {σ}, Var Γ σ → M.Dom σ
abbrev Assignment (M : Model.{u}) (Param : Ty → Type u) := ∀ {σ}, Param σ → M.Dom σ

namespace Env

variable {M : Model.{u}}

def nil : Env M [] := fun v => nomatch v

def cons {Γ σ} (x : M.Dom σ) (env : Env M Γ) : Env M (σ :: Γ)
  | _, .zero => x
  | _, .succ v => env v

def tail {Γ σ} (env : Env M (σ :: Γ)) : Env M Γ := fun v => env (.succ v)

theorem nil_eta (env : Env M []) : @Eq (Env M []) env nil := by
  funext σ v
  cases v

theorem cons_eta {Γ σ} (env : Env M (σ :: Γ)) :
    @Eq (Env M (σ :: Γ)) (cons (env .zero) (tail env)) env := by
  funext τ v
  cases v <;> rfl

def append {Δ : Ctx} : {Γ : Ctx} → Env M Γ → Env M Δ → Env M (Γ ++ Δ)
  | [], _, env => env
  | _ :: _, xs, env => cons (xs .zero) (append (tail xs) env)

theorem append_embed {Γ Δ} (xs : Env M Γ) (env : Env M Δ)
    {σ} (v : Var Γ σ) : append xs env (Ren.embed Γ Δ v) = xs v := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih (tail xs)

theorem append_last (Γ : Ctx) (xs : Env M Γ) {σ}
    (x : M.Dom σ) : append xs (cons x nil) (lastVar Γ σ) = x := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih => exact ih (tail xs)

end Env

variable (M : Model.{u})

/-- Recursive interpretation; quantifiers retain their full current domains. -/
def eval {Param : Ty → Type u} (η : Assignment M Param) :
    {Γ : Ctx} → {σ : Ty} → Term Param Γ σ → Env M Γ → M.Dom σ
  | _, _, .var v, env => env v
  | _, _, .param p, _ => η p
  | _, _, .app f a, env => M.app (eval η f env) (eval η a env)
  | _, _, .top, _ => M.top
  | _, _, .bot, _ => M.bot
  | _, _, .neg p, env => M.neg (eval η p env)
  | _, _, .conj p q, env => M.conj (eval η p env) (eval η q env)
  | _, _, .disj p q, env => M.disj (eval η p env) (eval η q env)
  | _, _, .imp p q, env => M.imp (eval η p env) (eval η q env)
  | _, _, .iff p q, env => M.iff (eval η p env) (eval η q env)
  | _, _, .eq a b, env => M.eq (eval η a env) (eval η b env)
  | _, _, .boxOp, _ => M.boxObj
  | _, _, .all p, env => M.iAnd _ (fun x => eval η p (Env.cons x env))
  | _, _, .ex p, env => M.iOr _ (fun x => eval η p (Env.cons x env))
  | _, _, .iAnd I p, env => M.iAnd I (fun i => eval η (p i) env)
  | _, _, .iOr I p, env => M.iOr I (fun i => eval η (p i) env)

theorem eval_rename {Param : Ty → Type u} (η : Assignment M Param) :
    ∀ {Γ σ} (a : Term Param Γ σ) {Δ} (r : Ren Γ Δ)
      (env : Env M Γ) (env' : Env M Δ),
      (∀ {τ} (x : Var Γ τ), env' (r x) = env x) →
      eval M η (a.rename r) env' = eval M η a env := by
  intro Γ σ a
  induction a with
  | var x => intro Δ r env env' h; exact h x
  | param p => intros; rfl
  | app f a ihf iha =>
      intro Δ r env env' h
      simp only [Term.rename, eval, ihf r env env' h, iha r env env' h]
  | top => intros; rfl
  | bot => intros; rfl
  | neg p ih =>
      intro Δ r env env' h
      simp only [Term.rename, eval, ih r env env' h]
  | conj p q ihp ihq =>
      intro Δ r env env' h
      simp only [Term.rename, eval, ihp r env env' h, ihq r env env' h]
  | disj p q ihp ihq =>
      intro Δ r env env' h
      simp only [Term.rename, eval, ihp r env env' h, ihq r env env' h]
  | imp p q ihp ihq =>
      intro Δ r env env' h
      simp only [Term.rename, eval, ihp r env env' h, ihq r env env' h]
  | iff p q ihp ihq =>
      intro Δ r env env' h
      simp only [Term.rename, eval, ihp r env env' h, ihq r env env' h]
  | eq a b iha ihb =>
      intro Δ r env env' h
      simp only [Term.rename, eval, iha r env env' h, ihb r env env' h]
  | boxOp => intros; rfl
  | all p ih =>
      intro Δ r env env' h
      apply congrArg (M.iAnd _)
      funext x
      apply ih
      intro τ y
      cases y with
      | zero => rfl
      | succ y => exact h y
  | ex p ih =>
      intro Δ r env env' h
      apply congrArg (M.iOr _)
      funext x
      apply ih
      intro τ y
      cases y with
      | zero => rfl
      | succ y => exact h y
  | iAnd I p ih =>
      intro Δ r env env' h
      exact congrArg (M.iAnd I) (funext (fun i => ih i r env env' h))
  | iOr I p ih =>
      intro Δ r env env' h
      exact congrArg (M.iOr I) (funext (fun i => ih i r env env' h))

/-- A relational entity's full profile, evaluated on its finite arguments. -/
def uncurry : (Γ : Ctx) → M.Dom (RTy.ofArgs Γ) → Env M Γ → M.Dom Ty.t
  | [], f, _ => f
  | _ :: Γ, f, xs => uncurry Γ (M.app f (xs .zero)) (Env.tail xs)

theorem eval_applyVars {Param : Ty → Type u} (η : Assignment M Param) (Γ : Ctx) :
    ∀ {Δ} (f : Term Param Δ (RTy.ofArgs Γ))
      (xs : ∀ {σ}, Var Γ σ → Term Param Δ σ) (env : Env M Δ),
      eval M η (Term.applyVars Γ f xs) env =
        uncurry M Γ (eval M η f env) (fun v => eval M η (xs v) env) := by
  induction Γ with
  | nil => intros; rfl
  | cons σ Γ ih =>
      intro Δ f xs env
      exact ih (.app f (xs .zero)) (fun v => xs (.succ v)) env

theorem eval_compBody {Param : Ty → Type u} (η : Assignment M Param) {Γ : Ctx}
    (A : Formula Param Γ) (R : M.Dom (RTy.ofArgs Γ)) (xs : Env M Γ) :
    eval M η A.compBody (Env.append xs (Env.cons R Env.nil)) =
      M.iff (uncurry M Γ R xs) (eval M η A xs) := by
  unfold Term.compBody
  change M.iff
    (eval M η (Term.applyVars Γ (.var (lastVar Γ _))
      (fun v => .var (Ren.embed Γ _ v))) (Env.append xs (Env.cons R Env.nil)))
    (eval M η (A.rename (Ren.embed Γ _)) (Env.append xs (Env.cons R Env.nil))) = _
  rw [eval_applyVars]
  have hvars : @Eq (Env M Γ) (fun {σ} (v : Var Γ σ) =>
      eval M η (.var (Ren.embed Γ _ v)) (Env.append xs (Env.cons R Env.nil))) xs := by
    funext σ v
    exact Env.append_embed xs (Env.cons R Env.nil) v
  have hA := eval_rename M η A (Ren.embed Γ _) xs
    (Env.append xs (Env.cons R Env.nil))
    (fun v => Env.append_embed xs (Env.cons R Env.nil) v)
  have hR : eval M η (.var (lastVar Γ _)) (Env.append xs (Env.cons R Env.nil)) = R :=
    Env.append_last Γ xs R
  rw [hvars, hA, hR]

theorem eval_closeAll {Param : Ty → Type u} (η : Assignment M Param) (Γ : Ctx) :
    ∀ {Δ} (A : Formula Param (Γ ++ Δ)) (env : Env M Δ) (w : M.World),
      M.truth (eval M η (Term.closeAll Γ A) env) w ↔
        ∀ xs : Env M Γ, M.truth (eval M η A (Env.append xs env)) w := by
  induction Γ with
  | nil => intro Δ A env w; exact ⟨fun h _ => h, fun h => h Env.nil⟩
  | cons σ Γ ih =>
      intro Δ A env w
      change M.truth (eval M η (Term.closeAll Γ (.all A)) env) w ↔ _
      rw [ih]
      constructor
      · intro h xs
        exact (M.iAnd_spec _ _ w).1 (h (Env.tail xs)) (xs .zero)
      · intro h xs
        exact (M.iAnd_spec _ _ w).2 (fun x => h (Env.cons x xs))

/-- The semantic content is obtained from the actual boxed existential formula. -/
theorem eval_comprehension_iff {Param : Ty → Type u} (η : Assignment M Param)
    {Γ : Ctx} (A : Formula Param Γ) (w : M.World) :
    M.truth (eval M η A.comprehension Env.nil) w ↔
      ∃ R : M.Dom (RTy.ofArgs Γ), ∀ (xs : Env M Γ) (v : M.World),
        M.truth (uncurry M Γ R xs) v ↔ M.truth (eval M η A xs) v := by
  change M.truth (M.iOr _ (fun R => M.app M.boxObj
    (eval M η (Term.closeAll Γ A.compBody) (Env.cons R Env.nil)))) w ↔ _
  rw [M.iOr_spec]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro xs v
    have hb := (eval_closeAll M η Γ A.compBody _ v).1
      ((M.box_spec _ w).1 hR v) xs
    rw [eval_compBody] at hb
    exact (M.iff_spec _ _ v).1 hb
  · rintro ⟨R, hR⟩
    refine ⟨R, (M.box_spec _ w).2 ?_⟩
    intro v
    apply (eval_closeAll M η Γ A.compBody _ v).2
    intro xs
    rw [eval_compBody]
    exact (M.iff_spec _ _ v).2 (hR xs v)

/-- Validity at one designated point under every parameter assignment. -/
def Comp (w : M.World) : Prop :=
  ∀ (Param : Ty → Type u) (η : Assignment M Param) (Γ : Ctx)
    (A : Formula Param Γ), M.truth (eval M η A.comprehension Env.nil) w

/-- Faithfulness is a representation assumption, separate from Comprehension. -/
def Faithful : Prop :=
  ∀ (Γ : Ctx) (R S : M.Dom (RTy.ofArgs Γ)),
    (∀ (xs : Env M Γ) (w : M.World),
      M.truth (uncurry M Γ R xs) w ↔ M.truth (uncurry M Γ S xs) w) → R = S

def selfAssignment : Assignment M M.Dom := fun p => p

noncomputable def represent {w : M.World} (hc : Comp M w) {Γ : Ctx}
    (A : Formula M.Dom Γ) : M.Dom (RTy.ofArgs Γ) :=
  Classical.choose ((eval_comprehension_iff M (selfAssignment M) A w).1
    (hc M.Dom (selfAssignment M) Γ A))

theorem represent_spec {w : M.World} (hc : Comp M w) {Γ : Ctx}
    (A : Formula M.Dom Γ) (xs : Env M Γ) (v : M.World) :
    M.truth (uncurry M Γ (represent M hc A) xs) v ↔
      M.truth (eval M (selfAssignment M) A xs) v :=
  Classical.choose_spec ((eval_comprehension_iff M (selfAssignment M) A w).1
    (hc M.Dom (selfAssignment M) Γ A)) xs v

def relationMatrix (Γ : Ctx) (R : M.Dom (RTy.ofArgs Γ)) : Formula M.Dom Γ :=
  Term.applyVars Γ (.param R) (fun v => .var v)

theorem eval_relationMatrix (Γ : Ctx) (R : M.Dom (RTy.ofArgs Γ)) (xs : Env M Γ) :
    eval M (selfAssignment M) (relationMatrix M Γ R) xs = uncurry M Γ R xs := by
  unfold relationMatrix
  rw [eval_applyVars]
  rfl

/-- Actual Comprehension supplies the support closure; it is not an input field. -/
noncomputable def supportFamily {w : M.World} (hc : Comp M w) (hf : Faithful M)
    (Γ : Ctx) : SupportFamily (M.Dom (RTy.ofArgs Γ)) (M.World × Env M Γ) where
  holds R p := M.truth (uncurry M Γ R p.2) p.1
  ext h := hf Γ _ _ (fun xs v => h (v, xs))
  bottom := represent M hc (.bot : Formula M.Dom Γ)
  bottom_spec p := by
    intro hp
    exact M.bot_spec p.1 ((represent_spec M hc .bot p.2 p.1).1 hp)
  neg R := represent M hc (.neg (relationMatrix M Γ R))
  neg_spec R p := by
    rw [represent_spec]
    change M.truth (M.neg (eval M (selfAssignment M) (relationMatrix M Γ R) p.2)) p.1 ↔ _
    rw [eval_relationMatrix, M.neg_spec]
  inf S := represent M hc (.iAnd {R : M.Dom (RTy.ofArgs Γ) // S R}
    (fun R => relationMatrix M Γ R.val))
  inf_spec S p := by
    rw [represent_spec]
    change M.truth (M.iAnd {R : M.Dom (RTy.ofArgs Γ) // S R}
      (fun R => eval M (selfAssignment M) (relationMatrix M Γ R.val) p.2)) p.1 ↔ _
    rw [M.iAnd_spec]
    constructor
    · intro h R hR
      have hx := h ⟨R, hR⟩
      rw [eval_relationMatrix] at hx
      exact hx
    · intro h R
      rw [eval_relationMatrix]
      exact h R.val R.property

theorem comp_atomicity {w : M.World} (hc : Comp M w) (hf : Faithful M) (Γ : Ctx) :
    (supportFamily M hc hf Γ).Atomic :=
  (supportFamily M hc hf Γ).atomicity

theorem comp_actuality_at {w : M.World} (hc : Comp M w) (hf : Faithful M)
    (Γ : Ctx) (p : M.World × Env M Γ) :
    (supportFamily M hc hf Γ).ActualityAt p :=
  (supportFamily M hc hf Γ).actuality p

theorem comp_arbitrary_joins {w : M.World} (hc : Comp M w) (hf : Faithful M)
    (Γ : Ctx) (S : M.Dom (RTy.ofArgs Γ) → Prop) :
    (∀ a, S a → (supportFamily M hc hf Γ).Included a
      ((supportFamily M hc hf Γ).sup S)) ∧
    (∀ b, (∀ a, S a → (supportFamily M hc hf Γ).Included a b) →
      (supportFamily M hc hf Γ).Included ((supportFamily M hc hf Γ).sup S) b) :=
  (supportFamily M hc hf Γ).arbitrary_join S

/-- Proposition closure is already present in the infinitary term interpretation. -/
def propositionFamily (hf : Faithful M) : SupportFamily (M.Dom Ty.t) M.World where
  holds := M.truth
  ext h := hf [] _ _ (fun _ v => h v)
  bottom := M.bot
  bottom_spec := M.bot_spec
  neg := M.neg
  neg_spec := M.neg_spec
  inf S := M.iAnd {p : M.Dom Ty.t // S p} (fun p => p.val)
  inf_spec S v := by
    rw [M.iAnd_spec]
    exact ⟨fun h p hp => h ⟨p, hp⟩, fun h p => h p.val p.property⟩

/-- Canonical worlds must be observably different; arbitrary duplicate worlds need not be. -/
def WorldSeparated : Prop :=
  ∀ w v : M.World, w ≠ v → ∃ p : M.Dom Ty.t, M.truth p w ∧ ¬ M.truth p v

def worldCore (hf : Faithful M) (w : M.World) : M.Dom Ty.t :=
  (propositionFamily M hf).core w

theorem worldCore_spec (hf : Faithful M) (hs : WorldSeparated M)
    (w v : M.World) : M.truth (worldCore M hf w) v ↔ v = w := by
  classical
  constructor
  · intro hv
    by_cases h : v = w
    · exact h
    · obtain ⟨p, hpw, hpv⟩ := hs w v (fun h' => h h'.symm)
      exact False.elim (hpv ((propositionFamily M hf).core_below w p hpw v hv))
  · intro h
    subst v
    exact (propositionFamily M hf).holds_core w

/-- Finite tuple identity written using the actual infinitary syntax.
The index is the finite family of typed variables, lifted to the syntax universe. -/
def tupleEq {Γ : Ctx} (xs : Env M Γ) : Formula M.Dom Γ :=
  .iAnd (ULift.{u} (Sigma (fun σ => Var Γ σ)))
    (fun i => .eq (.var i.down.2) (.param (xs i.down.2)))

theorem eval_tupleEq {Γ : Ctx} (xs env : Env M Γ) (w : M.World) :
    M.truth (eval M (selfAssignment M) (tupleEq M xs) env) w ↔
      @Eq (Env M Γ) env xs := by
  change M.truth (M.iAnd (ULift.{u} (Sigma (fun σ => Var Γ σ)))
    (fun i => M.eq (env i.down.2) (xs i.down.2))) w ↔ _
  rw [M.iAnd_spec]
  constructor
  · intro h
    funext σ v
    exact (M.eq_spec _ _ w).1 (h ⟨⟨σ, v⟩⟩)
  · intro h
    intro i
    exact (M.eq_spec _ _ w).2 (congrArg (fun e : Env M Γ => e i.down.2) h)

/-- A syntactically fixed disjunction of named world and tuple conditions. -/
def supportMatrix (hf : Faithful M) (Γ : Ctx) (U : M.World × Env M Γ → Prop) :
    Formula M.Dom Γ :=
  .iOr {z : M.World × Env M Γ // U z}
    (fun z => .conj (.param (worldCore M hf z.val.1)) (tupleEq M z.val.2))

theorem eval_supportMatrix (hf : Faithful M) (hs : WorldSeparated M)
    (Γ : Ctx) (U : M.World × Env M Γ → Prop) (xs : Env M Γ) (w : M.World) :
    M.truth (eval M (selfAssignment M) (supportMatrix M hf Γ U) xs) w ↔ U (w, xs) := by
  change M.truth (M.iOr {z : M.World × Env M Γ // U z}
    (fun z => M.conj (worldCore M hf z.val.1)
      (eval M (selfAssignment M) (tupleEq M z.val.2) xs))) w ↔ _
  rw [M.iOr_spec]
  constructor
  · rintro ⟨z, hz⟩
    have hh := (M.conj_spec _ _ w).1 hz
    have hw := (worldCore_spec M hf hs z.val.1 w).1 hh.1
    have hx := (eval_tupleEq M z.val.2 xs w).1 hh.2
    have hp : @Eq (M.World × Env M Γ) (w, xs) z.val :=
      @Prod.ext M.World (Env M Γ) (w, xs) z.val hw hx
    exact hp.symm ▸ z.property
  · intro h
    refine ⟨⟨(w, xs), h⟩, (M.conj_spec _ _ w).2 ?_⟩
    exact ⟨(worldCore_spec M hf hs w w).2 rfl, (eval_tupleEq M xs xs w).2 rfl⟩

/-- Full relational supports are a conclusion, conditional on the stated canonical semantics. -/
theorem full_profiles {w : M.World} (hc : Comp M w) (hf : Faithful M)
    (hs : WorldSeparated M) (Γ : Ctx) (U : M.World × Env M Γ → Prop) :
    ∃ R : M.Dom (RTy.ofArgs Γ), ∀ (xs : Env M Γ) (v : M.World),
      M.truth (uncurry M Γ R xs) v ↔ U (v, xs) := by
  refine ⟨represent M hc (supportMatrix M hf Γ U), ?_⟩
  intro xs v
  exact (represent_spec M hc (supportMatrix M hf Γ U) xs v).trans
    (eval_supportMatrix M hf hs Γ U xs v)

/-- In particular, every subset of the separating world space is a proposition. -/
theorem full_propositions {w : M.World} (hc : Comp M w) (hf : Faithful M)
    (hs : WorldSeparated M) (U : M.World → Prop) :
    ∃ p : M.Dom Ty.t, ∀ v : M.World, M.truth p v ↔ U v := by
  obtain ⟨p, hp⟩ := full_profiles M hc hf hs [] (fun z => U z.1)
  exact ⟨p, fun v => hp Env.nil v⟩

/-- Every map with an allowed relational output is represented by application.
This is derived from full profiles and faithfulness, not assumed in `Model`. -/
theorem full_functions {w : M.World} (hc : Comp M w) (hf : Faithful M)
    (hs : WorldSeparated M) (σ : Ty) (Γ : Ctx)
    (f : M.Dom σ → M.Dom (RTy.ofArgs Γ)) :
    ∃ R : M.Dom (σ ⇒ RTy.ofArgs Γ), ∀ a : M.Dom σ, M.app R a = f a := by
  obtain ⟨R, hR⟩ := full_profiles M hc hf hs (σ :: Γ)
    (fun z => M.truth (uncurry M Γ (f (z.2 .zero)) (Env.tail z.2)) z.1)
  refine ⟨R, ?_⟩
  intro a
  apply hf Γ
  intro xs v
  exact hR (Env.cons a xs) v

#print axioms eval_comprehension_iff
#print axioms comp_atomicity
#print axioms comp_actuality_at
#print axioms worldCore_spec
#print axioms full_profiles
#print axioms full_functions

end Classicism.Research.InfinitaryComprehension.Henkin
