import Classicism.Results.Research.InfinitaryComprehensionSyntax

/-!
# Full-standard semantics of the concrete infinitary language

Ordinary Lean metatheory (including extensionality and classical reasoning),
not a shallow C derivation. The original closed relational types are read
over individuals E and worlds W; propositions are W-indexed truth values and
every allowed arrow is a full function space. For the auxiliary `Ty.var`
codes we use E, exactly as the existing standard denotation does. All claims
therefore apply in particular to every original `Closed` type.

The principal theorem proves truth of the actual syntax
`Term.comprehension A` under every assignment to its arbitrary parameter
family. Its witness is obtained by finite currying of the interpreted
matrix. There is no semantic comprehension assumption or admitted-witness
field in the model definition.
-/

namespace Classicism.Research.InfinitaryComprehension

open Classicism.Meta

universe u v

mutual
  def FullTy (E W : Type v) : Ty → Type v
    | .e => E
    | .rel ρ => FullRel E W ρ
    | .var _ => E
  def FullRel (E W : Type v) : RTy → Type v
    | .t => W → Prop
    | .arr σ ρ => FullTy E W σ → FullRel E W ρ
end

attribute [reducible] FullTy FullRel

abbrev Env (E W : Type v) (Γ : Ctx) := ∀ {σ}, Var Γ σ → FullTy E W σ

namespace Env

variable {E W : Type v}

def nil : Env E W [] := fun v => nomatch v

def cons {Γ σ} (x : FullTy E W σ) (env : Env E W Γ) : Env E W (σ :: Γ)
  | _, .zero => x
  | _, .succ v => env v

def tail {Γ σ} (env : Env E W (σ :: Γ)) : Env E W Γ :=
  fun v => env (.succ v)

theorem nil_eta (env : Env E W []) : @Eq (Env E W []) env nil := by
  funext σ v
  cases v

theorem cons_eta {Γ σ} (env : Env E W (σ :: Γ)) :
    @Eq (Env E W (σ :: Γ)) (cons (env .zero) (tail env)) env := by
  funext τ v
  cases v <;> rfl

def append {Δ : Ctx} : {Γ : Ctx} → Env E W Γ → Env E W Δ → Env E W (Γ ++ Δ)
  | [], _, env => env
  | _ :: _, xs, env => cons (xs .zero) (append (tail xs) env)

theorem append_embed {Γ Δ} (xs : Env E W Γ) (env : Env E W Δ)
    {σ} (v : Var Γ σ) : append xs env (Ren.embed Γ Δ v) = xs v := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih (tail xs)

theorem append_last (Γ : Ctx) (xs : Env E W Γ) {σ}
    (x : FullTy E W σ) : append xs (cons x nil) (lastVar Γ σ) = x := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih => exact ih (tail xs)

end Env

abbrev Assignment (Param : Ty → Type u) (E W : Type v) :=
  ∀ {σ}, Param σ → FullTy E W σ

namespace Term

variable {Param : Ty → Type u} {E W : Type v}

def eval (η : Assignment Param E W) :
    {Γ : Ctx} → {σ : Ty} → Term Param Γ σ → Env E W Γ → FullTy E W σ
  | _, _, .var v, env => env v
  | _, _, .param p, _ => η p
  | _, _, .app f a, env => (eval η f env) (eval η a env)
  | _, _, .top, _ => fun _ => True
  | _, _, .bot, _ => fun _ => False
  | _, _, .neg p, env => fun w => ¬ eval η p env w
  | _, _, .conj p q, env => fun w => eval η p env w ∧ eval η q env w
  | _, _, .disj p q, env => fun w => eval η p env w ∨ eval η q env w
  | _, _, .imp p q, env => fun w => eval η p env w → eval η q env w
  | _, _, .iff p q, env => fun w => eval η p env w ↔ eval η q env w
  | _, _, .eq a b, env => fun _ => eval η a env = eval η b env
  | _, _, .boxOp, _ => fun p _ => ∀ w, p w
  | _, _, .all p, env => fun w => ∀ x, eval η p (Env.cons x env) w
  | _, _, .ex p, env => fun w => ∃ x, eval η p (Env.cons x env) w
  | _, _, .iAnd I p, env => fun w => ∀ i : I, eval η (p i) env w
  | _, _, .iOr I p, env => fun w => ∃ i : I, eval η (p i) env w

theorem eval_rename (η : Assignment Param E W) :
    ∀ {Γ σ} (a : Term Param Γ σ) {Δ} (r : Ren Γ Δ)
      (env : Env E W Γ) (env' : Env E W Δ),
      (∀ {τ} (x : Var Γ τ), env' (r x) = env x) →
      eval η (a.rename r) env' = eval η a env := by
  intro Γ σ a
  induction a with
  | var x => intro Δ r env env' h; exact h x
  | param p => intros; rfl
  | app f a ihf iha =>
      intro Δ r env env' h
      simp only [rename, eval, ihf r env env' h, iha r env env' h]
  | top => intros; rfl
  | bot => intros; rfl
  | neg p ih =>
      intro Δ r env env' h
      simp only [rename, eval, ih r env env' h]
  | conj p q ihp ihq =>
      intro Δ r env env' h
      simp only [rename, eval, ihp r env env' h, ihq r env env' h]
  | disj p q ihp ihq =>
      intro Δ r env env' h
      simp only [rename, eval, ihp r env env' h, ihq r env env' h]
  | imp p q ihp ihq =>
      intro Δ r env env' h
      simp only [rename, eval, ihp r env env' h, ihq r env env' h]
  | iff p q ihp ihq =>
      intro Δ r env env' h
      simp only [rename, eval, ihp r env env' h, ihq r env env' h]
  | eq a b iha ihb =>
      intro Δ r env env' h
      simp only [rename, eval, iha r env env' h, ihb r env env' h]
  | boxOp => intros; rfl
  | all p ih =>
      intro Δ r env env' h
      have hx (x) : eval η (p.rename (Ren.lift r)) (Env.cons x env') =
          eval η p (Env.cons x env) := by
        apply ih
        intro τ y
        cases y with
        | zero => rfl
        | succ y => exact h y
      exact congrArg (fun f => fun w => ∀ x, f x w) (funext hx)
  | ex p ih =>
      intro Δ r env env' h
      have hx (x) : eval η (p.rename (Ren.lift r)) (Env.cons x env') =
          eval η p (Env.cons x env) := by
        apply ih
        intro τ y
        cases y with
        | zero => rfl
        | succ y => exact h y
      exact congrArg (fun f => fun w => ∃ x, f x w) (funext hx)
  | iAnd I p ih =>
      intro Δ r env env' h
      exact congrArg (fun f => fun w => ∀ i : I, f i w)
        (funext (fun i => ih i r env env' h))
  | iOr I p ih =>
      intro Δ r env env' h
      exact congrArg (fun f => fun w => ∃ i : I, f i w)
        (funext (fun i => ih i r env env' h))

end Term

/-- Ordinary finite currying into the existing relational type. -/
def curry (E W : Type v) : (Γ : Ctx) →
    (Env E W Γ → W → Prop) → FullRel E W (RTy.ofArgs Γ)
  | [], f => f Env.nil
  | _ :: Γ, f => fun x => curry E W Γ (fun xs => f (Env.cons x xs))

/-- Evaluate a curried relation on its finite argument environment. -/
def uncurry (E W : Type v) : (Γ : Ctx) →
    FullRel E W (RTy.ofArgs Γ) → Env E W Γ → W → Prop
  | [], f, _ => f
  | _ :: Γ, f, xs => uncurry E W Γ (f (xs .zero)) (Env.tail xs)

theorem uncurry_curry (E W : Type v) (Γ : Ctx)
    (f : Env E W Γ → W → Prop) (xs : Env E W Γ) :
    uncurry E W Γ (curry E W Γ f) xs = f xs := by
  induction Γ with
  | nil => exact congrArg f (Env.nil_eta xs).symm
  | cons σ Γ ih =>
      change uncurry E W Γ (curry E W Γ (fun ys => f (Env.cons (xs .zero) ys)))
        (Env.tail xs) = f xs
      rw [ih]
      exact congrArg f (Env.cons_eta xs)

/-- Full-standard relational entities are determined by their entire
world--argument profile. This is semantic Intensionality, not actual
coextension at just one designated world. -/
theorem full_intensionality (E W : Type v) (Γ : Ctx)
    (R S : FullRel E W (RTy.ofArgs Γ))
    (h : ∀ (xs : Env E W Γ) (w : W),
      uncurry E W Γ R xs w ↔ uncurry E W Γ S xs w) : R = S := by
  induction Γ with
  | nil =>
      funext w
      exact propext (h Env.nil w)
  | cons σ Γ ih =>
      funext x
      apply ih
      intro xs w
      exact h (Env.cons x xs) w

namespace Term

variable {Param : Ty → Type u} {E W : Type v}

theorem eval_applyVars (η : Assignment Param E W) (Γ : Ctx) :
    ∀ {Δ} (f : Term Param Δ (RTy.ofArgs Γ))
      (xs : ∀ {σ}, Var Γ σ → Term Param Δ σ) (env : Env E W Δ),
      eval η (applyVars Γ f xs) env =
        uncurry E W Γ (eval η f env) (fun v => eval η (xs v) env) := by
  induction Γ with
  | nil => intros; rfl
  | cons σ Γ ih =>
      intro Δ f xs env
      exact ih (.app f (xs .zero)) (fun v => xs (.succ v)) env

theorem eval_compBody (η : Assignment Param E W) {Γ : Ctx}
    (A : Formula Param Γ) (R : FullRel E W (RTy.ofArgs Γ))
    (xs : Env E W Γ) :
    eval η A.compBody (Env.append xs (Env.cons (σ := Ty.rel (RTy.ofArgs Γ)) R Env.nil)) =
      fun w => (uncurry E W Γ R xs w ↔ eval η A xs w) := by
  unfold compBody
  change (fun w => eval η (applyVars Γ (.var (lastVar Γ _))
      (fun v => .var (Ren.embed Γ _ v))) (Env.append xs (Env.cons (σ := Ty.rel (RTy.ofArgs Γ)) R Env.nil)) w ↔
      eval η (A.rename (Ren.embed Γ _)) (Env.append xs (Env.cons (σ := Ty.rel (RTy.ofArgs Γ)) R Env.nil)) w) = _
  rw [eval_applyVars]
  have hvars : @Eq (Env E W Γ) (fun {σ} (v : Var Γ σ) =>
      eval η (.var (Ren.embed Γ _ v)) (Env.append xs (Env.cons (σ := Ty.rel (RTy.ofArgs Γ)) R Env.nil))) xs := by
    funext σ v
    exact Env.append_embed xs (Env.cons (σ := Ty.rel (RTy.ofArgs Γ)) R Env.nil) v
  have hA := eval_rename η A (Ren.embed Γ _) xs
    (Env.append xs (Env.cons (σ := Ty.rel (RTy.ofArgs Γ)) R Env.nil))
    (fun v => Env.append_embed xs (Env.cons (σ := Ty.rel (RTy.ofArgs Γ)) R Env.nil) v)
  have hR : eval η (.var (lastVar Γ _)) (Env.append xs (Env.cons (σ := Ty.rel (RTy.ofArgs Γ)) R Env.nil)) = R :=
    Env.append_last Γ xs (σ := Ty.rel (RTy.ofArgs Γ)) R
  rw [hvars, hA, hR]

theorem eval_closeAll (η : Assignment Param E W) (Γ : Ctx) :
    ∀ {Δ} (A : Formula Param (Γ ++ Δ)) (env : Env E W Δ) (w : W),
      eval η (closeAll Γ A) env w ↔
        ∀ xs : Env E W Γ, eval η A (Env.append xs env) w := by
  induction Γ with
  | nil => intro Δ A env w; exact ⟨fun h _ => h, fun h => h Env.nil⟩
  | cons σ Γ ih =>
      intro Δ A env w
      change eval η (closeAll Γ (.all A)) env w ↔ _
      rw [ih]
      constructor
      · intro h xs
        exact h (Env.tail xs) (xs .zero)
      · intro h xs x
        exact h (Env.cons x xs)

/-- Every actual object-language infinitary Comprehension instance is true
in every full standard hierarchy, for every simultaneous parameter assignment. -/
theorem full_comprehension (η : Assignment Param E W) {Γ : Ctx}
    (A : Formula Param Γ) (w : W) :
    eval η A.comprehension Env.nil w := by
  change ∃ R : FullRel E W (RTy.ofArgs Γ),
    ∀ v : W, eval η (closeAll Γ A.compBody) (Env.cons R Env.nil) v
  refine ⟨curry E W Γ (fun xs => eval η A xs), ?_⟩
  intro v
  apply (eval_closeAll η Γ A.compBody _ v).2
  intro xs
  rw [eval_compBody, uncurry_curry]

/-- The witness represents the whole intension, not just current truth. -/
theorem full_comprehension_profile (η : Assignment Param E W) {Γ : Ctx}
    (A : Formula Param Γ) :
    ∃ R : FullRel E W (RTy.ofArgs Γ),
      ∀ (xs : Env E W Γ) (w : W),
        uncurry E W Γ R xs w ↔ eval η A xs w := by
  refine ⟨curry E W Γ (fun xs => eval η A xs), ?_⟩
  intro xs w
  rw [uncurry_curry]

/-- The original first-class modal operator commutes with arbitrary meets. -/
theorem eval_box_iAnd (η : Assignment Param E W) {Γ : Ctx}
    (I : Type u) (p : I → Formula Param Γ) (env : Env E W Γ) (w : W) :
    eval η (.box (.iAnd I p)) env w ↔
      eval η (.iAnd I (fun i => .box (p i))) env w := by
  change (∀ v : W, ∀ i : I, eval η (p i) env v) ↔
    (∀ i : I, ∀ v : W, eval η (p i) env v)
  exact ⟨fun h i v => h v i, fun h v i => h i v⟩

/-- The concrete complete-truth-pattern formula. -/
def truthPattern {Γ : Ctx} (I : Type u) (p : I → Formula Param Γ) : Formula Param Γ :=
  .iOr (I → Bool) (fun ε => .iAnd I (fun i => if ε i then p i else .neg (p i)))

theorem eval_truthPattern (η : Assignment Param E W) {Γ : Ctx}
    (I : Type u) (p : I → Formula Param Γ) (env : Env E W Γ) (w : W) :
    eval η (truthPattern I p) env w := by
  classical
  change ∃ ε : I → Bool, ∀ i : I,
    eval η (if ε i then p i else .neg (p i)) env w
  refine ⟨fun i => decide (eval η (p i) env w), ?_⟩
  intro i
  by_cases h : eval η (p i) env w
  · simp [h]
  · simp [h, eval]

/-- The ordinary universally quantified ND instance as concrete syntax. -/
def distinctness (σ : Ty) : Formula Param [] :=
  .all (σ := σ) (.all (σ := σ)
    (.imp
      (.neg (.eq (.var (Var.succ Var.zero)) (.var Var.zero)))
      (.box (.neg (.eq (.var (Var.succ Var.zero)) (.var Var.zero))))))

/-- C5 is boxed ND, not merely its unboxed instance. -/
def c5 (σ : Ty) : Formula Param [] := .box (distinctness σ)

theorem full_c5 (η : Assignment Param E W) (σ : Ty) (w : W) :
    eval η (c5 (Param := Param) σ) Env.nil w := by
  change ∀ v : W, ∀ x y : FullTy E W σ, x ≠ y → ∀ z : W, x ≠ y
  intro v x y h z
  exact h

theorem full_modal_K (η : Assignment Param E W) {Γ : Ctx}
    (p q : Formula Param Γ) (env : Env E W Γ) (w : W) :
    eval η (.imp (.box (.imp p q)) (.imp (.box p) (.box q))) env w := by
  change (∀ v : W, eval η p env v → eval η q env v) →
    (∀ v : W, eval η p env v) → ∀ v : W, eval η q env v
  exact fun hpq hp v => hpq v (hp v)

/-- The primitive b has the original equality-to-top interpretation. -/
theorem full_box_eq_top (p : W → Prop) :
    (∀ w, p w) ↔ p = (fun _ => True) := by
  constructor
  · intro h
    funext w
    exact propext ⟨fun _ => trivial, fun _ => h w⟩
  · intro h w
    rw [h]
    trivial

end Term

end Classicism.Research.InfinitaryComprehension

/- The eventual dispatcher log records exact kernel axiom dependencies.
These metatheorems may use Lean's ordinary mathematical extensionality and
classical axioms. `sorryAx` or any newly introduced axiom is not permitted. -/
#print axioms Classicism.Research.InfinitaryComprehension.uncurry_curry
#print axioms Classicism.Research.InfinitaryComprehension.full_intensionality
#print axioms Classicism.Research.InfinitaryComprehension.Term.full_comprehension
#print axioms Classicism.Research.InfinitaryComprehension.Term.full_comprehension_profile
#print axioms Classicism.Research.InfinitaryComprehension.Term.eval_box_iAnd
#print axioms Classicism.Research.InfinitaryComprehension.Term.eval_truthPattern
#print axioms Classicism.Research.InfinitaryComprehension.Term.full_c5
#print axioms Classicism.Research.InfinitaryComprehension.Term.full_modal_K
#print axioms Classicism.Research.InfinitaryComprehension.Term.full_box_eq_top
