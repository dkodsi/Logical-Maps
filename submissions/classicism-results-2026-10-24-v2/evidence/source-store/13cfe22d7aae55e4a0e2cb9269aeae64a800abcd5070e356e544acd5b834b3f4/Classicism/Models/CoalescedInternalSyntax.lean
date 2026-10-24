import Classicism.Models.ChoiceFirstOrderSmall

/-!
# Finite first-order membership syntax for internal hierarchies

Original formalization (misc), 23 October 2026. The type labels on variables
are only names for positions: every quantifier here ranges over the entire
membership universe. Parameters and ordered-pair terms are finite syntactic
data. No constructor accepts an arbitrary predicate or a semantic function.
The language contains an ordered-pair function. Separation is required for
this expanded finite first-order language, as in the source ZFC presentation.
It may alternatively be obtained by eliminating definable pair terms.
-/

namespace Classicism.Meta.CoalescedInternalHierarchy

open ChoiceFirstOrder

abbrev RawEnv (M : Type) (Γ : Ctx) := IEnv (fun _ => M) Γ

inductive RawTerm (M : Type) : Ctx → Type where
  | var {Γ σ} : Var Γ σ → RawTerm M Γ
  | param {Γ} : M → RawTerm M Γ
  | pair {Γ} : RawTerm M Γ → RawTerm M Γ → RawTerm M Γ

def RawTerm.eval {M : Type} (pair : M → M → M) :
    {Γ : Ctx} → RawTerm M Γ → RawEnv M Γ → M
  | _, .var v, g => g.get v
  | _, .param x, _ => x
  | _, .pair a b, g => pair (a.eval pair g) (b.eval pair g)

inductive RawFormula (M : Type) : Ctx → Type where
  | equal {Γ} : RawTerm M Γ → RawTerm M Γ → RawFormula M Γ
  | mem {Γ} : RawTerm M Γ → RawTerm M Γ → RawFormula M Γ
  | falsum {Γ} : RawFormula M Γ
  | neg {Γ} : RawFormula M Γ → RawFormula M Γ
  | conj {Γ} : RawFormula M Γ → RawFormula M Γ → RawFormula M Γ
  | disj {Γ} : RawFormula M Γ → RawFormula M Γ → RawFormula M Γ
  | all {Γ} (σ : Ty) : RawFormula M (σ :: Γ) → RawFormula M Γ
  | ex {Γ} (σ : Ty) : RawFormula M (σ :: Γ) → RawFormula M Γ

def RawFormula.Realize {M : Type} (mem : M → M → Prop) (pair : M → M → M) :
    {Γ : Ctx} → RawFormula M Γ → RawEnv M Γ → Prop
  | _, .equal a b, g => a.eval pair g = b.eval pair g
  | _, .mem a b, g => mem (a.eval pair g) (b.eval pair g)
  | _, .falsum, _ => False
  | _, .neg p, g => ¬ p.Realize mem pair g
  | _, .conj p q, g => p.Realize mem pair g ∧ q.Realize mem pair g
  | _, .disj p q, g => p.Realize mem pair g ∨ q.Realize mem pair g
  | _, .all _ p, g => ∀ x : M, p.Realize mem pair (.cons x g)
  | _, .ex _ p, g => ∃ x : M, p.Realize mem pair (.cons x g)

def RawFormula.imp {M Γ} (p q : RawFormula M Γ) : RawFormula M Γ :=
  .disj (.neg p) q

theorem RawFormula.realize_imp {M Γ} (mem : M → M → Prop) (pair : M → M → M)
    (p q : RawFormula M Γ) (g : RawEnv M Γ) :
    (p.imp q).Realize mem pair g ↔
      (p.Realize mem pair g → q.Realize mem pair g) := by
  classical
  change (¬ p.Realize mem pair g ∨ q.Realize mem pair g) ↔ _
  constructor
  · intro h hp
    exact h.elim (fun hn => False.elim (hn hp)) id
  · intro h
    by_cases hp : p.Realize mem pair g
    · exact Or.inr (h hp)
    · exact Or.inl hp

abbrev RawRen (Γ Δ : Ctx) := ∀ {σ}, Var Γ σ → Var Δ σ

def RawRen.lift {Γ Δ σ} (r : RawRen Γ Δ) : RawRen (σ :: Γ) (σ :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def RawTerm.rename {M Γ Δ} (r : RawRen Γ Δ) : RawTerm M Γ → RawTerm M Δ
  | .var v => .var (r v)
  | .param x => .param x
  | .pair a b => .pair (a.rename r) (b.rename r)

def RawFormula.rename {M Γ Δ} (r : RawRen Γ Δ) : RawFormula M Γ → RawFormula M Δ
  | .equal a b => .equal (a.rename r) (b.rename r)
  | .mem a b => .mem (a.rename r) (b.rename r)
  | .falsum => .falsum
  | .neg p => .neg (p.rename r)
  | .conj p q => .conj (p.rename r) (q.rename r)
  | .disj p q => .disj (p.rename r) (q.rename r)
  | .all σ p => .all σ (p.rename (RawRen.lift r))
  | .ex σ p => .ex σ (p.rename (RawRen.lift r))

theorem RawTerm.eval_rename {M Γ Δ} (pair : M → M → M) (r : RawRen Γ Δ)
    (g : RawEnv M Γ) (h : RawEnv M Δ)
    (hr : ∀ σ (v : Var Γ σ), h.get (r v) = g.get v) :
    ∀ t : RawTerm M Γ, (t.rename r).eval pair h = t.eval pair g
  | .var v => by
      simpa only [RawTerm.rename, RawTerm.eval] using hr _ v
  | .param _ => by
      simp only [RawTerm.rename, RawTerm.eval]
  | .pair a b => by
      simpa only [RawTerm.rename, RawTerm.eval] using
        congrArg₂ pair (eval_rename pair r g h hr a) (eval_rename pair r g h hr b)

theorem RawFormula.realize_rename {M : Type} (mem : M → M → Prop)
    (pair : M → M → M) : ∀ {Γ Δ} (p : RawFormula M Γ) (r : RawRen Γ Δ)
      (g : RawEnv M Γ) (h : RawEnv M Δ),
      (∀ σ (v : Var Γ σ), h.get (r v) = g.get v) →
      ((p.rename r).Realize mem pair h ↔ p.Realize mem pair g)
  | _, _, .equal a b, r, g, h, hr =>
    Iff.of_eq (congrArg₂ (fun x y => x = y)
      (RawTerm.eval_rename pair r g h hr a) (RawTerm.eval_rename pair r g h hr b))
  | _, _, .mem a b, r, g, h, hr =>
    Iff.of_eq (congrArg₂ mem
      (RawTerm.eval_rename pair r g h hr a) (RawTerm.eval_rename pair r g h hr b))
  | _, _, .falsum, _, _, _, _ => Iff.rfl
  | _, _, .neg p, r, g, h, hr => not_congr (realize_rename mem pair p r g h hr)
  | _, _, .conj p q, r, g, h, hr => and_congr
      (realize_rename mem pair p r g h hr) (realize_rename mem pair q r g h hr)
  | _, _, .disj p q, r, g, h, hr => or_congr
      (realize_rename mem pair p r g h hr) (realize_rename mem pair q r g h hr)
  | _, _, .all σ p, r, g, h, hr => by
    apply forall_congr'
    intro x
    apply realize_rename mem pair p (RawRen.lift r) (.cons x g) (.cons x h)
    intro τ v
    cases v with
    | zero => rfl
    | succ v => exact hr τ v
  | _, _, .ex σ p, r, g, h, hr => by
    apply exists_congr
    intro x
    apply realize_rename mem pair p (RawRen.lift r) (.cons x g) (.cons x h)
    intro τ v
    cases v with
    | zero => rfl
    | succ v => exact hr τ v

/-- Insert one fresh position after a fixed finite prefix. -/
def insertRen {Γ : Ctx} (κ : Ty) : (Δ : Ctx) → RawRen (Δ ++ Γ) (Δ ++ κ :: Γ)
  | [], _, v => .succ v
  | _ :: _, _, .zero => .zero
  | _ :: Δ, _, .succ v => .succ (insertRen κ Δ v)

theorem get_insertRen {M : Type} {Γ : Ctx} (κ : Ty) (x : M)
    (g : RawEnv M Γ) : ∀ {Δ} (a : RawEnv M Δ) σ (v : Var (Δ ++ Γ) σ),
    (appendEnv a (.cons x g)).get (insertRen κ Δ v) = (appendEnv a g).get v
  | [], .nil, _, _ => rfl
  | _ :: _, .cons _ _, _, .zero => rfl
  | _ :: _, .cons _ a, σ, .succ v => get_insertRen κ x g a σ v

end Classicism.Meta.CoalescedInternalHierarchy
