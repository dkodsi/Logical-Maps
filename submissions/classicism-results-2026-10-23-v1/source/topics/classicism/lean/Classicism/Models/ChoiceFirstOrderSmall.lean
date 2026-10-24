import Classicism.Models.ChoiceFirstOrderTerms

/-!
# Set-sized first-order sentence codes for the interpretation bridge

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/finite-choice-forcing-extraction-review.md` sections 2--4
(unpaginated). `SmallFormula Γ : Type` has only finite typed de Bruijn
contexts. Reification removes the general variable-family indexing used by
the convenient translator, with a proof that truth is unchanged.

This supplies concrete set-sized sentence codes. A countability encoding,
connection to a complete first-order proof calculus, and the forcing-to-
ground extraction theorem remain separate obligations.
-/

namespace Classicism.Meta.ChoiceFirstOrder

open CategoryTheory

def appendEnv {D : Ty → Type} : ∀ {Γ Δ : Ctx},
    IEnv D Γ → IEnv D Δ → IEnv D (Γ ++ Δ)
  | [], _, .nil, h => h
  | _ :: _, _, .cons x g, h => .cons x (appendEnv g h)

def leftVar {Δ : Ctx} : ∀ {Γ : Ctx} {σ : Ty}, Var Γ σ → Var (Γ ++ Δ) σ
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (leftVar v)

def rightVar : ∀ (Γ : Ctx) {Δ : Ctx} {σ : Ty}, Var Δ σ → Var (Γ ++ Δ) σ
  | [], _, _, v => v
  | _ :: Γ, _, _, v => .succ (rightVar Γ v)

theorem get_append_left {D : Ty → Type} : ∀ {Γ Δ : Ctx} {σ : Ty}
    (g : IEnv D Γ) (h : IEnv D Δ) (v : Var Γ σ),
    (appendEnv g h).get (leftVar v) = g.get v
  | _, _, _, .cons _ _, _, .zero => rfl
  | _, _, _, .cons _ g, h, .succ v => get_append_left g h v

theorem get_append_right {D : Ty → Type} : ∀ {Γ Δ : Ctx} {σ : Ty}
    (g : IEnv D Γ) (h : IEnv D Δ) (v : Var Δ σ),
    (appendEnv g h).get (rightVar Γ v) = h.get v
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons _ g, h, v => get_append_right g h v

/-- An ordinary small syntactic type, whose only variables are typed
positions in a finite context and whose only binders bind finite blocks. -/
inductive SmallFormula : Ctx → Type where
  | equal {Γ : Ctx} {σ : Ty} (x y : Var Γ σ) : SmallFormula Γ
  | rel {Γ : Ctx} (ρ : RTy) (x : Var Γ (.rel ρ))
      (a : Args (fun σ => Var Γ σ) ρ) : SmallFormula Γ
  | falsum {Γ : Ctx} : SmallFormula Γ
  | neg {Γ : Ctx} : SmallFormula Γ → SmallFormula Γ
  | conj {Γ : Ctx} : SmallFormula Γ → SmallFormula Γ → SmallFormula Γ
  | disj {Γ : Ctx} : SmallFormula Γ → SmallFormula Γ → SmallFormula Γ
  | all {Γ : Ctx} (ρ : RTy) : SmallFormula (ρ.args ++ Γ) → SmallFormula Γ
  | ex {Γ : Ctx} (ρ : RTy) : SmallFormula (ρ.args ++ Γ) → SmallFormula Γ

def SmallFormula.Realize (S : Structure) :
    {Γ : Ctx} → SmallFormula Γ → IEnv S.D Γ → Prop
  | _, .equal x y, g => g.get x = g.get y
  | _, .rel ρ x a, g => S.rel ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ a)
  | _, .falsum, _ => False
  | _, .neg p, g => ¬ p.Realize S g
  | _, .conj p q, g => p.Realize S g ∧ q.Realize S g
  | _, .disj p q, g => p.Realize S g ∨ q.Realize S g
  | _, .all ρ p, g => ∀ a : Args S.D ρ, p.Realize S (appendEnv (argsEnv ρ a) g)
  | _, .ex ρ p, g => ∃ a : Args S.D ρ, p.Realize S (appendEnv (argsEnv ρ a) g)

def bindVariables {V : Ty → Type} {Γ : Ctx}
    (r : ∀ σ, V σ → Var Γ σ) (ρ : RTy) :
    ∀ σ, Extend V ρ σ → Var (ρ.args ++ Γ) σ :=
  fun _ v => v.elim (fun x => rightVar ρ.args (r _ x)) leftVar

/-- Translate an explicit formula into finite-context syntax. The recursive
call is on the original subformula, not on an assumed semantic predicate. -/
def Formula.reify : {V : Ty → Type} → Formula V →
    ∀ (Γ : Ctx), (∀ σ, V σ → Var Γ σ) → SmallFormula Γ
  | _, .equal x y, _, r => .equal (r _ x) (r _ y)
  | _, .rel ρ x a, _, r => .rel ρ (r _ x) (mapArgs r ρ a)
  | _, .falsum, _, _ => .falsum
  | _, .neg p, Γ, r => .neg (p.reify Γ r)
  | _, .conj p q, Γ, r => .conj (p.reify Γ r) (q.reify Γ r)
  | _, .disj p q, Γ, r => .disj (p.reify Γ r) (q.reify Γ r)
  | _, .all ρ p, Γ, r => .all ρ (p.reify (ρ.args ++ Γ) (bindVariables r ρ))
  | _, .ex ρ p, Γ, r => .ex ρ (p.reify (ρ.args ++ Γ) (bindVariables r ρ))

theorem valuation_bindVariables {V D : Ty → Type} {Γ : Ctx}
    (r : ∀ σ, V σ → Var Γ σ) (g : IEnv D Γ) (ρ : RTy) (a : Args D ρ) :
    (fun σ v => (appendEnv (argsEnv ρ a) g).get (bindVariables r ρ σ v)) =
      extendEnv (fun σ v => g.get (r σ v)) ρ a := by
  funext σ v
  cases v with
  | inl v => exact get_append_right (argsEnv ρ a) g (r σ v)
  | inr v => exact get_append_left (argsEnv ρ a) g v

theorem Formula.reify_correct (S : Structure) :
    ∀ {V : Ty → Type} (φ : Formula V) (Γ : Ctx) (r : ∀ σ, V σ → Var Γ σ)
      (g : IEnv S.D Γ),
      (φ.reify Γ r).Realize S g ↔ φ.Realize S (fun σ v => g.get (r σ v))
  | _, .equal _ _, _, _, _ => Iff.rfl
  | _, .rel ρ x a, _, r, g => by
    change S.rel ρ (g.get (r _ x))
      (mapArgs (fun _ v => g.get v) ρ (mapArgs r ρ a)) ↔ _
    rw [mapArgs_comp]
    rfl
  | _, .falsum, _, _, _ => Iff.rfl
  | _, .neg p, Γ, r, g => not_congr (reify_correct S p Γ r g)
  | _, .conj p q, Γ, r, g => and_congr (reify_correct S p Γ r g) (reify_correct S q Γ r g)
  | _, .disj p q, Γ, r, g => or_congr (reify_correct S p Γ r g) (reify_correct S q Γ r g)
  | _, .all ρ p, Γ, r, g => by
    change (∀ a : Args S.D ρ, _) ↔ ∀ a : Args S.D ρ, _
    apply forall_congr'
    intro a
    rw [reify_correct, valuation_bindVariables]
  | _, .ex ρ p, Γ, r, g => by
    change (∃ a : Args S.D ρ, _) ↔ ∃ a : Args S.D ρ, _
    apply exists_congr
    intro a
    rw [reify_correct, valuation_bindVariables]

/-- A set-sized first-order sentence attached to each actual pure sentence. -/
def smallSentenceTranslation (p : Sentence Signature.pure) : SmallFormula [] :=
  (sentenceTranslation p).reify [] (fun _ v => nomatch v)

theorem smallSentenceTranslation_correct (S : Structure) (p : Sentence Signature.pure) :
    (smallSentenceTranslation p).Realize S .nil ↔ S.model.HoldsSentence p := by
  rw [smallSentenceTranslation, Formula.reify_correct]
  have hη :
      (fun σ (v : NoVars σ) =>
        (IEnv.nil : IEnv S.D []).get (show Var [] σ from nomatch v)) =
      (fun σ (v : NoVars σ) => (show S.D σ from nomatch v)) := by
    funext σ v
    exact Empty.elim v
  exact (Iff.of_eq (congrArg ((sentenceTranslation p).Realize S) hη)).trans
    (sentenceTranslation_correct S p)

/-- The comprehension scheme indexed exclusively by small formula codes and
finite parameter contexts. Each instance is its ordinary first-order
universal closure followed by one existentially bound relational value. -/
def SmallComprehension (S : Structure) : Prop :=
  ∀ (Γ : Ctx) (ρ : RTy) (φ : SmallFormula (ρ.args ++ Γ)) (g : IEnv S.D Γ),
    ∃ X : S.D (.rel ρ), ∀ a : Args S.D ρ,
      S.rel ρ X a ↔ φ.Realize S (appendEnv (argsEnv ρ a) g)

/-- Relational term admission from the finite-context comprehension scheme. -/
private theorem relational_sem_mem_small (S : Structure) (hC : SmallComprehension S)
    {Γ : Ctx} {ρ : RTy} (t : Term Signature.pure Γ (.rel ρ)) (g : IEnv S.D Γ) :
    S.model.sem (𝟙 World.star) t g ∈ Set.range (S.model.Incl (.rel ρ) World.star) := by
  let V : Ty → Type := fun τ => Var Γ τ
  let φ : Formula (Extend V ρ) :=
    translate t (Extend V ρ) (fun _ v => Sum.inl v) (boundArgs V ρ)
  obtain ⟨X, hX⟩ := hC Γ ρ
    (φ.reify (ρ.args ++ Γ) (bindVariables (fun _ v => v) ρ)) g
  refine ⟨X, intension_ext S (fun a => ?_)⟩
  have hr := Formula.reify_correct S φ (ρ.args ++ Γ)
    (bindVariables (fun _ v => v) ρ) (appendEnv (argsEnv ρ a) g)
  have hη := congrArg (φ.Realize S)
    (valuation_bindVariables (V := V) (D := S.D) (fun _ v => v) g ρ a)
  have ht := translate_correct S t (Extend V ρ) (fun _ v => Sum.inl v)
    (extendEnv (fun _ v => g.get v) ρ a) g (fun _ _ => rfl) (boundArgs V ρ)
  change _ ↔ observe S (.rel ρ) _
    (mapArgs (extendEnv (fun _ v => g.get v) ρ a) ρ (boundArgs V ρ)) at ht
  rw [eval_boundArgs] at ht
  exact (hX a).trans (hr.trans ((Iff.of_eq hη).trans ht))

/-- Actual model closure needs only the small first-order scheme. The
larger convenient variable-family presentation is not a premise here. -/
theorem isModel_of_small_comprehension (S : Structure) (hC : SmallComprehension S) :
    S.model.IsModel := by
  intro Γ σ W h t g
  cases W
  cases h
  cases t with
  | var v => exact ⟨g.get v, rfl⟩
  | const c => exact Empty.elim (show Empty from c)
  | app f a => exact relational_sem_mem_small S hC (.app f a) g
  | lam b => exact relational_sem_mem_small S hC (.lam b) g
  | and => exact relational_sem_mem_small S hC .and g
  | or => exact relational_sem_mem_small S hC .or g
  | not => exact relational_sem_mem_small S hC .not g
  | all τ => exact relational_sem_mem_small S hC (.all τ) g
  | ex τ => exact relational_sem_mem_small S hC (.ex τ) g
  | eq τ => exact relational_sem_mem_small S hC (.eq τ) g
  | constR ρ => exact relational_sem_mem_small S hC (.constR ρ) g
  | negR ρ => exact relational_sem_mem_small S hC (.negR ρ) g
  | andR ρ => exact relational_sem_mem_small S hC (.andR ρ) g
  | orR ρ => exact relational_sem_mem_small S hC (.orR ρ) g
  | coextR ρ => exact relational_sem_mem_small S hC (.coextR ρ) g
  | boxR ρ => exact relational_sem_mem_small S hC (.boxR ρ) g
  | inclR ρ => exact relational_sem_mem_small S hC (.inclR ρ) g

theorem small_c_theorem_holds (S : Structure) (hC : SmallComprehension S)
    {p : Sentence Signature.pure} (hp : C.Theorem p) : S.model.HoldsSentence p :=
  S.model.theorem_holds (isModel_of_small_comprehension S hC) hp

end Classicism.Meta.ChoiceFirstOrder
