import Classicism.Models.ChoiceFirstOrder

/-!
# First-order value formulas for the actual Classicism syntax

Original formalization (misc), 23 October 2026, of the E₂ interpretation
lemma in `research/2026-10-23/finite-choice-forcing-extraction-review.md`,
section 2 (unpaginated). The translation below consumes the project's real
`Term Signature.pure`, including every type-subscripted logical constant.
Its correctness uses the existing intensional `Premodel.sem`.

Comprehension is only the first-order schema on explicit finite syntax from
`ChoiceFirstOrder`; the conclusion `isModel` proves actual term closure.
Neither forcing, existence of a symmetric ZF model, nor any Choice failure
is supplied by this interpretation theorem.
-/

namespace Classicism.Meta.ChoiceFirstOrder

open CategoryTheory

abbrev Observation (V : Ty → Type) : Ty → Type
  | .e => V .e
  | .rel ρ => Args V ρ
  | .var n => V (.var n)

def mapObservation {V D : Ty → Type} (η : ∀ σ, V σ → D σ) :
    ∀ σ, Observation V σ → Observation D σ
  | .e, y => η _ y
  | .rel ρ, a => mapArgs η ρ a
  | .var _, y => η _ y

def observe (S : Structure) : ∀ σ,
    Intensional.Outer (inner S.D) σ World.star → Observation S.D σ → Prop
  | .e, x, y => y = x
  | .rel ρ, X, a =>
    (⟨World.star, a, 𝟙 World.star⟩ : Intensional.Tuple (inner S.D) ρ World.star) ∈ X
  | .var _, x, y => y = x

abbrev Code (Γ : Ctx) (σ : Ty) :=
  ∀ (V : Ty → Type), (∀ τ, Var Γ τ → V τ) → Observation V σ → Formula V

def variableFormula {V : Ty → Type} :
    ∀ σ, V σ → Observation V σ → Formula V
  | .e, x, y => .equal y x
  | .rel ρ, X, a => .rel ρ X a
  | .var _, x, y => .equal y x

/-- Equality to a denotation is a first-order formula. For a relational
output it universally compares the finite argument tuple. -/
def valueCode {Γ : Ctx} : ∀ {σ : Ty}, Code Γ σ →
    ∀ (V : Ty → Type), (∀ τ, Var Γ τ → V τ) → V σ → Formula V
  | .e, c, V, r, y => c V r y
  | .var _, c, V, r, y => c V r y
  | .rel ρ, c, V, r, y =>
    .all ρ ((Formula.rel ρ (Sum.inl y) (boundArgs V ρ)).iff
      (c (Extend V ρ) (fun τ v => Sum.inl (r τ v)) (boundArgs V ρ)))

abbrev newest {V : Ty → Type} (σ : Ty) : Extend V (.arr σ .t) σ :=
  Sum.inr Var.zero

/-- Pointwise formula of an actual pure Classicism term. Application uses
an existentially bound value, whose equality to the argument denotation is
itself a first-order formula; no global semantic evaluation symbol occurs. -/
def translate : ∀ {Γ : Ctx} {σ : Ty}, Term Signature.pure Γ σ → Code Γ σ
  | _, σ, .var v, V, r, a => variableFormula σ (r σ v) a
  | _, _, .const c, _, _, _ => nomatch c
  | _, _, .app (σ := σ) f a, V, r, b =>
    .ex (.arr σ .t)
      (.conj
        (valueCode (translate a) (Extend V (.arr σ .t))
          (fun τ v => Sum.inl (r τ v)) (newest σ))
        (translate f (Extend V (.arr σ .t))
          (fun τ v => Sum.inl (r τ v))
          (newest σ, mapArgs (liftVars (.arr σ .t)) _ b)))
  | _, _, .lam b, V, r, a =>
    translate b V (fun _ v => match v with
      | .zero => a.1
      | .succ v => r _ v) a.2
  | _, _, .and, _, _, a =>
    .conj (.rel .t a.1 PUnit.unit) (.rel .t a.2.1 PUnit.unit)
  | _, _, .or, _, _, a =>
    .disj (.rel .t a.1 PUnit.unit) (.rel .t a.2.1 PUnit.unit)
  | _, _, .not, _, _, a => .neg (.rel .t a.1 PUnit.unit)
  | _, _, .all σ, V, _, a =>
    .all (.arr σ .t) (.rel (.arr σ .t) (Sum.inl a.1) (boundArgs V (.arr σ .t)))
  | _, _, .ex σ, V, _, a =>
    .ex (.arr σ .t) (.rel (.arr σ .t) (Sum.inl a.1) (boundArgs V (.arr σ .t)))
  | _, _, .eq _, _, _, a => .equal a.1 a.2.1
  | _, _, .constR _, _, _, a => .rel .t a.1 PUnit.unit
  | _, _, .negR ρ, _, _, a => .neg (.rel ρ a.1 a.2)
  | _, _, .andR ρ, _, _, a => .conj (.rel ρ a.1 a.2.2) (.rel ρ a.2.1 a.2.2)
  | _, _, .orR ρ, _, _, a => .disj (.rel ρ a.1 a.2.2) (.rel ρ a.2.1 a.2.2)
  | _, _, .coextR ρ, V, _, a =>
    .all ρ ((Formula.rel ρ (Sum.inl a.1) (boundArgs V ρ)).iff
      (.rel ρ (Sum.inl a.2.1) (boundArgs V ρ)))
  | _, _, .boxR ρ, _, _, a => .rel ρ a.1 a.2
  | _, _, .inclR ρ, V, _, a =>
    .all ρ ((Formula.rel ρ (Sum.inl a.1) (boundArgs V ρ)).imp
      (.rel ρ (Sum.inl a.2.1) (boundArgs V ρ)))

def CodeCorrect (S : Structure) {Γ : Ctx} {σ : Ty}
    (t : Term Signature.pure Γ σ) (c : Code Γ σ) : Prop :=
  ∀ (V : Ty → Type) (r : ∀ τ, Var Γ τ → V τ) (η : ∀ τ, V τ → S.D τ)
    (g : IEnv S.D Γ),
    (∀ τ v, η τ (r τ v) = g.get v) →
    ∀ a : Observation V σ,
      (c V r a).Realize S η ↔
        observe S σ (S.model.sem (𝟙 World.star) t g) (mapObservation η σ a)

theorem valueCode_correct (S : Structure) {Γ : Ctx} {σ : Ty}
    (t : Term Signature.pure Γ σ) (c : Code Γ σ) (hc : CodeCorrect S t c)
    (V : Ty → Type) (r : ∀ τ, Var Γ τ → V τ) (η : ∀ τ, V τ → S.D τ)
    (g : IEnv S.D Γ) (hg : ∀ τ v, η τ (r τ v) = g.get v) (y : V σ) :
    (valueCode c V r y).Realize S η ↔
      S.model.Incl σ World.star (η σ y) = S.model.sem (𝟙 World.star) t g := by
  cases σ with
  | e => exact hc V r η g hg y
  | var n => exact hc V r η g hg y
  | rel ρ =>
    change (∀ a : Args S.D ρ, _ ) ↔ _
    have hl (a : Args S.D ρ) :
        (c (Extend V ρ) (fun τ v => Sum.inl (r τ v)) (boundArgs V ρ)).Realize S
          (extendEnv η ρ a) ↔
        observe S (.rel ρ) (S.model.sem (𝟙 World.star) t g) a := by
      have h := hc (Extend V ρ) (fun τ v => Sum.inl (r τ v))
        (extendEnv η ρ a) g hg (boundArgs V ρ)
      change _ ↔ observe S (.rel ρ) _ (mapArgs (extendEnv η ρ a) ρ (boundArgs V ρ)) at h
      rwa [eval_boundArgs] at h
    constructor
    · intro h
      apply intension_ext S
      intro a
      have ha := (Formula.realize_iff S _ _ (extendEnv η ρ a)).mp (h a)
      change S.rel ρ (η _ y) (mapArgs (extendEnv η ρ a) ρ (boundArgs V ρ)) ↔ _ at ha
      rw [eval_boundArgs] at ha
      exact ha.trans (hl a)
    · intro h a
      apply (Formula.realize_iff S _ _ (extendEnv η ρ a)).mpr
      change S.rel ρ (η _ y) (mapArgs (extendEnv η ρ a) ρ (boundArgs V ρ)) ↔ _
      rw [eval_boundArgs, hl a]
      change _ ↔ (⟨World.star, a, 𝟙 World.star⟩ :
        Intensional.Tuple (inner S.D) ρ World.star) ∈ S.model.sem _ t g
      rw [← h]
      rfl

/-- The translator agrees with the existing semantics, before any
comprehension or `IsModel` assumption is imposed. -/
theorem translate_correct (S : Structure) :
    ∀ {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ),
      CodeCorrect S t (translate t)
  | _, σ, .var v => by
    intro V r η g hg a
    cases σ with
    | e => exact iff_of_eq (congrArg (fun x => η _ a = x) (hg _ v))
    | var n => exact iff_of_eq (congrArg (fun x => η _ a = x) (hg _ v))
    | rel ρ =>
      change S.rel ρ (η _ (r _ v)) (mapArgs η ρ a) ↔ S.rel ρ (g.get v) (mapArgs η ρ a)
      rw [hg]
  | _, _, .const c => nomatch c
  | _, _, .app (σ := σ) (ρ := ρ) f a => by
    intro V r η g hg b
    let r' : ∀ τ, Var _ τ → Extend V (.arr σ .t) τ := fun τ v => Sum.inl (r τ v)
    have hv (x : S.D σ) := valueCode_correct S a (translate a) (translate_correct S a)
      (Extend V (.arr σ .t)) r' (extendEnv η (.arr σ .t) (x, PUnit.unit)) g hg (newest σ)
    have hf (x : S.D σ) :
        (translate f (Extend V (.arr σ .t)) r'
          (newest σ, mapArgs (liftVars (.arr σ .t)) ρ b)).Realize S
          (extendEnv η (.arr σ .t) (x, PUnit.unit)) ↔
        (⟨World.star, (x, mapArgs η ρ b), 𝟙 World.star⟩ :
          Intensional.Tuple (inner S.D) (.arr σ ρ) World.star) ∈
          S.model.sem (𝟙 World.star) f g := by
      have h := translate_correct S f (Extend V (.arr σ .t)) r'
        (extendEnv η (.arr σ .t) (x, PUnit.unit)) g hg
        (newest σ, mapArgs (liftVars (.arr σ .t)) ρ b)
      change _ ↔ (⟨World.star,
        (x, mapArgs (extendEnv η (.arr σ .t) (x, PUnit.unit)) ρ
          (mapArgs (liftVars (.arr σ .t)) ρ b)), 𝟙 World.star⟩ :
        Intensional.Tuple (inner S.D) (.arr σ ρ) World.star) ∈ _ at h
      rwa [eval_liftArgs] at h
    change (∃ z : Args S.D (.arr σ .t), _ ∧ _) ↔
      ∃ x : S.D σ,
        S.model.Incl σ World.star x =
          Intensional.Outer.map (inner S.D) σ (𝟙 World.star) (S.model.sem _ a g) ∧ _
    have hm := Intensional.Outer.map_id (inner S.D) σ World.star
      (S.model.sem (𝟙 World.star) a g)
    constructor
    · rintro ⟨⟨x, u⟩, ha, hb⟩
      cases u
      exact ⟨x, ((hv x).mp ha).trans hm.symm, (hf x).mp hb⟩
    · rintro ⟨x, ha, hb⟩
      exact ⟨(x, PUnit.unit), (hv x).mpr (ha.trans hm), (hf x).mpr hb⟩
  | _, _, .lam (σ := σ) (ρ := ρ) b => by
    intro V r η g hg a
    have h := translate_correct S b V
      (fun _ v => match v with | .zero => a.1 | .succ v => r _ v)
      η (.cons (η σ a.1) g)
      (fun τ v => by cases v with | zero => rfl | succ v => exact hg τ v) a.2
    change _ ↔ (⟨World.star, mapArgs η ρ a.2, 𝟙 World.star⟩ :
      Intensional.Tuple (inner S.D) ρ World.star) ∈
        S.model.sem _ b (.cons (η σ a.1) (S.model.push (𝟙 World.star) g))
    rw [push_eq]
    exact h
  | _, _, .and => by intro V r η g hg a; rfl
  | _, _, .or => by intro V r η g hg a; rfl
  | _, _, .not => by intro V r η g hg a; rfl
  | _, _, .all σ => by
    intro V r η g hg a
    change (∀ b : Args S.D (.arr σ .t),
      S.rel (.arr σ .t) (η _ a.1)
        (mapArgs (extendEnv η (.arr σ .t) b) _ (boundArgs V (.arr σ .t)))) ↔
      ∀ x : S.D σ, S.rel (.arr σ .t) (η _ a.1) (x, PUnit.unit)
    simp only [eval_boundArgs]
    exact ⟨fun h x => h (x, PUnit.unit), fun h ⟨x, u⟩ => by cases u; exact h x⟩
  | _, _, .ex σ => by
    intro V r η g hg a
    change (∃ b : Args S.D (.arr σ .t),
      S.rel (.arr σ .t) (η _ a.1)
        (mapArgs (extendEnv η (.arr σ .t) b) _ (boundArgs V (.arr σ .t)))) ↔
      ∃ x : S.D σ, S.rel (.arr σ .t) (η _ a.1) (x, PUnit.unit)
    simp only [eval_boundArgs]
    constructor
    · rintro ⟨⟨x, u⟩, h⟩; cases u; exact ⟨x, h⟩
    · rintro ⟨x, h⟩; exact ⟨(x, PUnit.unit), h⟩
  | _, _, .eq _ => by intro V r η g hg a; rfl
  | _, _, .constR _ => by intro V r η g hg a; rfl
  | _, _, .negR _ => by intro V r η g hg a; rfl
  | _, _, .andR _ => by intro V r η g hg a; rfl
  | _, _, .orR _ => by intro V r η g hg a; rfl
  | _, _, .coextR ρ => by
    intro V r η g hg a
    change (∀ b : Args S.D ρ, _) ↔
      ∀ b : Args S.D ρ, S.rel ρ (η _ a.1) b ↔ S.rel ρ (η _ a.2.1) b
    apply forall_congr'
    intro b
    rw [Formula.realize_iff]
    change (S.rel ρ (η _ a.1) (mapArgs (extendEnv η ρ b) ρ (boundArgs V ρ)) ↔
      S.rel ρ (η _ a.2.1) (mapArgs (extendEnv η ρ b) ρ (boundArgs V ρ))) ↔ _
    rw [eval_boundArgs]
  | _, _, .boxR ρ => by
    intro V r η g hg a
    change S.rel ρ (η _ a.1) (mapArgs η ρ a.2) ↔
      ∀ (U : World) (j : World.star ⟶ U),
        S.rel ρ (η _ a.1) (Intensional.Args.map (inner S.D) ρ j (mapArgs η ρ a.2))
    simp only [args_map_eq]
    exact ⟨fun h _ _ => h, fun h => h World.star (𝟙 World.star)⟩
  | _, _, .inclR ρ => by
    intro V r η g hg a
    change (∀ b : Args S.D ρ, _) ↔
      ∀ b : Args S.D ρ, S.rel ρ (η _ a.1) b → S.rel ρ (η _ a.2.1) b
    apply forall_congr'
    intro b
    rw [Formula.realize_imp]
    change (S.rel ρ (η _ a.1) (mapArgs (extendEnv η ρ b) ρ (boundArgs V ρ)) →
      S.rel ρ (η _ a.2.1) (mapArgs (extendEnv η ρ b) ρ (boundArgs V ρ))) ↔ _
    rw [eval_boundArgs]

/-- The relational-output part of term closure follows from its value formula. -/
private theorem relational_sem_mem (S : Structure) (hC : Comprehension S)
    {Γ : Ctx} {ρ : RTy} (t : Term Signature.pure Γ (.rel ρ)) (g : IEnv S.D Γ) :
    S.model.sem (𝟙 World.star) t g ∈ Set.range (S.model.Incl (.rel ρ) World.star) := by
  let V : Ty → Type := fun τ => Var Γ τ
  let η : ∀ τ, V τ → S.D τ := fun _ v => g.get v
  apply admit_definable S hC ρ
    (translate t (Extend V ρ) (fun _ v => Sum.inl v) (boundArgs V ρ)) η
  intro a
  have hc := translate_correct S t (Extend V ρ) (fun _ v => Sum.inl v)
    (extendEnv η ρ a) g (fun _ _ => rfl) (boundArgs V ρ)
  change _ ↔ observe S (.rel ρ) _ (mapArgs (extendEnv η ρ a) ρ (boundArgs V ρ)) at hc
  rw [eval_boundArgs] at hc
  exact hc.symm

/-- First-order comprehension proves the actual `Premodel.IsModel` condition
for every term of the fixed relational grammar. -/
theorem isModel (S : Structure) (hC : Comprehension S) : S.model.IsModel := by
  intro Γ σ W h t g
  cases W
  cases h
  -- Eliminate the syntax while its result type is still general. Fixing an
  -- atomic result type first leaves the pure constant's empty index stuck.
  cases t with
  | var v => exact ⟨g.get v, rfl⟩
  | const c => exact Empty.elim (show Empty from c)
  | app f a => exact relational_sem_mem S hC (.app f a) g
  | lam b => exact relational_sem_mem S hC (.lam b) g
  | and => exact relational_sem_mem S hC .and g
  | or => exact relational_sem_mem S hC .or g
  | not => exact relational_sem_mem S hC .not g
  | all τ => exact relational_sem_mem S hC (.all τ) g
  | ex τ => exact relational_sem_mem S hC (.ex τ) g
  | eq τ => exact relational_sem_mem S hC (.eq τ) g
  | constR ρ => exact relational_sem_mem S hC (.constR ρ) g
  | negR ρ => exact relational_sem_mem S hC (.negR ρ) g
  | andR ρ => exact relational_sem_mem S hC (.andR ρ) g
  | orR ρ => exact relational_sem_mem S hC (.orR ρ) g
  | coextR ρ => exact relational_sem_mem S hC (.coextR ρ) g
  | boxR ρ => exact relational_sem_mem S hC (.boxR ρ) g
  | inclR ρ => exact relational_sem_mem S hC (.inclR ρ) g

/-- Soundness is the project's existing theorem, applied to the constructed model. -/
theorem c_theorem_holds (S : Structure) (hC : Comprehension S)
    {p : Sentence Signature.pure} (hp : C.Theorem p) : S.model.HoldsSentence p :=
  S.model.theorem_holds (isModel S hC) hp

abbrev NoVars (_ : Ty) := Empty

/-- The first-order translation of a closed pure Classicism sentence. -/
def sentenceTranslation (p : Sentence Signature.pure) : Formula NoVars :=
  translate p NoVars (fun _ v => nomatch v) PUnit.unit

theorem sentenceTranslation_correct (S : Structure) (p : Sentence Signature.pure) :
    (sentenceTranslation p).Realize S (fun _ x => nomatch x) ↔ S.model.HoldsSentence p :=
  translate_correct S p NoVars (fun _ v => nomatch v) (fun _ x => nomatch x)
    .nil (fun _ v => nomatch v) PUnit.unit

end Classicism.Meta.ChoiceFirstOrder
