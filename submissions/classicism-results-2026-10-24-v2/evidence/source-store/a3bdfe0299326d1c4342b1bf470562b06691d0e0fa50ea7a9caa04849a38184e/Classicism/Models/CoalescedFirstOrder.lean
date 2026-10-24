import Classicism.Models.CoalescedBase
import Classicism.Models.ChoiceFirstOrderSmall

/-!
# First-order Henkin structures on the coalescence singleton category

Original formalization, misc, Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. This changes only the singleton category used to present the
existing `ChoiceFirstOrder.Structure.model`. The domains and application
relations are unchanged. Explicit tuple equivalences and induction on every
term constructor prove semantic transfer; small definable comprehension then
supplies actual term closure. Neither sentence truth nor modelhood is a field.

The semantic comparison follows the terminal comparison in `CoalescedLeaf`.
No set-theoretic model existence or CH verdict is asserted in this module.
-/

namespace Classicism.Meta.Intensional.Coalesced.FirstOrderBridge

open CategoryTheory

variable (S : ChoiceFirstOrder.Structure)

def action (X : Type) : One ⥤ Type where
  obj _ := X
  map _ := 𝟙 X
  map_id _ := rfl
  map_comp _ _ := rfl

def inner (σ : Ty) : One ⥤ Type := action (S.D σ)

def argsEquiv : (ρ : RTy) → (W : One) →
    Args (inner S) ρ W ≃ ChoiceFirstOrder.Args S.D ρ
  | .t, _ => Equiv.refl _
  | .arr _ ρ, W => Equiv.prodCongr (Equiv.refl _) (argsEquiv ρ W)

/-- The same sorted domains and relations, presented over `Coalesced.One`. -/
def model : Premodel Signature.pure One where
  W₀ := One.point
  inner := inner S
  nonempty_e _ := S.nonempty_e
  incl ρ _ X := fun p => S.rel ρ X (argsEquiv S ρ p.1 p.2.1)
  incl_map := by intros; rfl
  incl_injective ρ W := by
    intro X Y h
    apply S.rel_injective ρ
    funext a
    have he := congrFun h ⟨W, (argsEquiv S ρ W).symm a, 𝟙 W⟩
    simpa only [Equiv.apply_symm_apply] using he
  I c := nomatch c

def tupleTo (ρ : RTy) : Tuple (inner S) ρ One.point →
    Tuple S.model.inner ρ ChoiceFirstOrder.World.star
  | ⟨One.point, a, _⟩ => ⟨ChoiceFirstOrder.World.star, argsEquiv S ρ One.point a, 𝟙 ChoiceFirstOrder.World.star⟩

def tupleFrom (ρ : RTy) : Tuple S.model.inner ρ ChoiceFirstOrder.World.star →
    Tuple (inner S) ρ One.point
  | ⟨ChoiceFirstOrder.World.star, a, _⟩ => ⟨One.point, (argsEquiv S ρ One.point).symm a, 𝟙 One.point⟩

def tupleEquiv (ρ : RTy) : Tuple (inner S) ρ One.point ≃
    Tuple S.model.inner ρ ChoiceFirstOrder.World.star where
  toFun := tupleTo S ρ
  invFun := tupleFrom S ρ
  left_inv p := by
    rcases p with ⟨W, a, h⟩
    cases W
    cases h
    exact congrArg
      (fun b : Args (inner S) ρ One.point =>
        (⟨One.point, b, 𝟙 One.point⟩ : Tuple (inner S) ρ One.point))
      ((argsEquiv S ρ One.point).symm_apply_apply a)
  right_inv p := by
    rcases p with ⟨W, a, h⟩
    cases W
    cases h
    exact congrArg
      (fun b : ChoiceFirstOrder.Args S.D ρ =>
        (⟨ChoiceFirstOrder.World.star, b, 𝟙 ChoiceFirstOrder.World.star⟩ :
          Tuple S.model.inner ρ ChoiceFirstOrder.World.star))
      ((argsEquiv S ρ One.point).apply_symm_apply a)

def outer : (σ : Ty) → Outer (inner S) σ One.point ≃
    Outer S.model.inner σ ChoiceFirstOrder.World.star
  | .e => Equiv.refl _
  | .rel ρ => setEquiv (tupleEquiv S ρ)
  | .var _ => Equiv.refl _

@[simp] theorem outer_eval (ρ : RTy) (F : Intension (inner S) ρ One.point)
    (a : ChoiceFirstOrder.Args S.D ρ)
    (h : ChoiceFirstOrder.World.star ⟶ ChoiceFirstOrder.World.star) :
    outer S (.rel ρ) F ⟨ChoiceFirstOrder.World.star, a, h⟩ =
      F ⟨One.point, (argsEquiv S ρ One.point).symm a, 𝟙 One.point⟩ := rfl

@[simp] theorem args_symm_arr (σ : Ty) (ρ : RTy) (x : S.D σ)
    (a : ChoiceFirstOrder.Args S.D ρ) :
    (argsEquiv S (.arr σ ρ) One.point).symm (x, a) =
      (x, (argsEquiv S ρ One.point).symm a) := rfl

@[simp] theorem incl_eval (ρ : RTy) (x : S.D (.rel ρ))
    (a : ChoiceFirstOrder.Args S.D ρ) :
    (model S).incl ρ One.point x
        ⟨One.point, (argsEquiv S ρ One.point).symm a, 𝟙 One.point⟩ =
      S.model.incl ρ ChoiceFirstOrder.World.star x ⟨ChoiceFirstOrder.World.star, a, 𝟙 ChoiceFirstOrder.World.star⟩ := by
  change S.rel ρ x (argsEquiv S ρ One.point ((argsEquiv S ρ One.point).symm a)) = S.rel ρ x a
  rw [Equiv.apply_symm_apply]

@[simp] theorem outer_Incl (σ : Ty) (x : S.D σ) :
    outer S σ ((model S).Incl σ One.point x) = S.model.Incl σ ChoiceFirstOrder.World.star x := by
  cases σ with
  | e => rfl
  | var i => rfl
  | rel ρ =>
    funext p
    rcases p with ⟨W, a, h⟩
    cases W
    cases h
    exact incl_eval S ρ x a

theorem incl_eq (σ : Ty) (x : S.D σ) (y : Outer (inner S) σ One.point) :
    (model S).Incl σ One.point x = y ↔ S.model.Incl σ ChoiceFirstOrder.World.star x = outer S σ y := by
  constructor
  · intro h
    simpa only [outer_Incl] using congrArg (outer S σ) h
  · intro h
    apply (outer S σ).injective
    simpa only [outer_Incl] using h

theorem apply_transfer {σ : Ty} {ρ : RTy}
    (F : Intension (inner S) (.arr σ ρ) One.point) (x : Outer (inner S) σ One.point) :
    outer S (.rel ρ) ((model S).apply F x) =
      S.model.apply (outer S (.rel (.arr σ ρ)) F) (outer S σ x) := by
  ext ⟨W, a, h⟩
  cases W
  cases h
  change
    (∃ x' : S.D σ,
      (model S).Incl σ One.point x' = Outer.map (inner S) σ (𝟙 One.point) x ∧
        F ⟨One.point, (x', (argsEquiv S ρ One.point).symm a), 𝟙 One.point⟩) ↔
    (∃ x' : S.D σ,
      S.model.Incl σ ChoiceFirstOrder.World.star x' =
        Outer.map S.model.inner σ (𝟙 ChoiceFirstOrder.World.star) (outer S σ x) ∧
        F ⟨One.point, (x', (argsEquiv S ρ One.point).symm a), 𝟙 One.point⟩)
  simp only [Outer.map_id, incl_eq]

theorem constRead_transfer (ρ : RTy) :
    outer S (.rel (.arr (.rel .t) ρ)) ((model S).constRead ρ One.point) =
      S.model.constRead ρ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, a⟩, h⟩
  cases W
  cases h
  rfl

theorem negRead_transfer (ρ : RTy) :
    outer S (.rel (.arr (.rel ρ) ρ)) ((model S).negRead ρ One.point) =
      S.model.negRead ρ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, a⟩, h⟩
  cases W
  cases h
  change (¬ S.rel ρ x (argsEquiv S ρ One.point ((argsEquiv S ρ One.point).symm a))) ↔
    (¬ S.rel ρ x a)
  exact Iff.of_eq (congrArg
    (fun b : ChoiceFirstOrder.Args S.D ρ => ¬ S.rel ρ x b)
    ((argsEquiv S ρ One.point).apply_symm_apply a))

theorem andRead_transfer (ρ : RTy) :
    outer S (.rel (.arr (.rel ρ) (.arr (.rel ρ) ρ))) ((model S).andRead ρ One.point) =
      S.model.andRead ρ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, y, a⟩, h⟩
  cases W
  cases h
  change
    (S.rel ρ x (argsEquiv S ρ One.point ((argsEquiv S ρ One.point).symm a)) ∧
      S.rel ρ y (argsEquiv S ρ One.point ((argsEquiv S ρ One.point).symm a))) ↔
    (S.rel ρ x a ∧ S.rel ρ y a)
  exact Iff.of_eq (congrArg
    (fun b : ChoiceFirstOrder.Args S.D ρ => S.rel ρ x b ∧ S.rel ρ y b)
    ((argsEquiv S ρ One.point).apply_symm_apply a))

theorem orRead_transfer (ρ : RTy) :
    outer S (.rel (.arr (.rel ρ) (.arr (.rel ρ) ρ))) ((model S).orRead ρ One.point) =
      S.model.orRead ρ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, y, a⟩, h⟩
  cases W
  cases h
  change
    (S.rel ρ x (argsEquiv S ρ One.point ((argsEquiv S ρ One.point).symm a)) ∨
      S.rel ρ y (argsEquiv S ρ One.point ((argsEquiv S ρ One.point).symm a))) ↔
    (S.rel ρ x a ∨ S.rel ρ y a)
  exact Iff.of_eq (congrArg
    (fun b : ChoiceFirstOrder.Args S.D ρ => S.rel ρ x b ∨ S.rel ρ y b)
    ((argsEquiv S ρ One.point).apply_symm_apply a))

theorem allRead_transfer (σ : Ty) :
    outer S (.rel (.arr (.rel (.arr σ .t)) .t)) ((model S).allRead σ One.point) =
      S.model.allRead σ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, a⟩, h⟩
  cases W
  cases h
  rfl

theorem exRead_transfer (σ : Ty) :
    outer S (.rel (.arr (.rel (.arr σ .t)) .t)) ((model S).exRead σ One.point) =
      S.model.exRead σ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, a⟩, h⟩
  cases W
  cases h
  rfl

theorem eqRead_transfer (σ : Ty) :
    outer S (.rel (.arr σ (.arr σ .t))) ((model S).eqRead σ One.point) =
      S.model.eqRead σ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, y, a⟩, h⟩
  cases W
  cases h
  rfl

theorem coextRead_transfer (ρ : RTy) :
    outer S (.rel (.arr (.rel ρ) (.arr (.rel ρ) .t))) ((model S).coextRead ρ One.point) =
      S.model.coextRead ρ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, y, a⟩, h⟩
  cases W
  cases h
  change (∀ b : Args (inner S) ρ One.point,
    S.rel ρ x (argsEquiv S ρ One.point b) ↔ S.rel ρ y (argsEquiv S ρ One.point b)) ↔
      (∀ b : ChoiceFirstOrder.Args S.D ρ, S.rel ρ x b ↔ S.rel ρ y b)
  constructor
  · intro H b
    simpa only [Equiv.apply_symm_apply] using H ((argsEquiv S ρ One.point).symm b)
  · intro H b
    exact H (argsEquiv S ρ One.point b)

theorem inclRead_transfer (ρ : RTy) :
    outer S (.rel (.arr (.rel ρ) (.arr (.rel ρ) .t))) ((model S).inclRead ρ One.point) =
      S.model.inclRead ρ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, y, a⟩, h⟩
  cases W
  cases h
  change (∀ b : Args (inner S) ρ One.point,
    S.rel ρ x (argsEquiv S ρ One.point b) → S.rel ρ y (argsEquiv S ρ One.point b)) ↔
      (∀ b : ChoiceFirstOrder.Args S.D ρ, S.rel ρ x b → S.rel ρ y b)
  constructor
  · intro H b
    simpa only [Equiv.apply_symm_apply] using H ((argsEquiv S ρ One.point).symm b)
  · intro H b
    exact H (argsEquiv S ρ One.point b)

theorem boxRead_transfer (ρ : RTy) :
    outer S (.rel (.arr (.rel ρ) ρ)) ((model S).boxRead ρ One.point) =
      S.model.boxRead ρ ChoiceFirstOrder.World.star := by
  ext ⟨W, ⟨x, a⟩, h⟩
  cases W
  cases h
  change
    (∀ (U : One) (j : One.point ⟶ U),
      (model S).incl ρ One.point x
        ⟨U, Args.map (inner S) ρ j ((argsEquiv S ρ One.point).symm a), j⟩) ↔
    (∀ (U : ChoiceFirstOrder.World) (j : ChoiceFirstOrder.World.star ⟶ U),
      S.model.incl ρ ChoiceFirstOrder.World.star x
        ⟨U, Args.map S.model.inner ρ j a, j⟩)
  have hargs : argsEquiv S ρ One.point
      (Args.map (inner S) ρ (𝟙 One.point) ((argsEquiv S ρ One.point).symm a)) =
      Args.map S.model.inner ρ (𝟙 ChoiceFirstOrder.World.star) a :=
    ((congrArg (argsEquiv S ρ One.point)
      (Args.map_id (inner S) ρ One.point ((argsEquiv S ρ One.point).symm a))).trans
        ((argsEquiv S ρ One.point).apply_symm_apply a)).trans
      (Args.map_id S.model.inner ρ ChoiceFirstOrder.World.star a).symm
  constructor
  · intro H U j
    cases U
    cases j
    have he := H One.point (𝟙 One.point)
    change S.rel ρ x (argsEquiv S ρ One.point
      (Args.map (inner S) ρ (𝟙 One.point) ((argsEquiv S ρ One.point).symm a))) at he
    change S.rel ρ x (Args.map S.model.inner ρ (𝟙 ChoiceFirstOrder.World.star) a)
    exact hargs ▸ he
  · intro H U j
    cases U
    cases j
    have he := H ChoiceFirstOrder.World.star (𝟙 ChoiceFirstOrder.World.star)
    change S.rel ρ x (Args.map S.model.inner ρ (𝟙 ChoiceFirstOrder.World.star) a) at he
    change S.rel ρ x (argsEquiv S ρ One.point
      (Args.map (inner S) ρ (𝟙 One.point) ((argsEquiv S ρ One.point).symm a)))
    exact hargs.symm ▸ he

/-- Every term, including abstraction, retains its interpretation. -/
theorem sem_transfer : ∀ {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ)
    (g : IEnv S.D Γ),
    outer S σ ((model S).sem (𝟙 One.point) t g) =
      S.model.sem (𝟙 ChoiceFirstOrder.World.star) t g
  | _, _, .var v, g => outer_Incl S _ (g.get v)
  | _, _, .const c, _ => nomatch c
  | _, _, .app (σ := σ) (ρ := ρ) f a, g => by
    exact (apply_transfer S
      ((model S).sem (𝟙 One.point) f g)
      ((model S).sem (𝟙 One.point) a g)).trans
      (congrArg₂ (S.model.apply (σ := σ) (ρ := ρ) (W := ChoiceFirstOrder.World.star))
        (sem_transfer f g) (sem_transfer a g))
  | _, _, .lam (ρ := ρ) b, g => by
    funext p
    rcases p with ⟨W, ⟨x, a⟩, h⟩
    cases W
    cases h
    have hb := congrFun (sem_transfer b (.cons x g))
      ⟨ChoiceFirstOrder.World.star, a, 𝟙 ChoiceFirstOrder.World.star⟩
    change
      (model S).sem (𝟙 One.point) b (.cons x g)
          ⟨One.point, (argsEquiv S ρ One.point).symm a, 𝟙 One.point⟩ =
        S.model.sem (𝟙 ChoiceFirstOrder.World.star) b (.cons x g)
          ⟨ChoiceFirstOrder.World.star, a, 𝟙 ChoiceFirstOrder.World.star⟩ at hb
    change
      (model S).sem ((𝟙 One.point) ≫ 𝟙 One.point) b
          (.cons x ((model S).push (𝟙 One.point) g))
          ⟨One.point, (argsEquiv S ρ One.point).symm a, 𝟙 One.point⟩ =
        S.model.sem ((𝟙 ChoiceFirstOrder.World.star) ≫ 𝟙 ChoiceFirstOrder.World.star) b
          (.cons x (S.model.push (𝟙 ChoiceFirstOrder.World.star) g))
          ⟨ChoiceFirstOrder.World.star, a, 𝟙 ChoiceFirstOrder.World.star⟩
    have hl := congrArg
      (fun env : IEnv S.D _ =>
        (model S).sem (𝟙 One.point) b (.cons x env)
          ⟨One.point, (argsEquiv S ρ One.point).symm a, 𝟙 One.point⟩)
      ((model S).push_id (W := One.point) g)
    have hr := congrArg
      (fun env : IEnv S.D _ =>
        S.model.sem (𝟙 ChoiceFirstOrder.World.star) b (.cons x env)
          ⟨ChoiceFirstOrder.World.star, a, 𝟙 ChoiceFirstOrder.World.star⟩)
      (S.model.push_id (W := ChoiceFirstOrder.World.star) g)
    exact hl.trans (hb.trans hr.symm)
  | _, _, .and, _ => andRead_transfer S .t
  | _, _, .or, _ => orRead_transfer S .t
  | _, _, .not, _ => negRead_transfer S .t
  | _, _, .all σ, _ => allRead_transfer S σ
  | _, _, .ex σ, _ => exRead_transfer S σ
  | _, _, .eq σ, _ => eqRead_transfer S σ
  | _, _, .constR ρ, _ => constRead_transfer S ρ
  | _, _, .negR ρ, _ => negRead_transfer S ρ
  | _, _, .andR ρ, _ => andRead_transfer S ρ
  | _, _, .orR ρ, _ => orRead_transfer S ρ
  | _, _, .coextR ρ, _ => coextRead_transfer S ρ
  | _, _, .boxR ρ, _ => boxRead_transfer S ρ
  | _, _, .inclR ρ, _ => inclRead_transfer S ρ

theorem holdsSentence_iff (p : Sentence Signature.pure) :
    (model S).HoldsSentence p ↔ S.model.HoldsSentence p := by
  have h := congrFun (sem_transfer S p .nil) ⟨ChoiceFirstOrder.World.star, PUnit.unit, 𝟙 ChoiceFirstOrder.World.star⟩
  exact Iff.of_eq h

/-- Actual term closure follows from the established first-order comprehension
theorem and the explicit equality of term interpretations above. -/
theorem isModel (hC : ChoiceFirstOrder.SmallComprehension S) : (model S).IsModel := by
  intro Γ σ W h t g
  cases W
  cases h
  obtain ⟨x, hx⟩ := ChoiceFirstOrder.isModel_of_small_comprehension S hC
    (𝟙 ChoiceFirstOrder.World.star) t g
  refine ⟨x, ?_⟩
  exact (outer S σ).injective
    ((outer_Incl S σ x).trans (hx.trans (sem_transfer S t g).symm))

#print axioms model
#print axioms sem_transfer
#print axioms holdsSentence_iff
#print axioms isModel

end Classicism.Meta.Intensional.Coalesced.FirstOrderBridge
