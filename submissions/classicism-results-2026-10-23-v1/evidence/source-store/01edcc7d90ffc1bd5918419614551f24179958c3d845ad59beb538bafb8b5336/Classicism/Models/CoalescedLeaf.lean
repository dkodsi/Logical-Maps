import Classicism.Models.CoalescedBase
import Classicism.Semantics.IntensionalSoundness

/-!
# Exact terminal-component evaluation in the two-component coalescence

This is a structural induction on the full typed term syntax. It proves the transfer
for arbitrary premodels, before term closure is available. Component quantifiers keep
their original Henkin domains. No external fullness, modal assumption, or model
condition is required.
-/

namespace Classicism.Meta.Intensional.Coalesced

open CategoryTheory

variable (L R : Premodel Signature.pure One)

/-! Evaluation at the left terminal component. -/

@[simp] theorem left_outer_eval (ρ : RTy) (F : Intension (inner L R) ρ .left)
    (a : Args L.inner ρ .point) (h : One.point ⟶ One.point) :
    leftOuter L R (.rel ρ) F ⟨.point, a, h⟩ =
      F ⟨.left, (leftArgsEquiv L R ρ).symm a, 𝟙 World.left⟩ := rfl

@[simp] theorem left_args_symm_arr (σ : Ty) (ρ : RTy)
    (x : L.Dom .point σ) (a : Args L.inner ρ .point) :
    (leftArgsEquiv L R (.arr σ ρ)).symm (x, a) =
      (x, (leftArgsEquiv L R ρ).symm a) := rfl

@[simp] theorem left_incl_eval (ρ : RTy) (x : L.Dom .point (.rel ρ))
    (a : Args L.inner ρ .point) :
    (model L R).incl ρ .left x
        ⟨.left, (leftArgsEquiv L R ρ).symm a, 𝟙 World.left⟩ =
      L.incl ρ .point x ⟨.point, a, 𝟙 One.point⟩ := by
  change extension L ρ x (leftArgsEquiv L R ρ ((leftArgsEquiv L R ρ).symm a)) =
    extension L ρ x a
  rw [Equiv.apply_symm_apply]

theorem left_incl_eq (σ : Ty) (x : L.Dom .point σ)
    (y : Outer (inner L R) σ .left) :
    (model L R).Incl σ .left x = y ↔ L.Incl σ .point x = leftOuter L R σ y := by
  constructor
  · intro h
    simpa only [leftOuter_Incl] using congrArg (leftOuter L R σ) h
  · intro h
    apply (leftOuter L R σ).injective
    simpa only [leftOuter_Incl] using h

theorem left_apply {σ : Ty} {ρ : RTy}
    (F : Intension (inner L R) (.arr σ ρ) .left)
    (x : Outer (inner L R) σ .left) :
    leftOuter L R (.rel ρ) ((model L R).apply F x) =
      L.apply (leftOuter L R (.rel (.arr σ ρ)) F) (leftOuter L R σ x) := by
  ext ⟨V, a, h⟩
  cases V
  cases h
  change
    (∃ x' : L.Dom .point σ,
      (model L R).Incl σ .left x' = Outer.map (inner L R) σ (𝟙 World.left) x ∧
        F ⟨.left, (x', (leftArgsEquiv L R ρ).symm a), 𝟙 World.left⟩) ↔
    (∃ x' : L.Dom .point σ,
      L.Incl σ .point x' = Outer.map L.inner σ (𝟙 One.point) (leftOuter L R σ x) ∧
        F ⟨.left, (x', (leftArgsEquiv L R ρ).symm a), 𝟙 World.left⟩)
  simp only [Outer.map_id, left_incl_eq]

theorem left_constRead (ρ : RTy) :
    leftOuter L R (.rel (.arr (.rel .t) ρ)) ((model L R).constRead ρ .left) =
      L.constRead ρ .point := by
  ext ⟨V, ⟨x, a⟩, h⟩
  cases V
  cases h
  rfl

theorem left_negRead (ρ : RTy) :
    leftOuter L R (.rel (.arr (.rel ρ) ρ)) ((model L R).negRead ρ .left) =
      L.negRead ρ .point := by
  ext ⟨V, ⟨x, a⟩, h⟩
  cases V
  cases h
  change (¬ extension L ρ x (leftArgsEquiv L R ρ ((leftArgsEquiv L R ρ).symm a))) ↔ (¬ extension L ρ x a)
  rw [Equiv.apply_symm_apply]

theorem left_andRead (ρ : RTy) :
    leftOuter L R (.rel (.arr (.rel ρ) (.arr (.rel ρ) ρ)))
        ((model L R).andRead ρ .left) = L.andRead ρ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  change
    (extension L ρ x (leftArgsEquiv L R ρ ((leftArgsEquiv L R ρ).symm a)) ∧
      extension L ρ y (leftArgsEquiv L R ρ ((leftArgsEquiv L R ρ).symm a))) ↔
    (extension L ρ x a ∧ extension L ρ y a)
  rw [Equiv.apply_symm_apply]

theorem left_orRead (ρ : RTy) :
    leftOuter L R (.rel (.arr (.rel ρ) (.arr (.rel ρ) ρ)))
        ((model L R).orRead ρ .left) = L.orRead ρ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  change
    (extension L ρ x (leftArgsEquiv L R ρ ((leftArgsEquiv L R ρ).symm a)) ∨
      extension L ρ y (leftArgsEquiv L R ρ ((leftArgsEquiv L R ρ).symm a))) ↔
    (extension L ρ x a ∨ extension L ρ y a)
  rw [Equiv.apply_symm_apply]

theorem left_allRead (σ : Ty) :
    leftOuter L R (.rel (.arr (.rel (.arr σ .t)) .t))
        ((model L R).allRead σ .left) = L.allRead σ .point := by
  ext ⟨V, ⟨B, a⟩, h⟩
  cases V
  cases h
  rfl

theorem left_exRead (σ : Ty) :
    leftOuter L R (.rel (.arr (.rel (.arr σ .t)) .t))
        ((model L R).exRead σ .left) = L.exRead σ .point := by
  ext ⟨V, ⟨B, a⟩, h⟩
  cases V
  cases h
  rfl

theorem left_eqRead (σ : Ty) :
    leftOuter L R (.rel (.arr σ (.arr σ .t)))
        ((model L R).eqRead σ .left) = L.eqRead σ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  rfl

theorem left_coextRead (ρ : RTy) :
    leftOuter L R (.rel (.arr (.rel ρ) (.arr (.rel ρ) .t)))
        ((model L R).coextRead ρ .left) = L.coextRead ρ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  change (∀ b : Args (inner L R) ρ .left,
    extension L ρ x (leftArgsEquiv L R ρ b) ↔
      extension L ρ y (leftArgsEquiv L R ρ b)) ↔
    (∀ b : Args L.inner ρ .point, extension L ρ x b ↔ extension L ρ y b)
  constructor
  · intro H b
    simpa only [Equiv.apply_symm_apply] using H ((leftArgsEquiv L R ρ).symm b)
  · intro H b
    exact H (leftArgsEquiv L R ρ b)

theorem left_inclRead (ρ : RTy) :
    leftOuter L R (.rel (.arr (.rel ρ) (.arr (.rel ρ) .t)))
        ((model L R).inclRead ρ .left) = L.inclRead ρ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  change (∀ b : Args (inner L R) ρ .left,
    extension L ρ x (leftArgsEquiv L R ρ b) →
      extension L ρ y (leftArgsEquiv L R ρ b)) ↔
    (∀ b : Args L.inner ρ .point, extension L ρ x b → extension L ρ y b)
  constructor
  · intro H b
    simpa only [Equiv.apply_symm_apply] using H ((leftArgsEquiv L R ρ).symm b)
  · intro H b
    exact H (leftArgsEquiv L R ρ b)

theorem left_boxRead (ρ : RTy) :
    leftOuter L R (.rel (.arr (.rel ρ) ρ)) ((model L R).boxRead ρ .left) =
      L.boxRead ρ .point := by
  ext ⟨V, ⟨x, a⟩, h⟩
  cases V
  cases h
  change
    (∀ (U : World) (j : World.left ⟶ U),
      (model L R).incl ρ .left x
        ⟨U, Args.map (inner L R) ρ j ((leftArgsEquiv L R ρ).symm a), j⟩) ↔
    (∀ (U : One) (j : One.point ⟶ U),
      L.incl ρ .point x ⟨U, Args.map L.inner ρ j a, j⟩)
  constructor
  · intro H U j
    cases U
    cases j
    have h := H .left (𝟙 World.left)
    change extension L ρ x
      (leftArgsEquiv L R ρ
        (Args.map (inner L R) ρ (𝟙 World.left) ((leftArgsEquiv L R ρ).symm a))) at h
    change extension L ρ x (Args.map L.inner ρ (𝟙 One.point) a)
    simpa only [Args.map_id, Equiv.apply_symm_apply] using h
  · intro H U j
    cases j
    have h := H .point (𝟙 One.point)
    change extension L ρ x (Args.map L.inner ρ (𝟙 One.point) a) at h
    change extension L ρ x
      (leftArgsEquiv L R ρ
        (Args.map (inner L R) ρ (𝟙 World.left) ((leftArgsEquiv L R ρ).symm a)))
    simpa only [Args.map_id, Equiv.apply_symm_apply] using h

/-- Evaluation at the terminal leaf is evaluation in its original component,
including lambda binding and every primitive relational constructor. -/
theorem left_sem : ∀ {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ)
    (g : IEnv ((model L R).Dom .left) Γ),
    leftOuter L R σ ((model L R).sem toLeft t g) =
      L.sem (PUnit.unit : L.W₀ ⟶ One.point) t g
  | _, _, .var v, g => leftOuter_Incl L R _ (g.get v)
  | _, _, .const c, _ => nomatch c
  | _, _, .app f a, g => by
    rw [Premodel.sem.eq_def, left_apply, left_sem f g, left_sem a g] <;> rfl
  | _, _, .lam (ρ := ρ) b, g => by
    funext p
    rcases p with ⟨V, ⟨x, a⟩, h⟩
    cases V
    cases h
    have hb := congrFun (left_sem b (.cons x g)) ⟨.point, a, 𝟙 One.point⟩
    change
      (model L R).sem toLeft b (.cons x g)
          ⟨.left, (leftArgsEquiv L R ρ).symm a, 𝟙 World.left⟩ =
        L.sem (PUnit.unit : L.W₀ ⟶ One.point) b (.cons x g)
          ⟨.point, a, 𝟙 One.point⟩ at hb
    change
      (model L R).sem (toLeft ≫ 𝟙 World.left) b
          (.cons x ((model L R).push (𝟙 World.left) g))
          ⟨.left, (leftArgsEquiv L R ρ).symm a, 𝟙 World.left⟩ =
        L.sem ((PUnit.unit : L.W₀ ⟶ One.point) ≫ 𝟙 One.point) b
          (.cons x (L.push (𝟙 One.point) g)) ⟨.point, a, 𝟙 One.point⟩
    simpa only [Category.comp_id, Premodel.push_id] using hb
  | _, _, .and, _ => left_andRead L R .t
  | _, _, .or, _ => left_orRead L R .t
  | _, _, .not, _ => left_negRead L R .t
  | _, _, .all σ, _ => left_allRead L R σ
  | _, _, .ex σ, _ => left_exRead L R σ
  | _, _, .eq σ, _ => left_eqRead L R σ
  | _, _, .constR ρ, _ => left_constRead L R ρ
  | _, _, .negR ρ, _ => left_negRead L R ρ
  | _, _, .andR ρ, _ => left_andRead L R ρ
  | _, _, .orR ρ, _ => left_orRead L R ρ
  | _, _, .coextR ρ, _ => left_coextRead L R ρ
  | _, _, .boxR ρ, _ => left_boxRead L R ρ
  | _, _, .inclR ρ, _ => left_inclRead L R ρ

theorem holds_left {Γ : Ctx} (p : Formula Signature.pure Γ)
    (g : IEnv ((model L R).Dom .left) Γ) :
    (model L R).Holds toLeft p g ↔
      L.Holds (PUnit.unit : L.W₀ ⟶ One.point) p g := by
  have h := congrFun (left_sem L R p g) ⟨.point, PUnit.unit, 𝟙 One.point⟩
  exact Iff.of_eq h

/-! Evaluation at the right terminal component. -/

@[simp] theorem right_outer_eval (ρ : RTy) (F : Intension (inner L R) ρ .right)
    (a : Args R.inner ρ .point) (h : One.point ⟶ One.point) :
    rightOuter L R (.rel ρ) F ⟨.point, a, h⟩ =
      F ⟨.right, (rightArgsEquiv L R ρ).symm a, 𝟙 World.right⟩ := rfl

@[simp] theorem right_args_symm_arr (σ : Ty) (ρ : RTy)
    (x : R.Dom .point σ) (a : Args R.inner ρ .point) :
    (rightArgsEquiv L R (.arr σ ρ)).symm (x, a) =
      (x, (rightArgsEquiv L R ρ).symm a) := rfl

@[simp] theorem right_incl_eval (ρ : RTy) (x : R.Dom .point (.rel ρ))
    (a : Args R.inner ρ .point) :
    (model L R).incl ρ .right x
        ⟨.right, (rightArgsEquiv L R ρ).symm a, 𝟙 World.right⟩ =
      R.incl ρ .point x ⟨.point, a, 𝟙 One.point⟩ := by
  change extension R ρ x (rightArgsEquiv L R ρ ((rightArgsEquiv L R ρ).symm a)) =
    extension R ρ x a
  rw [Equiv.apply_symm_apply]

theorem right_incl_eq (σ : Ty) (x : R.Dom .point σ)
    (y : Outer (inner L R) σ .right) :
    (model L R).Incl σ .right x = y ↔ R.Incl σ .point x = rightOuter L R σ y := by
  constructor
  · intro h
    simpa only [rightOuter_Incl] using congrArg (rightOuter L R σ) h
  · intro h
    apply (rightOuter L R σ).injective
    simpa only [rightOuter_Incl] using h

theorem right_apply {σ : Ty} {ρ : RTy}
    (F : Intension (inner L R) (.arr σ ρ) .right)
    (x : Outer (inner L R) σ .right) :
    rightOuter L R (.rel ρ) ((model L R).apply F x) =
      R.apply (rightOuter L R (.rel (.arr σ ρ)) F) (rightOuter L R σ x) := by
  ext ⟨V, a, h⟩
  cases V
  cases h
  change
    (∃ x' : R.Dom .point σ,
      (model L R).Incl σ .right x' = Outer.map (inner L R) σ (𝟙 World.right) x ∧
        F ⟨.right, (x', (rightArgsEquiv L R ρ).symm a), 𝟙 World.right⟩) ↔
    (∃ x' : R.Dom .point σ,
      R.Incl σ .point x' = Outer.map R.inner σ (𝟙 One.point) (rightOuter L R σ x) ∧
        F ⟨.right, (x', (rightArgsEquiv L R ρ).symm a), 𝟙 World.right⟩)
  simp only [Outer.map_id, right_incl_eq]

theorem right_constRead (ρ : RTy) :
    rightOuter L R (.rel (.arr (.rel .t) ρ)) ((model L R).constRead ρ .right) =
      R.constRead ρ .point := by
  ext ⟨V, ⟨x, a⟩, h⟩
  cases V
  cases h
  rfl

theorem right_negRead (ρ : RTy) :
    rightOuter L R (.rel (.arr (.rel ρ) ρ)) ((model L R).negRead ρ .right) =
      R.negRead ρ .point := by
  ext ⟨V, ⟨x, a⟩, h⟩
  cases V
  cases h
  change (¬ extension R ρ x (rightArgsEquiv L R ρ ((rightArgsEquiv L R ρ).symm a))) ↔ (¬ extension R ρ x a)
  rw [Equiv.apply_symm_apply]

theorem right_andRead (ρ : RTy) :
    rightOuter L R (.rel (.arr (.rel ρ) (.arr (.rel ρ) ρ)))
        ((model L R).andRead ρ .right) = R.andRead ρ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  change
    (extension R ρ x (rightArgsEquiv L R ρ ((rightArgsEquiv L R ρ).symm a)) ∧
      extension R ρ y (rightArgsEquiv L R ρ ((rightArgsEquiv L R ρ).symm a))) ↔
    (extension R ρ x a ∧ extension R ρ y a)
  rw [Equiv.apply_symm_apply]

theorem right_orRead (ρ : RTy) :
    rightOuter L R (.rel (.arr (.rel ρ) (.arr (.rel ρ) ρ)))
        ((model L R).orRead ρ .right) = R.orRead ρ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  change
    (extension R ρ x (rightArgsEquiv L R ρ ((rightArgsEquiv L R ρ).symm a)) ∨
      extension R ρ y (rightArgsEquiv L R ρ ((rightArgsEquiv L R ρ).symm a))) ↔
    (extension R ρ x a ∨ extension R ρ y a)
  rw [Equiv.apply_symm_apply]

theorem right_allRead (σ : Ty) :
    rightOuter L R (.rel (.arr (.rel (.arr σ .t)) .t))
        ((model L R).allRead σ .right) = R.allRead σ .point := by
  ext ⟨V, ⟨B, a⟩, h⟩
  cases V
  cases h
  rfl

theorem right_exRead (σ : Ty) :
    rightOuter L R (.rel (.arr (.rel (.arr σ .t)) .t))
        ((model L R).exRead σ .right) = R.exRead σ .point := by
  ext ⟨V, ⟨B, a⟩, h⟩
  cases V
  cases h
  rfl

theorem right_eqRead (σ : Ty) :
    rightOuter L R (.rel (.arr σ (.arr σ .t)))
        ((model L R).eqRead σ .right) = R.eqRead σ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  rfl

theorem right_coextRead (ρ : RTy) :
    rightOuter L R (.rel (.arr (.rel ρ) (.arr (.rel ρ) .t)))
        ((model L R).coextRead ρ .right) = R.coextRead ρ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  change (∀ b : Args (inner L R) ρ .right,
    extension R ρ x (rightArgsEquiv L R ρ b) ↔
      extension R ρ y (rightArgsEquiv L R ρ b)) ↔
    (∀ b : Args R.inner ρ .point, extension R ρ x b ↔ extension R ρ y b)
  constructor
  · intro H b
    simpa only [Equiv.apply_symm_apply] using H ((rightArgsEquiv L R ρ).symm b)
  · intro H b
    exact H (rightArgsEquiv L R ρ b)

theorem right_inclRead (ρ : RTy) :
    rightOuter L R (.rel (.arr (.rel ρ) (.arr (.rel ρ) .t)))
        ((model L R).inclRead ρ .right) = R.inclRead ρ .point := by
  ext ⟨V, ⟨x, y, a⟩, h⟩
  cases V
  cases h
  change (∀ b : Args (inner L R) ρ .right,
    extension R ρ x (rightArgsEquiv L R ρ b) →
      extension R ρ y (rightArgsEquiv L R ρ b)) ↔
    (∀ b : Args R.inner ρ .point, extension R ρ x b → extension R ρ y b)
  constructor
  · intro H b
    simpa only [Equiv.apply_symm_apply] using H ((rightArgsEquiv L R ρ).symm b)
  · intro H b
    exact H (rightArgsEquiv L R ρ b)

theorem right_boxRead (ρ : RTy) :
    rightOuter L R (.rel (.arr (.rel ρ) ρ)) ((model L R).boxRead ρ .right) =
      R.boxRead ρ .point := by
  ext ⟨V, ⟨x, a⟩, h⟩
  cases V
  cases h
  change
    (∀ (U : World) (j : World.right ⟶ U),
      (model L R).incl ρ .right x
        ⟨U, Args.map (inner L R) ρ j ((rightArgsEquiv L R ρ).symm a), j⟩) ↔
    (∀ (U : One) (j : One.point ⟶ U),
      R.incl ρ .point x ⟨U, Args.map R.inner ρ j a, j⟩)
  constructor
  · intro H U j
    cases U
    cases j
    have h := H .right (𝟙 World.right)
    change extension R ρ x
      (rightArgsEquiv L R ρ
        (Args.map (inner L R) ρ (𝟙 World.right) ((rightArgsEquiv L R ρ).symm a))) at h
    change extension R ρ x (Args.map R.inner ρ (𝟙 One.point) a)
    simpa only [Args.map_id, Equiv.apply_symm_apply] using h
  · intro H U j
    cases j
    have h := H .point (𝟙 One.point)
    change extension R ρ x (Args.map R.inner ρ (𝟙 One.point) a) at h
    change extension R ρ x
      (rightArgsEquiv L R ρ
        (Args.map (inner L R) ρ (𝟙 World.right) ((rightArgsEquiv L R ρ).symm a)))
    simpa only [Args.map_id, Equiv.apply_symm_apply] using h

/-- Evaluation at the terminal leaf is evaluation in its original component,
including lambda binding and every primitive relational constructor. -/
theorem right_sem : ∀ {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ)
    (g : IEnv ((model L R).Dom .right) Γ),
    rightOuter L R σ ((model L R).sem toRight t g) =
      R.sem (PUnit.unit : R.W₀ ⟶ One.point) t g
  | _, _, .var v, g => rightOuter_Incl L R _ (g.get v)
  | _, _, .const c, _ => nomatch c
  | _, _, .app f a, g => by
    rw [Premodel.sem.eq_def, right_apply, right_sem f g, right_sem a g] <;> rfl
  | _, _, .lam (ρ := ρ) b, g => by
    funext p
    rcases p with ⟨V, ⟨x, a⟩, h⟩
    cases V
    cases h
    have hb := congrFun (right_sem b (.cons x g)) ⟨.point, a, 𝟙 One.point⟩
    change
      (model L R).sem toRight b (.cons x g)
          ⟨.right, (rightArgsEquiv L R ρ).symm a, 𝟙 World.right⟩ =
        R.sem (PUnit.unit : R.W₀ ⟶ One.point) b (.cons x g)
          ⟨.point, a, 𝟙 One.point⟩ at hb
    change
      (model L R).sem (toRight ≫ 𝟙 World.right) b
          (.cons x ((model L R).push (𝟙 World.right) g))
          ⟨.right, (rightArgsEquiv L R ρ).symm a, 𝟙 World.right⟩ =
        R.sem ((PUnit.unit : R.W₀ ⟶ One.point) ≫ 𝟙 One.point) b
          (.cons x (R.push (𝟙 One.point) g)) ⟨.point, a, 𝟙 One.point⟩
    simpa only [Category.comp_id, Premodel.push_id] using hb
  | _, _, .and, _ => right_andRead L R .t
  | _, _, .or, _ => right_orRead L R .t
  | _, _, .not, _ => right_negRead L R .t
  | _, _, .all σ, _ => right_allRead L R σ
  | _, _, .ex σ, _ => right_exRead L R σ
  | _, _, .eq σ, _ => right_eqRead L R σ
  | _, _, .constR ρ, _ => right_constRead L R ρ
  | _, _, .negR ρ, _ => right_negRead L R ρ
  | _, _, .andR ρ, _ => right_andRead L R ρ
  | _, _, .orR ρ, _ => right_orRead L R ρ
  | _, _, .coextR ρ, _ => right_coextRead L R ρ
  | _, _, .boxR ρ, _ => right_boxRead L R ρ
  | _, _, .inclR ρ, _ => right_inclRead L R ρ

theorem holds_right {Γ : Ctx} (p : Formula Signature.pure Γ)
    (g : IEnv ((model L R).Dom .right) Γ) :
    (model L R).Holds toRight p g ↔
      R.Holds (PUnit.unit : R.W₀ ⟶ One.point) p g := by
  have h := congrFun (right_sem L R p g) ⟨.point, PUnit.unit, 𝟙 One.point⟩
  exact Iff.of_eq h

#print axioms left_sem
#print axioms right_sem
#print axioms holds_left
#print axioms holds_right

end Classicism.Meta.Intensional.Coalesced

