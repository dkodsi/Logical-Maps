import Classicism.Results.Research.InfinitaryComprehensionCanonical
import Classicism.Semantics.FullModels

/-!
# Comprehension and Atomicity in general action models

Direct source: research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md, sections 2--3 (misc, 23 October 2026, unpaginated).

The points of a relational support are all outgoing-world argument tuples,
not tuples of root objects. No C5, Barcan, injective action, surjective
action, or constant-domain presentation is assumed. The generic profile
lemma is obtained by interpreting the actual boxed comprehension formula.
Faithfulness comes from the premodel's injective inclusion. Complement and
arbitrary intersections are then represented by actual matrices.

This is source development in ordinary Lean model theory, not a shallow C
proof or a completed compiler certificate.
-/

namespace Classicism.Research.InfinitaryComprehension.Canonical

open Classicism.Meta Classicism.Meta.Intensional CategoryTheory

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C)

theorem sem_transport {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) :
    ∀ {Γ σ W} (h : A.W₀ ⟶ W) (p : ITerm Param Γ σ)
      (g : IEnv (A.Dom W) Γ) {V} (k : W ⟶ V),
      sem A η (h ≫ k) p (A.push k g) =
        Outer.map A.inner σ k (sem A η h p g)
  | _, _, _, h, .var v, g, _, k => by
      simp only [sem, Premodel.push, IEnv.get_map, A.Incl_map]
  | _, _, _, h, .param p, g, _, k => by
      simp only [sem, Functor.map_comp, types_comp_apply, A.Incl_map]
  | _, _, _, h, .app f a, g, _, k => by
      change A.apply (sem A η (h ≫ k) f (A.push k g))
        (sem A η (h ≫ k) a (A.push k g)) = _
      rw [sem_transport η h f g k, sem_transport η h a g k]
      exact A.apply_map k _ _
  | _, _, _, _, .top, _, _, _ => rfl
  | _, _, _, _, .bot, _, _, _ => rfl
  | _, _, _, h, .neg p, g, _, k => by
      simp only [sem, sem_transport η h p g k, Outer.map_rel] <;> rfl
  | _, _, _, h, .conj p q, g, _, k => by
      simp only [sem, sem_transport η h p g k,
        sem_transport η h q g k, Outer.map_rel] <;> rfl
  | _, _, _, h, .disj p q, g, _, k => by
      simp only [sem, sem_transport η h p g k,
        sem_transport η h q g k, Outer.map_rel] <;> rfl
  | _, _, _, h, .imp p q, g, _, k => by
      simp only [sem, sem_transport η h p g k,
        sem_transport η h q g k, Outer.map_rel] <;> rfl
  | _, _, _, h, .iff p q, g, _, k => by
      simp only [sem, sem_transport η h p g k,
        sem_transport η h q g k, Outer.map_rel] <;> rfl
  | _, _, _, h, .eq p q, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.mem_map, Set.mem_setOf_eq,
        sem_transport η h p g k, sem_transport η h q g k,
        Outer.map_comp]
  | _, _, _, _, .boxOp, _, _, _ => rfl
  | _, _, _, h, .all p, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.mem_map, Set.mem_setOf_eq,
        Category.assoc, A.push_push]
  | _, _, _, h, .ex p, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.mem_map, Set.mem_setOf_eq,
        Category.assoc, A.push_push]
  | _, _, _, h, .iAnd I p, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.mem_map, Set.mem_setOf_eq,
        sem_transport η h (p _) g k]
  | _, _, _, h, .iOr I p, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.mem_map, Set.mem_setOf_eq,
        sem_transport η h (p _) g k]

theorem mem_sem_iff {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    {Γ W} (h : A.W₀ ⟶ W) (p : ITerm Param Γ Ty.t)
    (g : IEnv (A.Dom W) Γ) {V} (k : W ⟶ V) :
    (⟨V, PUnit.unit, k⟩ : Tuple A.inner .t W) ∈ sem A η h p g ↔
      Holds A η (h ≫ k) p (A.push k g) := by
  unfold Holds Intension.True
  rw [sem_transport, Outer.map_rel, Intension.mem_map, Category.comp_id]

/-- Renaming is proved for the actual infinitary constructors, including binders. -/
theorem sem_rename {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) :
    ∀ {Γ σ} (p : ITerm Param Γ σ) {Δ W} (r : Ren Γ Δ) (h : A.W₀ ⟶ W)
      (g : IEnv (A.Dom W) Γ) (g' : IEnv (A.Dom W) Δ),
      (∀ {τ} (v : Var Γ τ), g'.get (r v) = g.get v) →
      sem A η h (p.rename r) g' = sem A η h p g := by
  intro Γ σ p
  induction p with
  | var v => intro Δ W r h g g' hg; exact congrArg (A.Incl _ W) (hg v)
  | param p => intros; rfl
  | app f a ihf iha =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ihf r h g g' hg, iha r h g g' hg]
  | top => intros; rfl
  | bot => intros; rfl
  | neg p ih =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ih r h g g' hg]
  | conj p q ihp ihq =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ihp r h g g' hg, ihq r h g g' hg]
  | disj p q ihp ihq =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ihp r h g g' hg, ihq r h g g' hg]
  | imp p q ihp ihq =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ihp r h g g' hg, ihq r h g g' hg]
  | iff p q ihp ihq =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ihp r h g g' hg, ihq r h g g' hg]
  | eq p q ihp ihq =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ihp r h g g' hg, ihq r h g g' hg]
  | boxOp => intros; rfl
  | all p ih =>
      intro Δ W r h g g' hg
      apply Set.ext
      intro z
      change (∀ x, Intension.True A.inner
        (sem A η (h ≫ z.2.2) (p.rename (Ren.lift r)) (.cons x (A.push z.2.2 g')))) ↔ _
      apply forall_congr'
      intro x
      apply Iff.of_eq
      apply congrArg (Intension.True A.inner)
      apply ih
      intro τ v
      cases v with
      | zero => rfl
      | succ v =>
          simp only [Ren.lift, IEnv.get, Premodel.push, IEnv.get_map]
          exact congrArg ((A.inner τ).map z.2.2) (hg v)
  | ex p ih =>
      intro Δ W r h g g' hg
      apply Set.ext
      intro z
      change (∃ x, Intension.True A.inner
        (sem A η (h ≫ z.2.2) (p.rename (Ren.lift r)) (.cons x (A.push z.2.2 g')))) ↔ _
      apply exists_congr
      intro x
      apply Iff.of_eq
      apply congrArg (Intension.True A.inner)
      apply ih
      intro τ v
      cases v with
      | zero => rfl
      | succ v =>
          simp only [Ren.lift, IEnv.get, Premodel.push, IEnv.get_map]
          exact congrArg ((A.inner τ).map z.2.2) (hg v)
  | iAnd I p ih =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ih _ r h g g' hg]
  | iOr I p ih =>
      intro Δ W r h g g' hg
      simp only [Term.rename, sem, ih _ r h g g' hg]

def argsEnv : (Γ : Ctx) → {V : C} → Args A.inner (RTy.ofArgs Γ) V → IEnv (A.Dom V) Γ
  | [], _, _ => .nil
  | _ :: Γ, _, xs => .cons xs.1 (argsEnv Γ xs.2)

def envArgs : (Γ : Ctx) → {V : C} → IEnv (A.Dom V) Γ → Args A.inner (RTy.ofArgs Γ) V
  | [], _, .nil => PUnit.unit
  | _ :: Γ, _, .cons x xs => (x, envArgs Γ xs)

theorem argsEnv_envArgs (Γ : Ctx) {V : C} (xs : IEnv (A.Dom V) Γ) :
    argsEnv A Γ (envArgs A Γ xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [argsEnv, envArgs, ih]

theorem envArgs_argsEnv (Γ : Ctx) {V : C} (xs : Args A.inner (RTy.ofArgs Γ) V) :
    envArgs A Γ (argsEnv A Γ xs) = xs := by
  induction Γ with
  | nil => cases xs; rfl
  | cons σ Γ ih => exact Prod.ext rfl (ih xs.2)

def envAppend {V : C} {Δ : Ctx} : {Γ : Ctx} →
    IEnv (A.Dom V) Γ → IEnv (A.Dom V) Δ → IEnv (A.Dom V) (Γ ++ Δ)
  | [], .nil, g => g
  | _ :: _, .cons x xs, g => .cons x (envAppend xs g)

theorem envAppend_embed {V : C} {Γ Δ : Ctx}
    (xs : IEnv (A.Dom V) Γ) (g : IEnv (A.Dom V) Δ) {σ} (v : Var Γ σ) :
    (envAppend A xs g).get (Ren.embed Γ Δ v) = xs.get v := by
  induction v with
  | zero => cases xs; rfl
  | succ v ih => cases xs with | cons x xs => exact ih xs

theorem envAppend_last (Γ : Ctx) {V : C} (xs : IEnv (A.Dom V) Γ)
    {σ} (R : A.Dom V σ) :
    (envAppend A xs (.cons R .nil)).get (lastVar Γ σ) = R := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

def applyEnv {W : C} : (Γ : Ctx) → Intension A.inner (RTy.ofArgs Γ) W →
    IEnv (A.Dom W) Γ → Intension A.inner .t W
  | [], F, .nil => F
  | _ :: Γ, F, .cons x xs => applyEnv Γ (Intension.app A.inner F x) xs

theorem true_applyEnv {W : C} (Γ : Ctx)
    (F : Intension A.inner (RTy.ofArgs Γ) W) (xs : IEnv (A.Dom W) Γ) :
    Intension.True A.inner (applyEnv A Γ F xs) ↔
      (⟨W, envArgs A Γ xs, 𝟙 W⟩ : Tuple A.inner (RTy.ofArgs Γ) W) ∈ F := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [applyEnv, ih]
      simp only [Intension.mem_app, Functor.map_id, types_id_apply, envArgs]

theorem sem_applyVars {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) (Γ : Ctx) :
    ∀ {Δ W} (h : A.W₀ ⟶ W) (F : ITerm Param Δ (RTy.ofArgs Γ))
      (ts : ∀ {σ}, Var Γ σ → ITerm Param Δ σ) (g : IEnv (A.Dom W) Δ)
      (xs : IEnv (A.Dom W) Γ),
      (∀ {σ} (v : Var Γ σ), sem A η h (ts v) g = A.Incl σ W (xs.get v)) →
      sem A η h (Term.applyVars Γ F ts) g = applyEnv A Γ (sem A η h F g) xs := by
  induction Γ with
  | nil => intro Δ W h F ts g xs hx; cases xs; rfl
  | cons σ Γ ih =>
      intro Δ W h F ts g xs hx
      cases xs with
      | cons x xs =>
          change sem A η h
            (Term.applyVars Γ (.app F (ts .zero)) (fun v => ts (.succ v))) g = _
          rw [ih h (.app F (ts .zero)) (fun v => ts (.succ v)) g xs
            (fun v => hx (.succ v))]
          simp only [sem, hx .zero, A.apply_Incl, applyEnv, IEnv.get]

theorem holds_iff {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    {Γ W} (h : A.W₀ ⟶ W) (p q : ITerm Param Γ Ty.t) (g : IEnv (A.Dom W) Γ) :
    Holds A η h (.iff p q) g ↔ (Holds A η h p g ↔ Holds A η h q g) := by
  classical
  simp only [Holds, sem, Intension.True, Set.mem_inter_iff, Set.mem_union,
    Set.mem_compl_iff]
  tauto

theorem holds_closeAll {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) (Γ : Ctx) :
    ∀ {Δ W} (h : A.W₀ ⟶ W) (p : ITerm Param (Γ ++ Δ) Ty.t)
      (g : IEnv (A.Dom W) Δ),
      Holds A η h (Term.closeAll Γ p) g ↔
        ∀ xs : IEnv (A.Dom W) Γ, Holds A η h p (envAppend A xs g) := by
  induction Γ with
  | nil =>
      intro Δ W h p g
      exact ⟨fun hp xs => by cases xs; exact hp, fun hp => hp .nil⟩
  | cons σ Γ ih =>
      intro Δ W h p g
      rw [Term.closeAll, ih]
      constructor
      · intro hp xs
        cases xs with
        | cons x xs => exact (holds_all A η h p _).1 (hp xs) x
      · intro hp xs
        exact (holds_all A η h p _).2 (fun x => hp (.cons x xs))

theorem holds_compBody {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    {Γ W} (h : A.W₀ ⟶ W) (p : ITerm Param Γ Ty.t)
    (R : A.Dom W (RTy.ofArgs Γ)) (xs : IEnv (A.Dom W) Γ) :
    Holds A η h p.compBody (envAppend A xs (.cons R .nil)) ↔
      ((⟨W, envArgs A Γ xs, 𝟙 W⟩ : Tuple A.inner (RTy.ofArgs Γ) W) ∈
        A.incl _ W R ↔ Holds A η h p xs) := by
  rw [Term.compBody, holds_iff]
  have hp := sem_rename A η p (Ren.embed Γ _) h xs
    (envAppend A xs (.cons R .nil)) (fun v => envAppend_embed A xs _ v)
  have hv (σ) (v : Var Γ σ) :
      sem A η h (.var (Ren.embed Γ _ v)) (envAppend A xs (.cons R .nil)) =
        A.Incl σ W (xs.get v) :=
    congrArg (A.Incl σ W) (envAppend_embed A xs _ v)
  have hr : sem A η h (.var (lastVar Γ _)) (envAppend A xs (.cons R .nil)) =
      A.incl _ W R := congrArg (A.Incl _ W) (envAppend_last A Γ xs R)
  unfold Holds
  rw [hp, sem_applyVars A η Γ h _ _ _ xs (fun v => hv _ v), hr, true_applyEnv]

/-- The complete outgoing-world profile of a matrix. -/
def formulaProfile {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    {Γ : Ctx} (p : ITerm Param Γ Ty.t) : Intension A.inner (RTy.ofArgs Γ) A.W₀ :=
  {z | Holds A η z.2.2 p (argsEnv A Γ z.2.1)}

/-- The semantic witness condition is obtained from the actual existential,
box and finite argument binders. This is not a full-support assumption. -/
theorem comprehension_profile_iff {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    (hc : Closed A) {Γ : Ctx} (p : ITerm Param Γ Ty.t) :
    Holds A η (𝟙 A.W₀) p.comprehension .nil ↔
      ∃ R : A.Dom A.W₀ (RTy.ofArgs Γ), A.incl _ A.W₀ R = formulaProfile A η p := by
  rw [Term.comprehension, holds_ex]
  constructor
  · rintro ⟨R, hR⟩
    have hb := (holds_box A η hc (𝟙 A.W₀) _ (.cons R .nil)).1 hR
    refine ⟨R, Set.ext ?_⟩
    rintro ⟨V, xs, k⟩
    have hh := (mem_sem_iff A η (𝟙 A.W₀)
      (Term.closeAll Γ p.compBody) (.cons R .nil) k).1 (hb ⟨V, PUnit.unit, k⟩)
    rw [Category.id_comp] at hh
    have hx := (holds_closeAll A η Γ k p.compBody _).1 hh (argsEnv A Γ xs)
    have hy := (holds_compBody A η k p ((A.inner _).map k R) (argsEnv A Γ xs)).1 hx
    simpa only [formulaProfile, Set.mem_setOf_eq, envArgs_argsEnv, A.incl_map,
      Intension.mem_map, Category.comp_id] using hy
  · rintro ⟨R, hR⟩
    refine ⟨R, (holds_box A η hc (𝟙 A.W₀) _ (.cons R .nil)).2 ?_⟩
    rintro ⟨V, ⟨⟩, k⟩
    apply (mem_sem_iff A η (𝟙 A.W₀)
      (Term.closeAll Γ p.compBody) (.cons R .nil) k).2
    rw [Category.id_comp]
    apply (holds_closeAll A η Γ k p.compBody _).2
    intro xs
    apply (holds_compBody A η k p ((A.inner _).map k R) xs).2
    have hh := Set.ext_iff.mp hR ⟨V, envArgs A Γ xs, k⟩
    simpa only [formulaProfile, Set.mem_setOf_eq, argsEnv_envArgs, A.incl_map,
      Intension.mem_map, Category.comp_id] using hh

theorem comprehension_profile {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    (hc : Closed A) (hcomp : Comprehension A) {Γ : Ctx} (p : ITerm Param Γ Ty.t) :
    ∃ R : A.Dom A.W₀ (RTy.ofArgs Γ), A.incl _ A.W₀ R = formulaProfile A η p :=
  (comprehension_profile_iff A η hc p).1 (hcomp η p)

noncomputable def representProfile (hc : Closed A) (hcomp : Comprehension A)
    {Γ : Ctx} (p : ITerm (A.Dom A.W₀) Γ Ty.t) : A.Dom A.W₀ (RTy.ofArgs Γ) :=
  Classical.choose (comprehension_profile A (Canonical.selfAssignment A) hc hcomp p)

theorem representProfile_spec (hc : Closed A) (hcomp : Comprehension A)
    {Γ : Ctx} (p : ITerm (A.Dom A.W₀) Γ Ty.t) :
    A.incl _ A.W₀ (representProfile A hc hcomp p) = formulaProfile A (Canonical.selfAssignment A) p :=
  Classical.choose_spec (comprehension_profile A (Canonical.selfAssignment A) hc hcomp p)

def relationMatrix (Γ : Ctx) (R : A.Dom A.W₀ (RTy.ofArgs Γ)) :
    ITerm (A.Dom A.W₀) Γ Ty.t :=
  Term.applyVars Γ (.param R) (fun v => .var v)

theorem profile_relationMatrix (Γ : Ctx) (R : A.Dom A.W₀ (RTy.ofArgs Γ)) :
    formulaProfile A (Canonical.selfAssignment A) (relationMatrix A Γ R) = A.incl _ A.W₀ R := by
  apply Set.ext
  rintro ⟨V, xs, k⟩
  change Holds A (Canonical.selfAssignment A) k
    (Term.applyVars Γ (.param R) (fun v => .var v)) (argsEnv A Γ xs) ↔ _
  unfold Holds
  rw [sem_applyVars A (Canonical.selfAssignment A) Γ k _ _ _ (argsEnv A Γ xs) (fun _ => rfl)]
  rw [true_applyEnv]
  simp only [sem, selfAssignment, Premodel.Incl_rel, A.incl_map, Intension.mem_map,
    envArgs_argsEnv, Category.comp_id]

/-- Actual closure under infinitary matrices, with no constant-domain input. -/
noncomputable def actionSupportFamily (hc : Closed A) (hcomp : Comprehension A)
    (Γ : Ctx) : SupportFamily (A.Dom A.W₀ (RTy.ofArgs Γ))
      (Tuple A.inner (RTy.ofArgs Γ) A.W₀) where
  holds R z := z ∈ A.incl _ A.W₀ R
  ext h := A.incl_injective _ A.W₀ (Set.ext h)
  bottom := representProfile A hc hcomp (.bot : ITerm (A.Dom A.W₀) Γ Ty.t)
  bottom_spec z := by
    rw [representProfile_spec]
    exact fun h => h
  neg R := representProfile A hc hcomp (.neg (relationMatrix A Γ R))
  neg_spec R z := by
    rw [representProfile_spec]
    change ¬ Holds A (Canonical.selfAssignment A) z.2.2 (relationMatrix A Γ R)
      (argsEnv A Γ z.2.1) ↔ _
    exact not_congr (Set.ext_iff.mp (profile_relationMatrix A Γ R) z)
  inf S := representProfile A hc hcomp
    (.iAnd {R : A.Dom A.W₀ (RTy.ofArgs Γ) // S R}
      (fun R => relationMatrix A Γ R.val))
  inf_spec S z := by
    rw [representProfile_spec]
    change (∀ R : {R : A.Dom A.W₀ (RTy.ofArgs Γ) // S R},
      Holds A (Canonical.selfAssignment A) z.2.2 (relationMatrix A Γ R.val)
        (argsEnv A Γ z.2.1)) ↔ _
    constructor
    · intro h R hR
      exact (Set.ext_iff.mp (profile_relationMatrix A Γ R) z).1 (h ⟨R, hR⟩)
    · intro h R
      exact (Set.ext_iff.mp (profile_relationMatrix A Γ R.val) z).2 (h R.val R.property)

/-- The carrier is atomic under inclusion of its full outgoing-tuple supports. -/
theorem action_atomicity (hc : Closed A) (hcomp : Comprehension A) (Γ : Ctx) :
    (actionSupportFamily A hc hcomp Γ).Atomic :=
  (actionSupportFamily A hc hcomp Γ).atomicity

theorem action_actuality (hc : Closed A) (hcomp : Comprehension A) (Γ : Ctx)
    (z : Tuple A.inner (RTy.ofArgs Γ) A.W₀) :
    (actionSupportFamily A hc hcomp Γ).ActualityAt z :=
  (actionSupportFamily A hc hcomp Γ).actuality z

theorem action_arbitrary_joins (hc : Closed A) (hcomp : Comprehension A) (Γ : Ctx)
    (S : A.Dom A.W₀ (RTy.ofArgs Γ) → Prop) :
    (∀ R, S R → (actionSupportFamily A hc hcomp Γ).Included R
      ((actionSupportFamily A hc hcomp Γ).sup S)) ∧
    (∀ T, (∀ R, S R → (actionSupportFamily A hc hcomp Γ).Included R T) →
      (actionSupportFamily A hc hcomp Γ).Included
        ((actionSupportFamily A hc hcomp Γ).sup S) T) :=
  (actionSupportFamily A hc hcomp Γ).arbitrary_join S

/-- A finite tuple equality matrix, whose ordinary parameters name root objects. -/
def namedTuple {Γ : Ctx} (xs : IEnv (A.Dom A.W₀) Γ) :
    ITerm (A.Dom A.W₀) Γ Ty.t :=
  .iAnd (Sigma (fun σ => Var Γ σ))
    (fun i => .eq (.var i.2) (.param (xs.get i.2)))

theorem holds_namedTuple {Γ W} (h : A.W₀ ⟶ W)
    (xs : IEnv (A.Dom A.W₀) Γ) (g : IEnv (A.Dom W) Γ) :
    Holds A (Canonical.selfAssignment A) h (namedTuple A xs) g ↔ g = A.push h xs := by
  change (∀ i : Sigma (fun σ => Var Γ σ),
    Outer.map A.inner i.1 (𝟙 W) (A.Incl i.1 W (g.get i.2)) =
      Outer.map A.inner i.1 (𝟙 W)
        (A.Incl i.1 W ((A.inner i.1).map h (xs.get i.2)))) ↔ _
  simp only [Outer.map_id]
  constructor
  · intro he
    apply IEnv.ext
    intro σ v
    simpa only [Premodel.push, IEnv.get_map] using
      A.Incl_injective σ W (he ⟨σ, v⟩)
  · intro he
    subst g
    intro i
    simp only [Premodel.push, IEnv.get_map]

theorem argsEnv_map (Γ : Ctx) {W V : C} (k : W ⟶ V)
    (xs : Args A.inner (RTy.ofArgs Γ) W) :
    argsEnv A Γ (Args.map A.inner (RTy.ofArgs Γ) k xs) =
      A.push k (argsEnv A Γ xs) := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
      simp only [argsEnv, Args.map, Premodel.push, IEnv.map, ih]

/-- A disjunction of root tuples in the current extension of R. -/
def rigidMatrix (Γ : Ctx) (R : A.Dom A.W₀ (RTy.ofArgs Γ)) :
    ITerm (A.Dom A.W₀) Γ Ty.t :=
  .iOr {xs : Args A.inner (RTy.ofArgs Γ) A.W₀ //
      (⟨A.W₀, xs, 𝟙 A.W₀⟩ : Tuple A.inner (RTy.ofArgs Γ) A.W₀) ∈ A.incl _ A.W₀ R}
    (fun xs => namedTuple A (argsEnv A Γ xs.val))

theorem profile_rigidMatrix (Γ : Ctx) (R : A.Dom A.W₀ (RTy.ofArgs Γ)) :
    formulaProfile A (Canonical.selfAssignment A) (rigidMatrix A Γ R) =
      {z | ∃ xs : Args A.inner (RTy.ofArgs Γ) A.W₀,
        (⟨A.W₀, xs, 𝟙 A.W₀⟩ : Tuple A.inner (RTy.ofArgs Γ) A.W₀) ∈ A.incl _ A.W₀ R ∧
          z.2.1 = Args.map A.inner (RTy.ofArgs Γ) z.2.2 xs} := by
  apply Set.ext
  rintro ⟨V, ys, k⟩
  change (∃ xs : {xs : Args A.inner (RTy.ofArgs Γ) A.W₀ //
      (⟨A.W₀, xs, 𝟙 A.W₀⟩ : Tuple A.inner (RTy.ofArgs Γ) A.W₀) ∈ A.incl _ A.W₀ R},
    Holds A (Canonical.selfAssignment A) k (namedTuple A (argsEnv A Γ xs.val)) (argsEnv A Γ ys)) ↔ _
  simp only [holds_namedTuple, ← argsEnv_map]
  constructor
  · rintro ⟨xs, hxs⟩
    refine ⟨xs.val, xs.property, ?_⟩
    simpa only [envArgs_argsEnv] using congrArg (envArgs A Γ) hxs
  · rintro ⟨xs, hx, hys⟩
    exact ⟨⟨xs, hx⟩, congrArg (argsEnv A Γ) hys⟩

/-- Every current relation has a represented rigid transport of its current
extension. The witness is actual Comprehension of `rigidMatrix`. -/
theorem action_rigid_representative (hc : Closed A) (hcomp : Comprehension A)
    (Γ : Ctx) (X : A.Dom A.W₀ (RTy.ofArgs Γ)) :
    ∃ Y : A.Dom A.W₀ (RTy.ofArgs Γ), A.incl _ A.W₀ Y =
      {z | ∃ xs : Args A.inner (RTy.ofArgs Γ) A.W₀,
        (⟨A.W₀, xs, 𝟙 A.W₀⟩ : Tuple A.inner (RTy.ofArgs Γ) A.W₀) ∈ A.incl _ A.W₀ X ∧
          z.2.1 = Args.map A.inner (RTy.ofArgs Γ) z.2.2 xs} := by
  obtain ⟨Y, hY⟩ := comprehension_profile A (Canonical.selfAssignment A) hc hcomp (rigidMatrix A Γ X)
  exact ⟨Y, hY.trans (profile_rigidMatrix A Γ X)⟩

theorem action_rigid_representatives (hc : Closed A) (hcomp : Comprehension A)
    (ρ : RTy) : ∀ X : A.Dom A.W₀ ρ,
    ∃ Y : A.Dom A.W₀ ρ, A.incl ρ A.W₀ Y =
      {z | ∃ xs : Args A.inner ρ A.W₀,
        (⟨A.W₀, xs, 𝟙 A.W₀⟩ : Tuple A.inner ρ A.W₀) ∈ A.incl ρ A.W₀ X ∧
          z.2.1 = Args.map A.inner ρ z.2.2 xs} := by
  exact Eq.mp (congrArg (fun τ : RTy => ∀ X : A.Dom A.W₀ τ,
    ∃ Y : A.Dom A.W₀ τ, A.incl τ A.W₀ Y =
      {z | ∃ xs : Args A.inner τ A.W₀,
        (⟨A.W₀, xs, 𝟙 A.W₀⟩ : Tuple A.inner τ A.W₀) ∈ A.incl τ A.W₀ X ∧
          z.2.1 = Args.map A.inner τ z.2.2 xs}) (RTy.ofArgs_args ρ))
    (action_rigid_representative A hc hcomp ρ.args)

theorem action_bottom_support (hc : Closed A) (hcomp : Comprehension A) (Γ : Ctx) :
    A.incl _ A.W₀ (actionSupportFamily A hc hcomp Γ).bottom = ∅ := by
  apply Set.ext
  intro z
  exact ⟨(actionSupportFamily A hc hcomp Γ).bottom_spec z, False.elim⟩

/-- Nonzero represented supports have minimal nonzero represented sub-supports.
The atom need not be a singleton of outgoing tuples. -/
theorem action_support_atom (hc : Closed A) (hcomp : Comprehension A) (Γ : Ctx)
    (X : A.Dom A.W₀ (RTy.ofArgs Γ)) (hX : A.incl _ A.W₀ X ≠ ∅) :
    ∃ Y : A.Dom A.W₀ (RTy.ofArgs Γ), A.incl _ A.W₀ Y ≠ ∅ ∧
      (∀ Z : A.Dom A.W₀ (RTy.ofArgs Γ), A.incl _ A.W₀ Z ⊆ A.incl _ A.W₀ Y →
        A.incl _ A.W₀ Z = ∅ ∨ A.incl _ A.W₀ Z = A.incl _ A.W₀ Y) ∧
      A.incl _ A.W₀ Y ⊆ A.incl _ A.W₀ X := by
  let F := actionSupportFamily A hc hcomp Γ
  have hx : X ≠ F.bottom := by
    intro hx
    exact hX ((congrArg (A.incl _ A.W₀) hx).trans (action_bottom_support A hc hcomp Γ))
  obtain ⟨Y, hy, hyx⟩ := F.atomicity X hx
  refine ⟨Y, ?_, ?_, hyx⟩
  · intro he
    apply hy.1
    apply A.incl_injective _ A.W₀
    exact he.trans (action_bottom_support A hc hcomp Γ).symm
  · intro Z hz
    cases hy.2 Z hz with
    | inl he =>
        exact Or.inl ((congrArg (A.incl _ A.W₀) he).trans (action_bottom_support A hc hcomp Γ))
    | inr he => exact Or.inr (congrArg (A.incl _ A.W₀) he)

theorem action_support_atoms (hc : Closed A) (hcomp : Comprehension A) (ρ : RTy) :
    ∀ X : A.Dom A.W₀ ρ, A.incl ρ A.W₀ X ≠ ∅ →
    ∃ Y : A.Dom A.W₀ ρ, A.incl ρ A.W₀ Y ≠ ∅ ∧
      (∀ Z : A.Dom A.W₀ ρ, A.incl ρ A.W₀ Z ⊆ A.incl ρ A.W₀ Y →
        A.incl ρ A.W₀ Z = ∅ ∨ A.incl ρ A.W₀ Z = A.incl ρ A.W₀ Y) ∧
      A.incl ρ A.W₀ Y ⊆ A.incl ρ A.W₀ X := by
  exact Eq.mp (congrArg (fun τ : RTy =>
    ∀ X : A.Dom A.W₀ τ, A.incl τ A.W₀ X ≠ ∅ →
    ∃ Y : A.Dom A.W₀ τ, A.incl τ A.W₀ Y ≠ ∅ ∧
      (∀ Z : A.Dom A.W₀ τ, A.incl τ A.W₀ Z ⊆ A.incl τ A.W₀ Y →
        A.incl τ A.W₀ Z = ∅ ∨ A.incl τ A.W₀ Z = A.incl τ A.W₀ Y) ∧
      A.incl τ A.W₀ Y ⊆ A.incl τ A.W₀ X) (RTy.ofArgs_args ρ))
    (action_support_atom A hc hcomp ρ.args)

/-- Actual truth of the repository's finite Atomicity instance at every
relational type, rather than only an auxiliary lattice predicate. -/
theorem action_holds_atomicity {B : Premodel Signature.pure C} (M : B.IsModel)
    (hc : Closed B) (hcomp : Comprehension B) (ρ : RTy) :
    B.HoldsSentence (Classicism.P.Atomicity.quoted ρ) := by
  classical
  change B.Holds (𝟙 B.W₀) (Classicism.P.Atomicity.quoted ρ) .nil
  simp only [Classicism.P.Atomicity.quoted, B.holds_forall M, B.holds_disj M,
    B.holds_exists M, B.holds_conj M, B.holds_neg M, B.holds_eq M,
    B.sem_orR M, Premodel.sem_negR M, Premodel.sem_var, IEnv.get]
  have e1 : ∀ S : Set (Tuple B.inner ρ B.W₀), Sᶜ = S ∪ Sᶜ ↔ S = ∅ := fun S => by
    rw [Set.union_compl_self, Set.compl_univ_iff]
  intro X
  by_cases hX : B.incl ρ B.W₀ X = ∅
  · exact Or.inl ((e1 _).2 hX)
  · right
    obtain ⟨Y, hY, hmin, hYX⟩ := action_support_atoms B hc hcomp ρ X hX
    have e2 (Z : B.Dom B.W₀ ρ) :
        (B.incl ρ B.W₀ Y = B.incl ρ B.W₀ Z ∪ B.incl ρ B.W₀ Y ∧
          ¬ B.incl ρ B.W₀ Z = B.incl ρ B.W₀ Y) ↔ B.incl ρ B.W₀ Z = ∅ := by
      constructor
      · rintro ⟨hle, hne⟩
        exact (hmin Z (Set.union_eq_right.1 hle.symm)).resolve_right hne
      · intro hz
        rw [hz]
        exact ⟨(Set.empty_union _).symm, fun he => hY he.symm⟩
    refine ⟨Y, fun Z => ?_, ?_⟩
    · rw [e1, e2]
      tauto
    · exact (Set.union_eq_right.2 hYX).symm

/-- Actual truth of Rigid Comprehension, using the explicit named-tuple
matrix in place of the full-model theorem's arbitrary-subset witness. -/
theorem action_holds_rigid_comprehension {B : Premodel Signature.pure C}
    (M : B.IsModel) (hc : Closed B) (hcomp : Comprehension B) (ρ : RTy) :
    B.HoldsSentence (Classicism.P.RigidComprehension.quoted ρ) := by
  change B.Holds (𝟙 B.W₀) (Classicism.P.RigidComprehension.quoted ρ) .nil
  simp only [Classicism.P.RigidComprehension.quoted, B.holds_forall M,
    B.holds_exists M, B.holds_conj M, B.holds_box M, B.holds_imp M,
    Premodel.holds_inclR M, Premodel.holds_coextR M, Premodel.sem_boxR M,
    Premodel.sem_var, IEnv.get, IEnv.get_map, B.incl_map, Intension.mem_map,
    Set.mem_ofPred_eq, Category.comp_id, Category.id_comp]
  intro X
  obtain ⟨Y, hY⟩ := action_rigid_representatives B hc hcomp ρ X
  refine ⟨Y, ⟨fun k x hx U k₁ => ?_, fun k Z hZ V₁ k₁ x hx => ?_⟩, fun x => ?_⟩
  · rw [hY] at hx ⊢
    obtain ⟨e, he, hxe⟩ := hx
    change x = Args.map B.inner ρ k e at hxe
    subst hxe
    exact ⟨e, he, (Args.map_comp _ ρ k k₁ e).symm⟩
  · rw [hY] at hx
    obtain ⟨e, he, hxe⟩ := hx
    change x = Args.map B.inner ρ (k ≫ k₁) e at hxe
    subst hxe
    have hh := hZ (Args.map B.inner ρ k e) (by rw [hY]; exact ⟨e, he, rfl⟩) V₁ k₁
    rwa [← Args.map_comp] at hh
  · rw [hY]
    constructor
    · intro hx
      exact ⟨x, hx, (Args.map_id _ ρ B.W₀ x).symm⟩
    · rintro ⟨e, he, hx⟩
      rw [show x = e from hx.trans (Args.map_id _ ρ B.W₀ e)]
      exact he

theorem action_holds_atomicity_schema {B : Premodel Signature.pure C}
    (M : B.IsModel) (hc : Closed B) (hcomp : Comprehension B) :
    B.HoldsAx Classicism.P.Atomicity.schema := by
  rintro _ ⟨ρ, _, rfl⟩
  exact action_holds_atomicity M hc hcomp ρ

theorem action_holds_rigid_comprehension_schema {B : Premodel Signature.pure C}
    (M : B.IsModel) (hc : Closed B) (hcomp : Comprehension B) :
    B.HoldsAx Classicism.P.RigidComprehension.schema := by
  rintro _ ⟨ρ, _, rfl⟩
  exact action_holds_rigid_comprehension M hc hcomp ρ

/-- At t, the infinitary term itself is already a proposition; no
higher-type Comprehension witness is required. -/
noncomputable def representProposition (hc : Closed A)
    (p : ITerm (A.Dom A.W₀) [] Ty.t) : A.Dom A.W₀ Ty.t :=
  Classical.choose (hc (Canonical.selfAssignment A) (𝟙 A.W₀) p .nil)

theorem representProposition_spec (hc : Closed A) (p : ITerm (A.Dom A.W₀) [] Ty.t) :
    A.incl .t A.W₀ (representProposition A hc p) =
      sem A (Canonical.selfAssignment A) (𝟙 A.W₀) p .nil :=
  Classical.choose_spec (hc (Canonical.selfAssignment A) (𝟙 A.W₀) p .nil)

theorem sem_self_parameter (p : A.Dom A.W₀ Ty.t) :
    sem A (Canonical.selfAssignment A) (𝟙 A.W₀) (.param p : ITerm (A.Dom A.W₀) [] Ty.t) .nil =
      A.incl .t A.W₀ p := by
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply] <;> rfl

/-- Propositional support closure follows from admitted infinitary terms alone. -/
noncomputable def propositionActionSupportFamily (hc : Closed A) :
    SupportFamily (A.Dom A.W₀ Ty.t) (Tuple A.inner .t A.W₀) where
  holds p z := z ∈ A.incl .t A.W₀ p
  ext h := A.incl_injective .t A.W₀ (Set.ext h)
  bottom := representProposition A hc .bot
  bottom_spec z := by
    rw [representProposition_spec]
    exact fun h => h
  neg p := representProposition A hc (.neg (.param p))
  neg_spec p z := by
    rw [representProposition_spec]
    change ¬ z ∈ sem A (Canonical.selfAssignment A) (𝟙 A.W₀)
      (.param p : ITerm (A.Dom A.W₀) [] Ty.t) .nil ↔ _
    rw [sem_self_parameter]
  inf S := representProposition A hc
    (.iAnd {p : A.Dom A.W₀ Ty.t // S p} (fun p => .param p.val))
  inf_spec S z := by
    rw [representProposition_spec]
    change (∀ p : {p : A.Dom A.W₀ Ty.t // S p},
      z ∈ sem A (Canonical.selfAssignment A) (𝟙 A.W₀)
        (.param p.val : ITerm (A.Dom A.W₀) [] Ty.t) .nil) ↔ _
    simp only [sem_self_parameter]
    exact ⟨fun h p hp => h ⟨p, hp⟩, fun h p => h p.val p.property⟩

theorem closed_proposition_atomicity (hc : Closed A) :
    (propositionActionSupportFamily A hc).Atomic :=
  (propositionActionSupportFamily A hc).atomicity

theorem closed_proposition_actuality (hc : Closed A) :
    (propositionActionSupportFamily A hc).ActualityAt ⟨A.W₀, PUnit.unit, 𝟙 A.W₀⟩ :=
  (propositionActionSupportFamily A hc).actuality _

#print axioms sem_transport
#print axioms sem_rename
#print axioms comprehension_profile_iff
#print axioms action_atomicity
#print axioms action_actuality
#print axioms action_arbitrary_joins
#print axioms action_rigid_representatives
#print axioms action_holds_atomicity
#print axioms action_holds_rigid_comprehension
#print axioms action_holds_atomicity_schema
#print axioms action_holds_rigid_comprehension_schema
#print axioms closed_proposition_atomicity
#print axioms closed_proposition_actuality

end Classicism.Research.InfinitaryComprehension.Canonical
