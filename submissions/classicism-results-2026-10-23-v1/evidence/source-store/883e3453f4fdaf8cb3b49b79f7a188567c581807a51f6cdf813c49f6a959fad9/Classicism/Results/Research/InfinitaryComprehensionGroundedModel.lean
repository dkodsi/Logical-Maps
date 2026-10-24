import Classicism.Results.Research.InfinitaryComprehensionLambdaFreeCanonical
import Classicism.Results.Research.InfinitaryComprehensionOriginalLanguage

/-!
# Grounding an actual action premodel

Source: the original closed-type scope of the Infinitary Comprehension note,
sections 1 and 4 (misc, original research, 23 October 2026). Auxiliary type
variables are interpreted as e by a concrete pullback of the given model.
Every relational inclusion is transported by an explicit argument-tuple
bijection. No closure, faithfulness, fullness or modal law is postulated by
this construction. Compilation remains paused.
-/

namespace Classicism.Research.InfinitaryComprehension.Canonical

open Classicism.Meta Classicism.Meta.Intensional CategoryTheory Grounding

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C)

abbrev groundInner : Classicism.Meta.Ty → C ⥤ Type := fun σ => A.inner (groundTy σ)

def groundArgs : (ρ : RTy) → {W : C} → Args ((Canonical.groundInner A)) ρ W →
    Args A.inner (groundRTy ρ) W
  | .t, _, _ => PUnit.unit
  | .arr _ ρ, _, xs => (xs.1, groundArgs ρ xs.2)

def ungroundArgs : (ρ : RTy) → {W : C} → Args A.inner (groundRTy ρ) W →
    Args ((Canonical.groundInner A)) ρ W
  | .t, _, _ => PUnit.unit
  | .arr _ ρ, _, xs => (xs.1, ungroundArgs ρ xs.2)

theorem ground_ungroundArgs : ∀ (ρ : RTy) {W : C}
    (xs : Args A.inner (groundRTy ρ) W),
    (Canonical.groundArgs A) ρ ((Canonical.ungroundArgs A) ρ xs) = xs
  | .t, _, xs => by cases xs; rfl
  | .arr _ ρ, _, xs => Prod.ext rfl (ground_ungroundArgs ρ xs.2)

theorem unground_groundArgs : ∀ (ρ : RTy) {W : C}
    (xs : Args (Canonical.groundInner A) ρ W),
    (Canonical.ungroundArgs A) ρ ((Canonical.groundArgs A) ρ xs) = xs
  | .t, _, xs => by cases xs; rfl
  | .arr _ ρ, _, xs => Prod.ext rfl (unground_groundArgs ρ xs.2)

theorem groundArgs_map : ∀ (ρ : RTy) {W V : C} (h : W ⟶ V)
    (xs : Args (Canonical.groundInner A) ρ W),
    (Canonical.groundArgs A) ρ (Args.map (Canonical.groundInner A) ρ h xs) =
      Args.map A.inner (groundRTy ρ) h ((Canonical.groundArgs A) ρ xs)
  | .t, _, _, _, _ => rfl
  | .arr _ ρ, _, _, h, xs => Prod.ext rfl (groundArgs_map ρ h xs.2)

/-- Pullback of an original intension along the actual tuple bijection. -/
def pullOuter : (σ : Classicism.Meta.Ty) → {W : C} → Outer A.inner (groundTy σ) W →
    Outer (Canonical.groundInner A) σ W
  | .e, _, x => x
  | .var _, _, x => x
  | .rel ρ, W, p =>
      {z : Tuple (Canonical.groundInner A) ρ W |
        (⟨z.1, (Canonical.groundArgs A) ρ z.2.1, z.2.2⟩ :
          Tuple A.inner (groundRTy ρ) W) ∈
            (show Intension A.inner (groundRTy ρ) W from p)}

theorem pullOuter_injective (σ : Classicism.Meta.Ty) {W : C} :
    Function.Injective ((Canonical.pullOuter A) σ (W := W)) := by
  cases σ with
  | e => exact fun _ _ h => h
  | var _ => exact fun _ _ h => h
  | rel ρ =>
      intro p q h
      change @Eq (Intension A.inner (groundRTy ρ) W) p q
      apply Set.ext
      rintro ⟨V, xs, k⟩
      have hh := Set.ext_iff.mp h ⟨V, (Canonical.ungroundArgs A) ρ xs, k⟩
      simpa only [pullOuter, Set.mem_setOf_eq, (Canonical.ground_ungroundArgs A)] using hh

theorem pullOuter_map (σ : Classicism.Meta.Ty) {W V : C} (h : W ⟶ V)
    (p : Outer A.inner (groundTy σ) W) :
    (Canonical.pullOuter A) σ (Outer.map A.inner (groundTy σ) h p) =
      Outer.map (Canonical.groundInner A) σ h ((Canonical.pullOuter A) σ p) := by
  cases σ <;> rfl

/-- The pure signature is enough: all designated parameters are still retained
as actual assigned objects. No source constants are identified. -/
def groundedPremodel : Premodel Signature.pure C where
  W₀ := A.W₀
  inner := (Canonical.groundInner A)
  nonempty_e := A.nonempty_e
  incl ρ W x := (Canonical.pullOuter A) (.rel ρ) (A.incl (groundRTy ρ) W x)
  incl_map := by
    intro ρ W V h x
    change (Canonical.pullOuter A) (.rel ρ)
        (A.incl (groundRTy ρ) V ((A.inner (.rel (groundRTy ρ))).map h x)) =
      Intension.map (Canonical.groundInner A) h
        ((Canonical.pullOuter A) (.rel ρ) (A.incl (groundRTy ρ) W x))
    exact (congrArg ((Canonical.pullOuter A) (.rel ρ))
      (A.incl_map (groundRTy ρ) (W := W) (V := V) h x)).trans
        ((Canonical.pullOuter_map A) (.rel ρ) h (A.incl (groundRTy ρ) W x))
  incl_injective ρ W := ((Canonical.pullOuter_injective A) (.rel ρ)).comp
    (A.incl_injective (groundRTy ρ) W)
  I c := nomatch c

theorem grounded_Incl (σ : Classicism.Meta.Ty) {W : C} (a : (Canonical.groundedPremodel A).Dom W σ) :
    (Canonical.groundedPremodel A).Incl σ W a = (Canonical.pullOuter A) σ (A.Incl (groundTy σ) W a) := by
  cases σ <;> rfl

theorem grounded_apply {σ : Classicism.Meta.Ty} {ρ : RTy} {W : C}
    (F : Intension A.inner (groundTy σ ⇒ groundRTy ρ) W)
    (a : Outer A.inner (groundTy σ) W) :
    (Canonical.groundedPremodel A).apply ((Canonical.pullOuter A) (σ ⇒ ρ) F) ((Canonical.pullOuter A) σ a) =
      (Canonical.pullOuter A) ρ (A.apply F a) := by
  ext ⟨V, xs, h⟩
  change (∃ x : A.Dom V (groundTy σ),
    (Canonical.groundedPremodel A).Incl σ V x =
      Outer.map (Canonical.groundInner A) σ h ((Canonical.pullOuter A) σ a) ∧
    (⟨V, (x, (Canonical.groundArgs A) ρ xs), h⟩ :
      Tuple A.inner (groundTy σ ⇒ groundRTy ρ) W) ∈ F) ↔
    ∃ x : A.Dom V (groundTy σ),
      A.Incl (groundTy σ) V x = Outer.map A.inner (groundTy σ) h a ∧
      (⟨V, (x, (Canonical.groundArgs A) ρ xs), h⟩ :
        Tuple A.inner (groundTy σ ⇒ groundRTy ρ) W) ∈ F
  apply exists_congr
  intro x
  exact and_congr
    ((Iff.of_eq (congrArg₂ (fun u v : Outer (Canonical.groundInner A) σ V => u = v)
      ((Canonical.grounded_Incl A) σ x)
      ((Canonical.pullOuter_map A) σ h a).symm)).trans
        ((Canonical.pullOuter_injective A) σ).eq_iff) Iff.rfl

theorem grounded_boxRead (W : C) :
    (Canonical.groundedPremodel A).boxRead .t W = (Canonical.pullOuter A) (RTy.t ⇒ RTy.t) (A.boxRead .t W) := by
  ext ⟨V, ⟨p, ⟨⟩⟩, h⟩
  rfl

theorem grounded_true {W : C} (p : Intension A.inner .t W) :
    Intension.True (Canonical.groundedPremodel A).inner ((Canonical.pullOuter A) Ty.t p) ↔
      Intension.True A.inner p := Iff.rfl

theorem groundEnv_push {Γ : Ctx} {W V : C} (h : W ⟶ V)
    (g : IEnv ((Canonical.groundedPremodel A).Dom W) Γ) :
    Grounding.groundEnv ((Canonical.groundedPremodel A).push h g) =
      A.push h (Grounding.groundEnv g) := by
  induction g with
  | nil => rfl
  | cons x xs ih => exact congrArg (IEnv.cons ((A.inner _).map h x)) ih

/-- Exact recursive semantic compatibility with actual type grounding. -/
theorem grounded_sem {Param : Classicism.Meta.Ty → Type} (η : Assignment (Canonical.groundedPremodel A) Param) :
    ∀ {Γ σ W} (h : A.W₀ ⟶ W) (p : ITerm Param Γ σ)
      (g : IEnv ((Canonical.groundedPremodel A).Dom W) Γ),
      sem (Canonical.groundedPremodel A) η h p g = (Canonical.pullOuter A) σ
        (sem A (Canonical.selfAssignment A) h (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p) (Grounding.groundEnv g))
  | _, σ, W, _, .var v, g => by
      change (Canonical.groundedPremodel A).Incl σ W (g.get v) =
        (Canonical.pullOuter A) σ (A.Incl (groundTy σ) W
          ((Grounding.groundEnv g).get (groundVar v)))
      exact ((Canonical.grounded_Incl A) σ (g.get v)).trans
        (congrArg (fun x => (Canonical.pullOuter A) σ (A.Incl (groundTy σ) W x))
          (Grounding.groundEnv_get (D := A.Dom W) g v).symm)
  | _, σ, W, h, .param p, _ =>
      (Canonical.grounded_Incl A) σ ((A.inner (groundTy σ)).map h (η (σ := σ) p))
  | _, _, W, h, .app (σ := τ) (ρ := ρ) f a, g => by
      exact (congrArg₂
        (fun (F : Intension (Canonical.groundInner A) (τ ⇒ ρ) W)
          (x : Outer (Canonical.groundInner A) τ W) => (Canonical.groundedPremodel A).apply F x)
        (grounded_sem η h f g) (grounded_sem η h a g)).trans
          ((Canonical.grounded_apply A) _ _)
  | _, _, _, _, .top, _ => rfl
  | _, _, _, _, .bot, _ => rfl
  | _, _, W, h, .neg p, g =>
      congrArg (fun P : Intension (Canonical.groundInner A) .t W => Pᶜ)
        (grounded_sem η h p g)
  | _, _, W, h, .conj p q, g =>
      congrArg₂ (fun P Q : Intension (Canonical.groundInner A) .t W => P ∩ Q)
        (grounded_sem η h p g) (grounded_sem η h q g)
  | _, _, W, h, .disj p q, g =>
      congrArg₂ (fun P Q : Intension (Canonical.groundInner A) .t W => P ∪ Q)
        (grounded_sem η h p g) (grounded_sem η h q g)
  | _, _, W, h, .imp p q, g =>
      congrArg₂ (fun P Q : Intension (Canonical.groundInner A) .t W => Pᶜ ∪ Q)
        (grounded_sem η h p g) (grounded_sem η h q g)
  | _, _, W, h, .iff p q, g =>
      congrArg₂ (fun P Q : Intension (Canonical.groundInner A) .t W => (Pᶜ ∪ Q) ∩ (Qᶜ ∪ P))
        (grounded_sem η h p g) (grounded_sem η h q g)
  | _, _, _, h, .eq (σ := σ) a b, g => by
      simp only [sem, groundTerm, grounded_sem η h a g, grounded_sem η h b g]
      ext z
      change (Outer.map (Canonical.groundInner A) σ z.2.2 ((Canonical.pullOuter A) σ _) =
        Outer.map (Canonical.groundInner A) σ z.2.2 ((Canonical.pullOuter A) σ _)) ↔ _
      rw [← (Canonical.pullOuter_map A), ← (Canonical.pullOuter_map A)]
      exact ((Canonical.pullOuter_injective A) σ).eq_iff
  | _, _, W, _, .boxOp, _ => (Canonical.grounded_boxRead A) W
  | Γ, _, W, h, .all (σ := τ) p, g => by
      ext ⟨V, ⟨⟩, k⟩
      change (∀ x : A.Dom V (groundTy τ), Intension.True (Canonical.groundedPremodel A).inner
        (sem (Canonical.groundedPremodel A) η (h ≫ k) p
          (.cons x ((Canonical.groundedPremodel A).push k g)))) ↔
        (∀ x : A.Dom V (groundTy τ), Intension.True A.inner
          (sem A (Canonical.selfAssignment A) (h ≫ k)
            (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
            (.cons x (A.push k (Grounding.groundEnv g)))))
      apply forall_congr'
      intro x
      have hs := grounded_sem η (h ≫ k) p
        (@IEnv.cons ((Canonical.groundedPremodel A).Dom V) _ _ x
          ((Canonical.groundedPremodel A).push k g))
      have ht := (Iff.of_eq (congrArg (Intension.True (Canonical.groundedPremodel A).inner) hs)).trans
        ((Canonical.grounded_true A) _)
      have he : @Eq (IEnv (A.Dom V) (groundCtx (τ :: Γ)))
          (Grounding.groundEnv (D := A.Dom V)
            (@IEnv.cons ((Canonical.groundedPremodel A).Dom V) Γ τ x
              ((Canonical.groundedPremodel A).push k g)))
          (@IEnv.cons (A.Dom V) (groundCtx Γ) (groundTy τ) x
            (A.push k (Grounding.groundEnv (D := A.Dom W) g))) :=
        congrArg (fun ys : IEnv (A.Dom V) (groundCtx Γ) =>
          @IEnv.cons (A.Dom V) (groundCtx Γ) (groundTy τ) x ys)
            ((Canonical.groundEnv_push A) k g)
      exact ht.trans (Iff.of_eq (congrArg
        (fun env : IEnv (A.Dom V) (groundCtx (τ :: Γ)) => Intension.True A.inner
          (sem A (Canonical.selfAssignment A) (h ≫ k)
            (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p) env)) he))
  | Γ, _, W, h, .ex (σ := τ) p, g => by
      ext ⟨V, ⟨⟩, k⟩
      change (∃ x : A.Dom V (groundTy τ), Intension.True (Canonical.groundedPremodel A).inner
        (sem (Canonical.groundedPremodel A) η (h ≫ k) p
          (.cons x ((Canonical.groundedPremodel A).push k g)))) ↔
        (∃ x : A.Dom V (groundTy τ), Intension.True A.inner
          (sem A (Canonical.selfAssignment A) (h ≫ k)
            (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
            (.cons x (A.push k (Grounding.groundEnv g)))))
      apply exists_congr
      intro x
      have hs := grounded_sem η (h ≫ k) p
        (@IEnv.cons ((Canonical.groundedPremodel A).Dom V) _ _ x
          ((Canonical.groundedPremodel A).push k g))
      have ht := (Iff.of_eq (congrArg (Intension.True (Canonical.groundedPremodel A).inner) hs)).trans
        ((Canonical.grounded_true A) _)
      have he : @Eq (IEnv (A.Dom V) (groundCtx (τ :: Γ)))
          (Grounding.groundEnv (D := A.Dom V)
            (@IEnv.cons ((Canonical.groundedPremodel A).Dom V) Γ τ x
              ((Canonical.groundedPremodel A).push k g)))
          (@IEnv.cons (A.Dom V) (groundCtx Γ) (groundTy τ) x
            (A.push k (Grounding.groundEnv (D := A.Dom W) g))) :=
        congrArg (fun ys : IEnv (A.Dom V) (groundCtx Γ) =>
          @IEnv.cons (A.Dom V) (groundCtx Γ) (groundTy τ) x ys)
            ((Canonical.groundEnv_push A) k g)
      exact ht.trans (Iff.of_eq (congrArg
        (fun env : IEnv (A.Dom V) (groundCtx (τ :: Γ)) => Intension.True A.inner
          (sem A (Canonical.selfAssignment A) (h ≫ k)
            (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p) env)) he))
  | _, _, W, h, .iAnd I p, g => by
      ext ⟨V, ⟨⟩, k⟩
      change (∀ i : I, (⟨V, PUnit.unit, k⟩ : Tuple (Canonical.groundInner A) .t W) ∈
        sem (Canonical.groundedPremodel A) η h (p i) g) ↔
        (∀ i : I, (⟨V, PUnit.unit, k⟩ : Tuple A.inner .t W) ∈
          (show Intension A.inner .t W from sem A (Canonical.selfAssignment A) h
            (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η (p i)) (Grounding.groundEnv g)))
      apply forall_congr'
      intro i
      exact Iff.of_eq (congrArg
        (fun F : Intension (Canonical.groundInner A) .t W =>
          (⟨V, PUnit.unit, k⟩ : Tuple (Canonical.groundInner A) .t W) ∈ F)
        (grounded_sem η h (p i) g))
  | _, _, W, h, .iOr I p, g => by
      ext ⟨V, ⟨⟩, k⟩
      change (∃ i : I, (⟨V, PUnit.unit, k⟩ : Tuple (Canonical.groundInner A) .t W) ∈
        sem (Canonical.groundedPremodel A) η h (p i) g) ↔
        (∃ i : I, (⟨V, PUnit.unit, k⟩ : Tuple A.inner .t W) ∈
          (show Intension A.inner .t W from sem A (Canonical.selfAssignment A) h
            (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η (p i)) (Grounding.groundEnv g)))
      apply exists_congr
      intro i
      exact Iff.of_eq (congrArg
        (fun F : Intension (Canonical.groundInner A) .t W =>
          (⟨V, PUnit.unit, k⟩ : Tuple (Canonical.groundInner A) .t W) ∈ F)
        (grounded_sem η h (p i) g))


/-- Truth of every actual infinitary formula is preserved by grounding. -/
theorem grounded_holds {Param : Classicism.Meta.Ty → Type}
    (η : Assignment (Canonical.groundedPremodel A) Param) {Γ W} (h : A.W₀ ⟶ W)
    (p : ITerm Param Γ Ty.t) (g : IEnv ((Canonical.groundedPremodel A).Dom W) Γ) :
    Holds (Canonical.groundedPremodel A) η h p g ↔
      Holds A (Canonical.selfAssignment A) h (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p) (Grounding.groundEnv g) := by
  unfold Holds
  rw [(Canonical.grounded_sem A)]
  exact (Canonical.grounded_true A) _

/-- Original closed-type formation alone supplies full datatype closure of the
concrete grounding extension. No original Ty.var carrier is used. -/
theorem grounded_closed (hc : GroundClosed A) : Closed (Canonical.groundedPremodel A) := by
  intro Param η Γ σ W h p g
  obtain ⟨a, ha⟩ := hc (Canonical.selfAssignment A) h (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p) (Grounding.groundEnv g)
    (Formation.ground_context_closed Γ) (Formation.groundTerm_formed (Param := Param) (Param' := A.Dom A.W₀) η p)
  refine ⟨a, ?_⟩
  exact ((Canonical.grounded_Incl A) σ a).trans
    ((congrArg ((Canonical.pullOuter A) σ) ha).trans
      ((Canonical.grounded_sem A) η h p g).symm)

private theorem prod_heq {α β γ : Type} (x : α) {y : β} {z : γ} (h : HEq y z) :
    HEq (x, y) (x, z) := by
  cases h
  rfl

/-- Grounding a tuple and grounding its environment are the same operation,
up to the one explicit ofArgs type equality. -/
theorem groundArgs_env : ∀ (Γ : Ctx) {W : C}
    (xs : Args (Canonical.groundInner A) (RTy.ofArgs Γ) W),
    HEq ((Canonical.groundArgs A) (RTy.ofArgs Γ) xs)
      (envArgs A (groundCtx Γ)
        (Grounding.groundEnv (argsEnv (Canonical.groundedPremodel A) Γ xs)))
  | [], _, xs => by cases xs; rfl
  | _ :: Γ, _, xs => prod_heq xs.1 (groundArgs_env Γ xs.2)

private theorem incl_mem_heq {ρ τ : RTy} (e : ρ = τ) {W V : C}
    (R : A.Dom W ρ) (S : A.Dom W τ) (hRS : HEq R S)
    (xs : Args A.inner ρ V) (ys : Args A.inner τ V) (hxy : HEq xs ys) (k : W ⟶ V) :
    ((⟨V, xs, k⟩ : Tuple A.inner ρ W) ∈ A.incl ρ W R) ↔
      ((⟨V, ys, k⟩ : Tuple A.inner τ W) ∈ A.incl τ W S) := by
  cases e
  cases hRS
  cases hxy
  rfl

private def retypeRootRelation {ρ τ : RTy} (e : ρ = τ) (R : A.Dom A.W₀ ρ) :
    A.Dom A.W₀ τ := congrArg Ty.rel e ▸ R

private theorem retypeRootRelation_heq {ρ τ : RTy} (e : ρ = τ)
    (R : A.Dom A.W₀ ρ) : HEq (retypeRootRelation A e R) R := by
  cases e
  rfl

/-- Actual original-language Comprehension supplies all instances in the
auxiliary grounding extension. Its witnesses are taken from the original
formula's proved profile clause; no fullness assumption occurs. -/
theorem grounded_comprehension (hc : GroundClosed A) (hcomp : GroundComp A) :
    Comprehension (Canonical.groundedPremodel A) := by
  intro Param η Γ p
  apply (comprehension_profile_iff (Canonical.groundedPremodel A) η ((Canonical.grounded_closed A) hc) p).2
  obtain ⟨S, hS⟩ := ground_comprehension_profile A (Canonical.selfAssignment A) hc hcomp
    (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p) (Formation.ground_context_closed Γ) (Formation.groundTerm_formed (Param := Param) (Param' := A.Dom A.W₀) η p)
  let e := groundRTy_ofArgs Γ
  let R := retypeRootRelation A e.symm S
  refine ⟨R, Set.ext ?_⟩
  rintro ⟨V, xs, k⟩
  change ((⟨V, (Canonical.groundArgs A) (RTy.ofArgs Γ) xs, k⟩ :
    Tuple A.inner (groundRTy (RTy.ofArgs Γ)) A.W₀) ∈ A.incl _ A.W₀ R) ↔ _
  rw [incl_mem_heq A e R S (retypeRootRelation_heq A e.symm S)
    ((Canonical.groundArgs A) (RTy.ofArgs Γ) xs)
    (envArgs A (groundCtx Γ) (Grounding.groundEnv (argsEnv (Canonical.groundedPremodel A) Γ xs)))
    ((Canonical.groundArgs_env A) Γ xs) k, hS]
  change Holds A (Canonical.selfAssignment A) k (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
    (argsEnv A (groundCtx Γ) (envArgs A (groundCtx Γ)
      (Grounding.groundEnv (argsEnv (Canonical.groundedPremodel A) Γ xs)))) ↔
    Holds (Canonical.groundedPremodel A) η k p (argsEnv (Canonical.groundedPremodel A) Γ xs)
  rw [argsEnv_envArgs]
  exact ((Canonical.grounded_holds A) η k p _).symm

/-- The boxed ND_t sentence has only closed types. Its grounding is literally
itself, so the original lambda-free C5 premise transfers without finite C. -/
theorem grounded_c5 (hC5 : LambdaFreeC5 A) : LambdaFreeC5 (Canonical.groundedPremodel A) := by
  apply ((Canonical.grounded_holds A) (Canonical.selfAssignment (Canonical.groundedPremodel A)) (𝟙 A.W₀)
    ((Canonical.ndFormula (Canonical.groundedPremodel A)) Ty.t).box .nil).2
  exact hC5

/-- Both original-language premises and the exact C5 sentence now hold in the
concrete extension, with no assumed extension or representation theorem. -/
theorem grounded_original_package (hc : GroundClosed A) (hcomp : GroundComp A)
    (hC5 : LambdaFreeC5 A) :
    Closed (Canonical.groundedPremodel A) ∧ Comprehension (Canonical.groundedPremodel A) ∧
      LambdaFreeC5 (Canonical.groundedPremodel A) :=
  ⟨(Canonical.grounded_closed A) hc, (Canonical.grounded_comprehension A) hc hcomp, (Canonical.grounded_c5 A) hC5⟩

/-- On every original closed object type, grounding retains its exact carrier. -/
theorem grounded_rootDom_closed (σ : Classicism.Meta.Ty) (hσ : σ.Closed) :
    (Canonical.groundedPremodel A).Dom (Canonical.groundedPremodel A).W₀ (groundTy σ) = A.Dom A.W₀ σ := by
  change A.Dom A.W₀ (groundTy (groundTy σ)) = A.Dom A.W₀ σ
  rw [groundTy_eq_of_closed σ hσ, groundTy_eq_of_closed σ hσ]

end Classicism.Research.InfinitaryComprehension.Canonical
