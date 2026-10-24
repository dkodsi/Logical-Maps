import Classicism.Results.Research.InfinitaryComprehensionSupport
import Classicism.Semantics.IntensionalFacts
import Classicism.Results.Research.InfinitaryComprehensionC5Bridge
import Classicism.Results.Research.InfinitaryComprehensionGrounding

/-!
# Infinitary syntax in actual intensional action models

Source: `research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md`,
sections 2--4 (misc, original research, 23 October 2026).

This layer starts with the existing `Intensional.Premodel`, including its
possibly changing domains and noninvertible arrows. The infinitary interpretation
below is recursion on the actual `InfinitaryComprehension.Term` constructors.
`Closed` is closure of that interpretation; `Comprehension` is satisfaction of
the actual object-language comprehension formula. Neither condition assumes a
constant-domain, faithful root-application, atom-world, or full-support model.

The native C5 premise is used only at CLOSED original types. The canonical
carrier at an auxiliary type-variable code is obtained by explicit grounding
to e; no ND or BF instance at the input model's arbitrary Ty.var carrier is
inferred. `Closed` and `Comprehension` below describe an infinitary expansion
on the displayed full syntactic datatype. The separate `InfinitaryComprehensionGroundedModel` module constructs their
extension from original closed-type formation and Comprehension, with an
actual recursive semantic compatibility theorem.

The final actual-Comprehension transport and full-support assembly live in
`InfinitaryComprehensionRepresentation`, avoiding a dependency cycle with the
independent variable-domain comprehension-profile derivation.

All mathematics in this file is model theory in Lean's classical metatheory.
It is not a shallow proof in C, and has not been compiled at this checkpoint.
-/

namespace Classicism.Research.InfinitaryComprehension.Canonical

universe u

set_option pp.maxSteps 100

open Classicism.Meta
open Classicism.Meta.Intensional
open CategoryTheory

variable {Sig : Signature} {C : Type} [SmallCategory C]

abbrev ITerm := Classicism.Research.InfinitaryComprehension.Term

/-- Parameters are assigned at the root and transported by the original action. -/
abbrev Assignment (A : Premodel Sig C) (Param : Classicism.Meta.Ty → Type) :=
  ∀ {σ}, Param σ → A.Dom A.W₀ σ

/-- The genuine infinitary outer semantics. Quantifiers use the domain at the
evaluation point, not the root domain. -/
def sem (A : Premodel Sig C) {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) :
    ∀ {Γ : Ctx} {σ : Classicism.Meta.Ty} {W : C}, (A.W₀ ⟶ W) → ITerm Param Γ σ →
      IEnv (A.Dom W) Γ → Outer A.inner σ W
  | _, _, W, _, .var v, g => A.Incl _ W (g.get v)
  | _, _, W, h, .param p, _ => A.Incl _ W ((A.inner _).map h (η p))
  | _, _, _, h, .app f a, g => A.apply (sem A η h f g) (sem A η h a g)
  | _, _, _, _, .top, _ => Set.univ
  | _, _, _, _, .bot, _ => ∅
  | _, _, _, h, .neg p, g => (sem A η h p g)ᶜ
  | _, _, _, h, .conj p q, g => sem A η h p g ∩ sem A η h q g
  | _, _, _, h, .disj p q, g => sem A η h p g ∪ sem A η h q g
  | _, _, _, h, .imp p q, g => (sem A η h p g)ᶜ ∪ sem A η h q g
  | _, _, _, h, .iff p q, g =>
      ((sem A η h p g)ᶜ ∪ sem A η h q g) ∩
        ((sem A η h q g)ᶜ ∪ sem A η h p g)
  | _, _, W, h, .eq (σ := σ) a b, g =>
      {p : Tuple A.inner .t W |
        Outer.map A.inner σ p.2.2 (sem A η h a g) =
          Outer.map A.inner σ p.2.2 (sem A η h b g)}
  | _, _, W, _, .boxOp, _ => A.boxRead .t W
  | _, _, W, h, .all (σ := σ) p, g =>
      {z : Tuple A.inner .t W | ∀ x : A.Dom z.1 σ,
        Intension.True A.inner (sem A η (h ≫ z.2.2) p (.cons x (A.push z.2.2 g)))}
  | _, _, W, h, .ex (σ := σ) p, g =>
      {z : Tuple A.inner .t W | ∃ x : A.Dom z.1 σ,
        Intension.True A.inner (sem A η (h ≫ z.2.2) p (.cons x (A.push z.2.2 g)))}
  | _, _, _, h, .iAnd I p, g => {z | ∀ i : I, z ∈ sem A η h (p i) g}
  | _, _, _, h, .iOr I p, g => {z | ∃ i : I, z ∈ sem A η h (p i) g}

def Holds (A : Premodel Sig C) {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (p : ITerm Param Γ Ty.t)
    (g : IEnv (A.Dom W) Γ) : Prop :=
  Intension.True A.inner (sem A η h p g)

/-- Formula/term formation is interpreted in the admitted domains. -/
def Closed (A : Premodel Sig C) : Prop :=
  ∀ {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) {Γ σ W}
    (h : A.W₀ ⟶ W) (p : ITerm Param Γ σ) (g : IEnv (A.Dom W) Γ),
      ∃ a : A.Dom W σ, A.Incl σ W a = sem A η h p g

set_option allowUnsafeReducibility true in
attribute [local reducible] Closed

/-- The actual schema, under every simultaneous root assignment of parameters. -/
def Comprehension (A : Premodel Sig C) : Prop :=
  ∀ {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) {Γ}
    (p : ITerm Param Γ Ty.t), Holds A η (𝟙 A.W₀) p.comprehension .nil

variable (A : Premodel Sig C)

/-- Naturality of the actual infinitary interpretation, including its binders.
No Barcan, rigidity, or domain-surjectivity premise is used here. -/
theorem sem_push {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) :
    ∀ {Γ σ W} (h : A.W₀ ⟶ W) (p : ITerm Param Γ σ)
      (g : IEnv (A.Dom W) Γ) {V} (k : W ⟶ V),
      sem A η (h ≫ k) p (A.push k g) =
        Outer.map A.inner σ k (sem A η h p g)
  | _, _, _, _, .var v, g, _, k => by
      simpa only [sem, Premodel.push, IEnv.get_map] using
        A.Incl_map _ k (g.get v)
  | _, σ, _, h, .param p, _, _, k => by
      change A.Incl σ _ ((A.inner σ).map (h ≫ k) (η p)) =
        Outer.map A.inner σ k (A.Incl σ _ ((A.inner σ).map h (η p)))
      rw [← A.Incl_map, Functor.map_comp]
      rfl
  | _, _, _, h, .app f a, g, _, k => by
      simp only [sem, sem_push η h f g k, sem_push η h a g k]
      exact A.apply_map k _ _
  | _, _, _, _, .top, _, _, _ => rfl
  | _, _, _, _, .bot, _, _, _ => rfl
  | _, _, _, h, .neg p, g, _, k => by
      rw [sem, sem_push η h p g k]; rfl
  | _, _, _, h, .conj p q, g, _, k => by
      rw [sem, sem_push η h p g k, sem_push η h q g k]; rfl
  | _, _, _, h, .disj p q, g, _, k => by
      rw [sem, sem_push η h p g k, sem_push η h q g k]; rfl
  | _, _, _, h, .imp p q, g, _, k => by
      rw [sem, sem_push η h p g k, sem_push η h q g k]; rfl
  | _, _, _, h, .iff p q, g, _, k => by
      rw [sem, sem_push η h p g k, sem_push η h q g k]; rfl
  | _, _, _, h, .eq a b, g, _, k => by
      simp only [sem, sem_push η h a g k, sem_push η h b g k]
      ext z
      simp only [Outer.map_rel, Intension.map, Set.mem_setOf_eq,
        Outer.map_comp]
  | _, _, _, _, .boxOp, _, _, _ => rfl
  | _, _, _, h, .all p, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.map, Set.mem_setOf_eq,
        Category.assoc, A.push_push]
  | _, _, _, h, .ex p, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.map, Set.mem_setOf_eq,
        Category.assoc, A.push_push]
  | _, _, _, h, .iAnd I p, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.map, Set.mem_setOf_eq,
        sem_push η h (p _) g k]
  | _, _, _, h, .iOr I p, g, _, k => by
      ext z
      simp only [sem, Outer.map_rel, Intension.map, Set.mem_setOf_eq,
        sem_push η h (p _) g k]

/-- Choosing an admitted denotation uses metatheoretic choice only. -/
noncomputable def value (hc : Closed A) {Param : Classicism.Meta.Ty → Type}
    (η : Assignment A Param) {Γ σ} (p : ITerm Param Γ σ)
    (g : IEnv (A.Dom A.W₀) Γ) : A.Dom A.W₀ σ :=
  Classical.choose (hc η (𝟙 A.W₀) p g)

theorem value_spec (hc : Closed A) {Param : Classicism.Meta.Ty → Type}
    (η : Assignment A Param) {Γ σ} (p : ITerm Param Γ σ)
    (g : IEnv (A.Dom A.W₀) Γ) :
    A.Incl σ A.W₀ ((value A) hc η p g) = sem A η (𝟙 A.W₀) p g :=
  Classical.choose_spec (hc η (𝟙 A.W₀) p g)

theorem holds_all {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) {Γ σ W}
    (h : A.W₀ ⟶ W) (p : ITerm Param (σ :: Γ) Ty.t)
    (g : IEnv (A.Dom W) Γ) :
    Holds A η h (.all p) g ↔ ∀ x : A.Dom W σ, Holds A η h p (.cons x g) := by
  simp only [Holds, sem, Intension.True, Set.mem_setOf_eq,
    Category.comp_id, A.push_id]

theorem holds_ex {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param) {Γ σ W}
    (h : A.W₀ ⟶ W) (p : ITerm Param (σ :: Γ) Ty.t)
    (g : IEnv (A.Dom W) Γ) :
    Holds A η h (.ex p) g ↔ ∃ x : A.Dom W σ, Holds A η h p (.cons x g) := by
  simp only [Holds, sem, Intension.True, Set.mem_setOf_eq,
    Category.comp_id, A.push_id]

/-- The first-class modal operation reads the complete future profile of an
admitted proposition. This lemma does not assume S5 or constant domains. -/
theorem box_read_true {W : C} (p : A.Dom W Ty.t) :
    Intension.True A.inner (A.apply (A.boxRead .t W) (A.Incl Ty.t W p)) ↔
      ∀ z : Tuple A.inner .t W, z ∈ A.incl .t W p := by
  rw [A.apply_Incl]
  simp only [Intension.True, Intension.app, Premodel.boxRead, Set.mem_setOf_eq,
    Functor.map_id, types_id_apply]
  constructor
  · intro h z
    rcases z with ⟨V, ⟨⟩, k⟩
    exact h V k
  · intro h V k
    exact h ⟨V, PUnit.unit, k⟩

theorem holds_box {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    (hc : Closed A) {Γ W} (h : A.W₀ ⟶ W) (p : ITerm Param Γ Ty.t)
    (g : IEnv (A.Dom W) Γ) :
    Holds A η h p.box g ↔ ∀ z : Tuple A.inner .t W, z ∈ sem A η h p g := by
  obtain ⟨a, ha⟩ := hc η h p g
  change Intension.True A.inner (A.apply (A.boxRead .t W) (sem A η h p g)) ↔ _
  rw [← ha]
  exact (box_read_true A) a

/-- A specific admitted infinitary matrix naming precisely the root objects. -/
def namedRange (σ : Classicism.Meta.Ty) : ITerm (A.Dom A.W₀) [σ] Ty.t :=
  .iOr (A.Dom A.W₀ σ) (fun a => .eq (.var .zero) (.param a))

def selfAssignment : Assignment A (A.Dom A.W₀) := fun a => a

/-- Comprehension of the named-range formula yields the actual range of each
root-to-future map. No surjectivity or constant-domain presentation is assumed. -/
theorem named_range_witness (hc : Closed A) (hcomp : Comprehension A) (σ : Classicism.Meta.Ty) :
    ∃ R : A.Dom A.W₀ (σ ⇒ RTy.t),
      ∀ (V : C) (h : A.W₀ ⟶ V) (x : A.Dom V σ),
        (⟨V, (x, PUnit.unit), h⟩ : Tuple A.inner (σ ⇒ RTy.t) A.W₀) ∈
          A.incl (σ ⇒ RTy.t) A.W₀ R ↔
            ∃ a : A.Dom A.W₀ σ, (A.inner σ).map h a = x := by
  have H := hcomp (selfAssignment A) ((namedRange A) σ)
  obtain ⟨R, hR⟩ := ((holds_ex A) (selfAssignment A) (𝟙 A.W₀) _ IEnv.nil).1 H
  have hb := ((holds_box A) (selfAssignment A) hc (𝟙 A.W₀) _ (.cons R .nil)).1 hR
  refine ⟨R, ?_⟩
  intro V h x
  have hx := hb ⟨V, PUnit.unit, h⟩
  change ∀ y : A.Dom V σ, _ at hx
  specialize hx x
  simp only [InfinitaryComprehension.Term.comprehension, InfinitaryComprehension.Term.compBody,
    InfinitaryComprehension.Term.closeAll, InfinitaryComprehension.Term.applyVars,
    InfinitaryComprehension.Term.rename, lastVar, Ren.embed, namedRange,
    selfAssignment, sem, Intension.True, Premodel.push, IEnv.map, IEnv.get,
    Category.id_comp, Category.comp_id, A.push_id] at hx
  simp only [A.apply_Incl] at hx
  simp only [Intension.app, A.incl_map, Intension.map, Set.mem_setOf_eq,
    Functor.map_id, types_id_apply, Category.comp_id, Outer.map_id] at hx
  have heq (a : A.Dom A.W₀ σ) :
      A.Incl σ V x = A.Incl σ V ((A.inner σ).map h a) ↔
        (A.inner σ).map h a = x := by
    constructor
    · intro e
      exact (A.Incl_injective σ V e).symm
    · intro e
      exact congrArg (A.Incl σ V) e.symm
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_setOf_eq, Premodel.Incl_rel, Functor.map_id, types_id_apply,
    A.incl_map, Intension.map, Category.comp_id, Outer.map_id, heq] at hx
  exact ⟨fun hp => hx.1.resolve_left (fun hn => hn hp),
    fun hq => hx.2.resolve_left (fun hn => hn hq)⟩

/-- The finite BF reading needed for the range argument; supplied as truth of
the actual finite sentence, not as a domain-surjectivity premise. -/
theorem bf_predicate_read (M : A.IsModel) (σ : Classicism.Meta.Ty)
    (hbf : A.HoldsSentence (Sentence.bf σ))
    (R : A.Dom A.W₀ (σ ⇒ RTy.t))
    (hall : ∀ a : A.Dom A.W₀ σ, ∀ (V : C) (h : A.W₀ ⟶ V),
      (⟨V, ((A.inner σ).map h a, PUnit.unit), h⟩ :
        Tuple A.inner (σ ⇒ RTy.t) A.W₀) ∈ A.incl _ A.W₀ R) :
    ∀ (V : C) (h : A.W₀ ⟶ V) (x : A.Dom V σ),
      (⟨V, (x, PUnit.unit), h⟩ : Tuple A.inner (σ ⇒ RTy.t) A.W₀) ∈
        A.incl _ A.W₀ R := by
  intro V h x
  exact Classicism.Meta.Research.InfinitaryComprehensionC5Bridge.barcan_profile
    A M (𝟙 A.W₀) hbf R (fun a V k => hall a V k) h x

/-- Infinitary named ranges plus actual BF eliminate future domain growth. -/
theorem root_map_surjective (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (σ : Classicism.Meta.Ty)
    (hbf : A.HoldsSentence (Sentence.bf σ))
    {V : C} (h : A.W₀ ⟶ V) : Function.Surjective ((A.inner σ).map h) := by
  obtain ⟨R, hR⟩ := (named_range_witness A) hc hcomp σ
  have hall : ∀ a : A.Dom A.W₀ σ, ∀ (V : C) (k : A.W₀ ⟶ V),
      (⟨V, ((A.inner σ).map k a, PUnit.unit), k⟩ :
        Tuple A.inner (σ ⇒ RTy.t) A.W₀) ∈ A.incl _ A.W₀ R := by
    intro a V k
    exact (hR V k _).2 ⟨a, rfl⟩
  intro x
  exact (hR V h x).1 ((bf_predicate_read A) M σ hbf R hall V h x)

/-- ND gives the other half directly in the original categorical semantics. -/
theorem root_map_injective (M : A.IsModel) (σ : Classicism.Meta.Ty)
    (hnd : A.HoldsSentence (Sentence.nd σ)) {V : C} (h : A.W₀ ⟶ V) :
    Function.Injective ((A.inner σ).map h) :=
  (A.holds_nd_iff M σ (𝟙 A.W₀)).1 hnd h

theorem root_map_bijective (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (σ : Classicism.Meta.Ty)
    (hnd : A.HoldsSentence (Sentence.nd σ))
    (hbf : A.HoldsSentence (Sentence.bf σ)) {V : C} (h : A.W₀ ⟶ V) :
    Function.Bijective ((A.inner σ).map h) :=
  ⟨(root_map_injective A) M σ hnd h, (root_map_surjective A) M hc hcomp σ hbf h⟩


/-! ## Root operations, obtained from actual admitted terms -/

noncomputable def rootTerm (hc : Closed A) {σ}
    (p : ITerm (A.Dom A.W₀) [] σ) : A.Dom A.W₀ σ :=
  (value A) hc (selfAssignment A) p .nil

theorem rootTerm_spec (hc : Closed A) {σ}
    (p : ITerm (A.Dom A.W₀) [] σ) :
    A.Incl σ A.W₀ ((rootTerm A) hc p) = sem A (selfAssignment A) (𝟙 A.W₀) p .nil :=
  (value_spec A) hc (selfAssignment A) p .nil

noncomputable def rootApp (hc : Closed A) {σ : Classicism.Meta.Ty} {ρ : RTy}
    (f : A.Dom A.W₀ (σ ⇒ ρ)) (a : A.Dom A.W₀ σ) : A.Dom A.W₀ ρ :=
  (rootTerm A) hc (.app (.param f) (.param a))

set_option backward.isDefEq.respectTransparency false in
theorem rootApp_spec (hc : Closed A) {σ : Classicism.Meta.Ty} {ρ : RTy}
    (f : A.Dom A.W₀ (σ ⇒ ρ)) (a : A.Dom A.W₀ σ) :
    A.incl ρ A.W₀ ((rootApp A) hc f a) = (A.incl _ A.W₀ f).app A.inner a := by
  have hterm := rootTerm_spec A hc (σ := .rel ρ) (.app (.param f) (.param a))
  simp only [Premodel.Incl] at hterm
  rw [rootApp, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply]
  exact A.apply_Incl _ _

noncomputable def rootTop (hc : Closed A) : A.Dom A.W₀ Ty.t := (rootTerm A) hc .top
noncomputable def rootBot (hc : Closed A) : A.Dom A.W₀ Ty.t := (rootTerm A) hc .bot
noncomputable def rootNeg (hc : Closed A) (p : A.Dom A.W₀ Ty.t) :=
  (rootTerm A) hc (.neg (.param p))
noncomputable def rootConj (hc : Closed A) (p q : A.Dom A.W₀ Ty.t) :=
  (rootTerm A) hc (.conj (.param p) (.param q))
noncomputable def rootDisj (hc : Closed A) (p q : A.Dom A.W₀ Ty.t) :=
  (rootTerm A) hc (.disj (.param p) (.param q))
noncomputable def rootImp (hc : Closed A) (p q : A.Dom A.W₀ Ty.t) :=
  (rootTerm A) hc (.imp (.param p) (.param q))
noncomputable def rootIff (hc : Closed A) (p q : A.Dom A.W₀ Ty.t) :=
  (rootTerm A) hc (.iff (.param p) (.param q))
noncomputable def rootEq (hc : Closed A) {σ : Classicism.Meta.Ty} (a b : A.Dom A.W₀ σ) :=
  (rootTerm A) hc (.eq (.param a) (.param b))
noncomputable def rootBox (hc : Closed A) : A.Dom A.W₀ (RTy.t ⇒ RTy.t) :=
  (rootTerm A) hc .boxOp
noncomputable def rootAnd (hc : Closed A) (I : Type) (p : I → A.Dom A.W₀ Ty.t) :=
  (rootTerm A) hc (.iAnd I (fun i => .param (p i)))
noncomputable def rootOr (hc : Closed A) (I : Type) (p : I → A.Dom A.W₀ Ty.t) :=
  (rootTerm A) hc (.iOr I (fun i => .param (p i)))

@[simp] theorem incl_rootTop (hc : Closed A) :
    A.incl .t A.W₀ ((rootTop A) hc) = Set.univ := (rootTerm_spec A) hc .top
@[simp] theorem incl_rootBot (hc : Closed A) :
    A.incl .t A.W₀ ((rootBot A) hc) = ∅ := (rootTerm_spec A) hc .bot
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem incl_rootNeg (hc : Closed A) (p : A.Dom A.W₀ Ty.t) :
    A.incl .t A.W₀ ((rootNeg A) hc p) = (A.incl .t A.W₀ p)ᶜ := by
  have hterm := rootTerm_spec A hc (σ := Ty.t) (.neg (.param p))
  simp only [Premodel.Incl] at hterm
  rw [rootNeg, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply] <;> rfl
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem incl_rootConj (hc : Closed A) (p q : A.Dom A.W₀ Ty.t) :
    A.incl .t A.W₀ ((rootConj A) hc p q) = A.incl .t A.W₀ p ∩ A.incl .t A.W₀ q := by
  have hterm := rootTerm_spec A hc (σ := Ty.t) (.conj (.param p) (.param q))
  simp only [Premodel.Incl] at hterm
  rw [rootConj, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply] <;> rfl
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem incl_rootDisj (hc : Closed A) (p q : A.Dom A.W₀ Ty.t) :
    A.incl .t A.W₀ ((rootDisj A) hc p q) = A.incl .t A.W₀ p ∪ A.incl .t A.W₀ q := by
  have hterm := rootTerm_spec A hc (σ := Ty.t) (.disj (.param p) (.param q))
  simp only [Premodel.Incl] at hterm
  rw [rootDisj, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply] <;> rfl
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem incl_rootImp (hc : Closed A) (p q : A.Dom A.W₀ Ty.t) :
    A.incl .t A.W₀ ((rootImp A) hc p q) = (A.incl .t A.W₀ p)ᶜ ∪ A.incl .t A.W₀ q := by
  have hterm := rootTerm_spec A hc (σ := Ty.t) (.imp (.param p) (.param q))
  simp only [Premodel.Incl] at hterm
  rw [rootImp, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply] <;> rfl
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem incl_rootIff (hc : Closed A) (p q : A.Dom A.W₀ Ty.t) :
    A.incl .t A.W₀ ((rootIff A) hc p q) =
      ((A.incl .t A.W₀ p)ᶜ ∪ A.incl .t A.W₀ q) ∩
        ((A.incl .t A.W₀ q)ᶜ ∪ A.incl .t A.W₀ p) := by
  have hterm := rootTerm_spec A hc (σ := Ty.t) (.iff (.param p) (.param q))
  simp only [Premodel.Incl] at hterm
  rw [rootIff, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply] <;> rfl
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem incl_rootEq (hc : Closed A) {σ : Classicism.Meta.Ty} (a b : A.Dom A.W₀ σ) :
    A.incl .t A.W₀ ((rootEq A) hc a b) =
      {w | (A.inner σ).map w.2.2 a = (A.inner σ).map w.2.2 b} := by
  have hterm := rootTerm_spec A hc (σ := Ty.t) (.eq (.param a) (.param b))
  simp only [Premodel.Incl] at hterm
  rw [rootEq, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply]
  ext w
  simp only [Set.mem_setOf_eq]
  rw [← A.Incl_map, ← A.Incl_map]
  exact (A.Incl_injective σ w.1).eq_iff
@[simp] theorem incl_rootBox (hc : Closed A) :
    A.incl _ A.W₀ ((rootBox A) hc) = A.boxRead .t A.W₀ := (rootTerm_spec A) hc .boxOp
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem incl_rootAnd (hc : Closed A) (I : Type) (p : I → A.Dom A.W₀ Ty.t) :
    A.incl .t A.W₀ ((rootAnd A) hc I p) = {w | ∀ i, w ∈ A.incl .t A.W₀ (p i)} := by
  have hterm := rootTerm_spec A hc (σ := Ty.t) (.iAnd I (fun i => .param (p i)))
  simp only [Premodel.Incl] at hterm
  rw [rootAnd, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply] <;> rfl
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem incl_rootOr (hc : Closed A) (I : Type) (p : I → A.Dom A.W₀ Ty.t) :
    A.incl .t A.W₀ ((rootOr A) hc I p) = {w | ∃ i, w ∈ A.incl .t A.W₀ (p i)} := by
  have hterm := rootTerm_spec A hc (σ := Ty.t) (.iOr I (fun i => .param (p i)))
  simp only [Premodel.Incl] at hterm
  rw [rootOr, hterm]
  simp only [sem, selfAssignment, Functor.map_id, types_id_apply] <;> rfl

/-- Injectivity at t reflects a proposition's becoming top. This is precisely
why the forward cone modal clause becomes a universal-world modal clause. -/
theorem root_box_spec (hc : Closed A)
    (hinj : ∀ {V} (h : A.W₀ ⟶ V), Function.Injective ((A.inner Ty.t).map h))
    (p : A.Dom A.W₀ Ty.t) (w : Tuple A.inner .t A.W₀) :
    w ∈ A.incl .t A.W₀ ((rootApp A) hc ((rootBox A) hc) p) ↔
      ∀ v, v ∈ A.incl .t A.W₀ p := by
  rw [(rootApp_spec A), (incl_rootBox A), A.app_boxRead]
  change (∀ U (k : w.1 ⟶ U),
    (⟨U, PUnit.unit, w.2.2 ≫ k⟩ : Tuple A.inner .t A.W₀) ∈ A.incl .t A.W₀ p) ↔ _
  constructor
  · intro hw
    have he : (A.inner Ty.t).map w.2.2 p =
        (A.inner Ty.t).map w.2.2 ((rootTop A) hc) := by
      apply A.incl_injective .t w.1
      rw [A.incl_map, A.incl_map, (incl_rootTop A)]
      ext ⟨U, ⟨⟩, k⟩
      exact iff_true_intro (hw U k)
    have hp := hinj w.2.2 he
    rw [hp, (incl_rootTop A)]
    exact fun _ => Set.mem_univ _
  · intro hp U k
    exact hp ⟨U, PUnit.unit, w.2.2 ≫ k⟩

open Grounding

abbrev C5 (A : Premodel Sig C) : Prop :=
  Classicism.Meta.Research.InfinitaryComprehensionC5Bridge.C5 A

/-- Grounding changes only auxiliary type-variable codes. Every actual closed
object type, and all its root objects, are retained literally. -/
def RootInjective : Prop :=
  ∀ (σ : Classicism.Meta.Ty) {V : C} (h : A.W₀ ⟶ V),
    Function.Injective ((A.inner (groundTy σ)).map h)

def RootSurjective : Prop :=
  ∀ (σ : Classicism.Meta.Ty) {V : C} (h : A.W₀ ⟶ V),
    Function.Surjective ((A.inner (groundTy σ)).map h)

set_option backward.isDefEq.respectTransparency false in
noncomputable def rawModelOfInjections (hc : Closed A) (hinj : RootInjective A) :
    Henkin.Model where
  Dom σ := A.Dom A.W₀ (groundTy σ)
  World := Tuple A.inner .t A.W₀
  truth p w := w ∈ A.incl .t A.W₀ p
  app f a := (rootApp A) hc f a
  top := (rootTop A) hc
  bot := (rootBot A) hc
  neg := (rootNeg A) hc
  conj := (rootConj A) hc
  disj := (rootDisj A) hc
  imp := (rootImp A) hc
  iff := (rootIff A) hc
  eq a b := (rootEq A) hc a b
  boxObj := (rootBox A) hc
  iAnd := (rootAnd A) hc
  iOr := (rootOr A) hc
  top_spec w := by simp
  bot_spec w := by simp
  neg_spec p w := by simp
  conj_spec p q w := by simp
  disj_spec p q w := by simp
  imp_spec p q w := by classical simp [imp_iff_not_or]
  iff_spec p q w := by
    classical
    rw [(incl_rootIff A)]
    change ((¬ _ ∨ _) ∧ (¬ _ ∨ _)) ↔ (_ ↔ _)
    constructor
    · intro h
      exact ⟨fun hp => h.1.resolve_left (fun hn => hn hp),
        fun hq => h.2.resolve_left (fun hn => hn hq)⟩
    · intro h
      exact ⟨imp_iff_not_or.mp h.mp, imp_iff_not_or.mp h.mpr⟩
  eq_spec a b w := by
    rw [(incl_rootEq A)]
    exact (hinj _ w.2.2).eq_iff
  box_spec p w := (root_box_spec A) hc (fun {_} h => hinj Ty.t h) p w
  iAnd_spec I p w := by simp
  iOr_spec I p w := by simp

/-- Native finite-C5 wrapper, retained for existing callers. -/
theorem c5_rootInjective (M : A.IsModel) (hC5 : C5 A) : RootInjective A :=
  fun σ {_} h => Classicism.Meta.Research.InfinitaryComprehensionC5Bridge.c5_map_injective
    A M hC5 _ (groundTy_closed σ) (𝟙 A.W₀) h

noncomputable def rawModel (M : A.IsModel) (hc : Closed A) (hC5 : C5 A) : Henkin.Model :=
  (rawModelOfInjections A) hc ((c5_rootInjective A) M hC5)

/-- This is a proved property of the original C5 action, not a field of the
canonical presentation. -/
theorem ground_map_surjective (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A) (σ : Classicism.Meta.Ty)
    {V} (h : A.W₀ ⟶ V) : Function.Surjective ((A.inner (groundTy σ)).map h) :=
  (root_map_surjective A) M hc hcomp (groundTy σ)
    (Classicism.Meta.Research.InfinitaryComprehensionC5Bridge.c5_bf
      A M hC5 (groundTy σ) (groundTy_closed σ)) h

set_option backward.isDefEq.respectTransparency false in
/-- Root application profiles are faithful because every future argument has a
root preimage and the original intensional inclusion is injective. -/
theorem rawModel_faithful_of_surjections (hc : Closed A)
    (hinj : RootInjective A) (hepi : RootSurjective A) :
    Henkin.Faithful ((rawModelOfInjections A) hc hinj) := by
  intro Γ
  induction Γ with
  | nil =>
      intro R S h
      apply A.incl_injective .t A.W₀
      exact Set.ext (fun w => h Henkin.Env.nil w)
  | cons σ Γ ih =>
      intro R S h
      apply A.incl_injective (groundRTy (RTy.ofArgs (σ :: Γ))) A.W₀
      ext ⟨V, ⟨x, a⟩, k⟩
      obtain ⟨y, hy⟩ := hepi σ k x
      have he : (rootApp A) hc R y = (rootApp A) hc S y :=
        ih _ _ (fun xs w => by
          have hh := h (Henkin.Env.cons (M := rawModelOfInjections A hc hinj)
            (σ := σ) y xs) w
          dsimp only [Henkin.uncurry, Henkin.Env.tail, Henkin.Env.cons,
            rawModelOfInjections] at hh ⊢
          exact hh)
      have hi := congrArg (A.incl (groundRTy (RTy.ofArgs Γ)) A.W₀) he
      rw [(rootApp_spec A), (rootApp_spec A)] at hi
      have ht := Set.ext_iff.mp hi ⟨V, a, k⟩
      change (⟨V, (x, a), k⟩ ∈
          A.incl (groundTy σ ⇒ groundRTy (RTy.ofArgs Γ)) A.W₀ R) ↔
        (⟨V, (x, a), k⟩ ∈
          A.incl (groundTy σ ⇒ groundRTy (RTy.ofArgs Γ)) A.W₀ S)
      simpa only [Intension.mem_app, hy] using ht


theorem rawModel_faithful (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A) : Henkin.Faithful ((rawModel A) M hc hC5) :=
  (rawModel_faithful_of_surjections A) hc ((c5_rootInjective A) M hC5)
    (fun σ {_} h => (ground_map_surjective A) M hc hcomp hC5 σ h)

/-- Pull a typed environment through grounding without changing its entries. -/
def groundEnv :
    {Γ : Ctx} → (∀ {σ}, Var Γ σ → A.Dom A.W₀ (groundTy σ)) →
      IEnv (A.Dom A.W₀) (groundCtx Γ)
  | [], _ => .nil
  | _ :: _, xs => .cons (xs .zero) (groundEnv (fun v => xs (.succ v)))

theorem groundEnv_get {Γ σ}
    (xs : ∀ {τ}, Var Γ τ → A.Dom A.W₀ (groundTy τ)) (v : Var Γ σ) :
    ((groundEnv A) xs).get (groundVar v) = xs v := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih (fun v => xs (.succ v))

theorem groundEnv_cons {Γ σ} (a : A.Dom A.W₀ (groundTy σ))
    (xs : ∀ {τ}, Var Γ τ → A.Dom A.W₀ (groundTy τ)) :
    (groundEnv A)
      (fun {τ} (v : Var (σ :: Γ) τ) => match v with
        | .zero => a
        | .succ v => xs v) = IEnv.cons a ((groundEnv A) xs) := rfl

/-- Reading a transported formula at its current point reads the corresponding
root arrow of its root intension. -/
theorem holds_push_root {Param : Classicism.Meta.Ty → Type} (η : Assignment A Param)
    {Γ V} (h : A.W₀ ⟶ V) (p : ITerm Param Γ Ty.t)
    (g : IEnv (A.Dom A.W₀) Γ) :
    Holds A η h p (A.push h g) ↔
      (⟨V, PUnit.unit, h⟩ : Tuple A.inner .t A.W₀) ∈
        sem A η (𝟙 A.W₀) p g := by
  have hh := (sem_push A) η (𝟙 A.W₀) p g h
  rw [Category.id_comp] at hh
  simp only [Holds, hh, Outer.map_rel, Intension.True, Intension.map,
    Set.mem_setOf_eq, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical evaluator agrees with the genuine original infinitary
semantics. In the binder cases, future-domain quantification is converted
using the proved named-range surjectivity theorem, not by a semantic field. -/
theorem raw_eval_spec_of_surjections (hc : Closed A)
    (hinj : RootInjective A) (hepi : RootSurjective A) {Param : Classicism.Meta.Ty → Type}
    (η : Henkin.Assignment ((rawModelOfInjections A) hc hinj) Param) :
    ∀ {Γ σ} (p : ITerm Param Γ σ) (xs : Henkin.Env ((rawModelOfInjections A) hc hinj) Γ),
      A.Incl (groundTy σ) A.W₀ (Henkin.eval ((rawModelOfInjections A) hc hinj) η p xs) =
        sem A (selfAssignment A) (𝟙 A.W₀) (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p) ((groundEnv A) xs) := by
  intro Γ σ p
  induction p with
  | var v =>
      intro xs
      change A.Incl _ _ (xs v) = A.Incl _ _ (((groundEnv A) xs).get (groundVar v))
      rw [(groundEnv_get A)]
  | param p =>
      intro xs
      simp only [Henkin.eval, groundTerm, sem, selfAssignment,
        Functor.map_id, types_id_apply]
  | app f a ihf iha =>
      intro xs
      change A.incl _ _ ((rootApp A) hc _ _) = A.apply _ _
      rw [(rootApp_spec A), ← ihf xs, ← iha xs, A.apply_Incl]
      rfl
  | top => intro xs; exact (incl_rootTop A) hc
  | bot => intro xs; exact (incl_rootBot A) hc
  | neg p ih =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ih
      change A.incl .t A.W₀ ((rootNeg A) hc _) =
        (sem A (selfAssignment A) (σ := Ty.t) (𝟙 A.W₀)
          (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
          ((groundEnv A) xs))ᶜ
      rw [(incl_rootNeg A), ih xs]
  | conj p q ihp ihq =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ihp ihq
      change A.incl _ _ ((rootConj A) hc _ _) = _ ∩ _
      rw [(incl_rootConj A), ihp xs, ihq xs]
  | disj p q ihp ihq =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ihp ihq
      change A.incl _ _ ((rootDisj A) hc _ _) = _ ∪ _
      rw [(incl_rootDisj A), ihp xs, ihq xs]
  | imp p q ihp ihq =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ihp ihq
      change A.incl _ _ ((rootImp A) hc _ _) = _ᶜ ∪ _
      rw [(incl_rootImp A), ihp xs, ihq xs]
  | iff p q ihp ihq =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ihp ihq
      change A.incl _ _ ((rootIff A) hc _ _) = (_ᶜ ∪ _) ∩ (_ᶜ ∪ _)
      rw [(incl_rootIff A), ihp xs, ihq xs]
  | eq a b iha ihb =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl]
      rw [show Henkin.eval ((rawModelOfInjections A) hc hinj) η (.eq a b) xs =
        (rootEq A) hc (Henkin.eval _ η a xs) (Henkin.eval _ η b xs) from rfl,
        (incl_rootEq A)]
      change {w : Tuple A.inner .t A.W₀ | _ = _} =
        {w : Tuple A.inner .t A.W₀ | Outer.map A.inner _ w.2.2
          (sem A (selfAssignment A) (𝟙 A.W₀)
            (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η a) ((groundEnv A) xs)) =
          Outer.map A.inner _ w.2.2
          (sem A (selfAssignment A) (𝟙 A.W₀)
            (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η b) ((groundEnv A) xs))}
      rw [← iha xs, ← ihb xs]
      ext w
      simp only [Set.mem_setOf_eq]
      rw [← A.Incl_map, ← A.Incl_map]
      exact (A.Incl_injective _ _).eq_iff.symm
  | boxOp => intro xs; exact (incl_rootBox A) hc
  | all p ih =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ih
      change A.incl .t A.W₀ ((rootAnd A) hc _
        (fun x => Henkin.eval ((rawModelOfInjections A) hc hinj) η p (Henkin.Env.cons x xs))) = _
      rw [(incl_rootAnd A)]
      ext ⟨V, ⟨⟩, h⟩
      change (∀ x, _ ∈ A.incl .t A.W₀ (Henkin.eval _ η p (Henkin.Env.cons x xs))) ↔
        ∀ x, Holds A (selfAssignment A) ((𝟙 A.W₀) ≫ h) (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
          (.cons x (A.push h ((groundEnv A) xs)))
      rw [Category.id_comp]
      constructor
      · intro hx x
        obtain ⟨y, rfl⟩ := hepi _ h x
        have hy := hx y
        rw [ih] at hy
        exact ((holds_push_root A) (selfAssignment A) h (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
          (.cons y ((groundEnv A) xs))).2 hy
      · intro hx y
        rw [ih]
        exact ((holds_push_root A) (selfAssignment A) h (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
          (.cons y ((groundEnv A) xs))).1 (hx ((A.inner _).map h y))
  | ex p ih =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ih
      change A.incl .t A.W₀ ((rootOr A) hc _
        (fun x => Henkin.eval ((rawModelOfInjections A) hc hinj) η p (Henkin.Env.cons x xs))) = _
      rw [(incl_rootOr A)]
      ext ⟨V, ⟨⟩, h⟩
      change (∃ x, _ ∈ A.incl .t A.W₀ (Henkin.eval _ η p (Henkin.Env.cons x xs))) ↔
        ∃ x, Holds A (selfAssignment A) ((𝟙 A.W₀) ≫ h) (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
          (.cons x (A.push h ((groundEnv A) xs)))
      rw [Category.id_comp]
      constructor
      · rintro ⟨y, hy⟩
        rw [ih] at hy
        exact ⟨(A.inner _).map h y,
          ((holds_push_root A) (selfAssignment A) h (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
            (.cons y ((groundEnv A) xs))).2 hy⟩
      · rintro ⟨x, hx⟩
        obtain ⟨y, rfl⟩ := hepi _ h x
        refine ⟨y, ?_⟩
        rw [ih]
        exact ((holds_push_root A) (selfAssignment A) h (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
          (.cons y ((groundEnv A) xs))).1 hx
  | iAnd I p ih =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ih
      change A.incl _ _ ((rootAnd A) hc I _) = _
      rw [(incl_rootAnd A)]
      ext w
      exact forall_congr' (fun i => by rw [ih i xs])
  | iOr I p ih =>
      intro xs
      simp only [groundTy, groundRTy, Premodel.Incl] at ih
      change A.incl _ _ ((rootOr A) hc I _) = _
      rw [(incl_rootOr A)]
      ext w
      exact exists_congr (fun i => by rw [ih i xs])

/-- Original native-C wrapper for the stronger, lambda-free semantic lemma. -/
theorem raw_eval_spec (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A) {Param : Classicism.Meta.Ty → Type}
    (η : Henkin.Assignment ((rawModel A) M hc hC5) Param)
    {Γ σ} (p : ITerm Param Γ σ) (xs : Henkin.Env ((rawModel A) M hc hC5) Γ) :
    A.Incl (groundTy σ) A.W₀ (Henkin.eval ((rawModel A) M hc hC5) η p xs) =
      sem A (selfAssignment A) (𝟙 A.W₀) (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p) ((groundEnv A) xs) :=
  (raw_eval_spec_of_surjections A) hc ((c5_rootInjective A) M hC5)
    (fun τ {_} h => (ground_map_surjective A) M hc hcomp hC5 τ h) η p xs

/-- Every rooted evaluation agrees, not just the theorem sentences. -/
theorem raw_truth_spec_of_surjections (hc : Closed A)
    (hinj : RootInjective A) (hepi : RootSurjective A) {Param : Classicism.Meta.Ty → Type}
    (η : Henkin.Assignment ((rawModelOfInjections A) hc hinj) Param) {Γ}
    (p : ITerm Param Γ Ty.t) (xs : Henkin.Env ((rawModelOfInjections A) hc hinj) Γ)
    (w : Tuple A.inner .t A.W₀) :
    ((rawModelOfInjections A) hc hinj).truth (Henkin.eval _ η p xs) w ↔
      Holds A (selfAssignment A) w.2.2 (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
        (A.push w.2.2 ((groundEnv A) xs)) := by
  change w ∈ A.incl .t A.W₀ (Henkin.eval _ η p xs) ↔ _
  have he := (raw_eval_spec_of_surjections A) hc hinj hepi η p xs
  simp only [groundTy, groundRTy, Premodel.Incl] at he
  rw [he]
  rcases w with ⟨V, ⟨⟩, h⟩
  exact ((holds_push_root A) (selfAssignment A) h _ _).symm


theorem raw_truth_spec (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A) {Param : Classicism.Meta.Ty → Type}
    (η : Henkin.Assignment ((rawModel A) M hc hC5) Param) {Γ}
    (p : ITerm Param Γ Ty.t) (xs : Henkin.Env ((rawModel A) M hc hC5) Γ)
    (w : Tuple A.inner .t A.W₀) :
    ((rawModel A) M hc hC5).truth (Henkin.eval _ η p xs) w ↔
      Holds A (selfAssignment A) w.2.2 (groundTerm (Param := Param) (Param' := A.Dom A.W₀) η p)
        (A.push w.2.2 ((groundEnv A) xs)) :=
  (raw_truth_spec_of_surjections A) hc ((c5_rootInjective A) M hC5)
    (fun τ {_} h => (ground_map_surjective A) M hc hcomp hC5 τ h) η p xs w

/-! ## Removing duplicate worlds by their represented truth profiles -/

/-- This quotient only identifies worlds already indistinguishable by every
represented proposition. No separating propositions are assumed. -/
def observationalSetoid (N : Henkin.Model) : Setoid N.World where
  r w v := ∀ p, N.truth p w ↔ N.truth p v
  iseqv := ⟨fun _ _ => Iff.rfl, fun h p => (h p).symm,
    fun h k p => (h p).trans (k p)⟩

noncomputable def quotientModel (N : Henkin.Model) : Henkin.Model where
  Dom := N.Dom
  World := Quotient (observationalSetoid N)
  truth p := Quotient.lift (N.truth p) (fun _ _ h => propext (h p))
  app := N.app
  top := N.top
  bot := N.bot
  neg := N.neg
  conj := N.conj
  disj := N.disj
  imp := N.imp
  iff := N.iff
  eq := N.eq
  boxObj := N.boxObj
  iAnd := N.iAnd
  iOr := N.iOr
  top_spec w := Quotient.inductionOn w N.top_spec
  bot_spec w := Quotient.inductionOn w N.bot_spec
  neg_spec p w := Quotient.inductionOn w (N.neg_spec p)
  conj_spec p q w := Quotient.inductionOn w (N.conj_spec p q)
  disj_spec p q w := Quotient.inductionOn w (N.disj_spec p q)
  imp_spec p q w := Quotient.inductionOn w (N.imp_spec p q)
  iff_spec p q w := Quotient.inductionOn w (N.iff_spec p q)
  eq_spec a b w := Quotient.inductionOn w (N.eq_spec a b)
  box_spec p w := by
    induction w using Quotient.inductionOn with
    | h w =>
        change N.truth (N.app N.boxObj p) w ↔ _
        rw [N.box_spec]
        constructor
        · intro hp v
          exact Quotient.inductionOn v hp
        · intro hp v
          exact hp (Quotient.mk _ v)
  iAnd_spec I p w := Quotient.inductionOn w (N.iAnd_spec I p)
  iOr_spec I p w := Quotient.inductionOn w (N.iOr_spec I p)

@[simp] theorem quotient_truth (N : Henkin.Model) (p : N.Dom Ty.t) (w : N.World) :
    (quotientModel N).truth p (Quotient.mk _ w) ↔ N.truth p w := Iff.rfl

theorem quotient_worldSeparated (N : Henkin.Model) : Henkin.WorldSeparated (quotientModel N) := by
  classical
  intro w v
  refine Quotient.inductionOn₂ w v ?_
  intro w v hne
  by_contra hnone
  apply hne
  apply Quotient.sound
  intro p
  constructor
  · intro hp
    by_contra hn
    exact hnone ⟨p, hp, hn⟩
  · intro hp
    by_contra hn
    apply hnone
    refine ⟨N.neg p, (N.neg_spec p w).2 hn, ?_⟩
    intro hneg
    exact (N.neg_spec p v).1 hneg hp

/-- Changing only the world presentation changes no term's denotation. -/
theorem quotient_eval (N : Henkin.Model.{u}) {Param : Classicism.Meta.Ty → Type u}
    (η : Henkin.Assignment N Param) :
    ∀ {Γ σ} (p : ITerm Param Γ σ) (xs : Henkin.Env N Γ),
      Henkin.eval (quotientModel N) η p xs = Henkin.eval N η p xs := by
  intro Γ σ p
  induction p with
  | var => intro xs; rfl
  | param => intro xs; rfl
  | app f a ihf iha => intro xs; exact congrArg₂ N.app (ihf xs) (iha xs)
  | top => intro xs; rfl
  | bot => intro xs; rfl
  | neg p ih => intro xs; exact congrArg N.neg (ih xs)
  | conj p q ihp ihq => intro xs; exact congrArg₂ N.conj (ihp xs) (ihq xs)
  | disj p q ihp ihq => intro xs; exact congrArg₂ N.disj (ihp xs) (ihq xs)
  | imp p q ihp ihq => intro xs; exact congrArg₂ N.imp (ihp xs) (ihq xs)
  | iff p q ihp ihq => intro xs; exact congrArg₂ N.iff (ihp xs) (ihq xs)
  | eq a b iha ihb => intro xs; exact congrArg₂ N.eq (iha xs) (ihb xs)
  | boxOp => intro xs; rfl
  | all p ih =>
      intro xs
      exact congrArg (N.iAnd _) (funext (fun x => ih (Henkin.Env.cons x xs)))
  | ex p ih =>
      intro xs
      exact congrArg (N.iOr _) (funext (fun x => ih (Henkin.Env.cons x xs)))
  | iAnd I p ih => intro xs; exact congrArg (N.iAnd I) (funext (fun i => ih i xs))
  | iOr I p ih => intro xs; exact congrArg (N.iOr I) (funext (fun i => ih i xs))

theorem quotient_uncurry (N : Henkin.Model) :
    ∀ (Γ : Ctx) (R : N.Dom (RTy.ofArgs Γ)) (xs : Henkin.Env N Γ),
      Henkin.uncurry (quotientModel N) Γ R xs = Henkin.uncurry N Γ R xs := by
  intro Γ
  induction Γ with
  | nil => intro R xs; rfl
  | cons σ Γ ih => intro R xs; exact ih (N.app R (xs .zero)) (Henkin.Env.tail xs)

set_option backward.isDefEq.respectTransparency false in
theorem quotient_faithful (N : Henkin.Model) (hf : Henkin.Faithful N) :
    Henkin.Faithful (quotientModel N) := by
  intro Γ R S h
  apply hf Γ R S
  intro xs w
  have hw := h xs (Quotient.mk _ w)
  change N.truth (Henkin.uncurry (quotientModel N) Γ R xs) w ↔
    N.truth (Henkin.uncurry (quotientModel N) Γ S xs) w at hw
  rw [quotient_uncurry N Γ R xs, quotient_uncurry N Γ S xs] at hw
  exact hw

set_option backward.isDefEq.respectTransparency false in
theorem quotient_comp (N : Henkin.Model) {w : N.World} (hc : Henkin.Comp N w) :
    Henkin.Comp (quotientModel N) (Quotient.mk _ w) := by
  intro Param η Γ p
  change N.truth (Henkin.eval (quotientModel N) η p.comprehension Henkin.Env.nil) w
  rw [quotient_eval]
  exact hc Param η Γ p

/-- The faithful, world-separated canonical presentation constructed from the
actual model. Its object domains remain the original ground root domains. -/
noncomputable def model (M : A.IsModel) (hc : Closed A) (hC5 : C5 A) : Henkin.Model :=
  quotientModel ((rawModel A) M hc hC5)

noncomputable def rootWorld (M : A.IsModel) (hc : Closed A) (hC5 : C5 A) :
    ((model A) M hc hC5).World :=
  Quotient.mk _ ⟨A.W₀, PUnit.unit, 𝟙 A.W₀⟩

theorem model_faithful (M : A.IsModel) (hc : Closed A)
    (hcomp : Comprehension A) (hC5 : C5 A) : Henkin.Faithful ((model A) M hc hC5) :=
  quotient_faithful _ ((rawModel_faithful A) M hc hcomp hC5)

theorem model_worldSeparated (M : A.IsModel) (hc : Closed A) (hC5 : C5 A) :
    Henkin.WorldSeparated ((model A) M hc hC5) :=
  quotient_worldSeparated _

end Classicism.Research.InfinitaryComprehension.Canonical
