import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable

/-!
# Support ideals and supported function spaces

Ordinary ZFC-style metatheory for model_interpretation.02 and .03. The only
ideal closure required here is empty set, subsets, binary unions and translated
images. No regularity, countable-union closure or selector theorem is assumed.
Both finite and countable support ideals are constructed explicitly.

Sources: nominal-choice-classification-20261022.md §§1–3 and
support-bounds-world-geometry-20261022.md introductory construction, §§1,4;
original local research, unpaginated, misc. This is typed-domain infrastructure,
not yet a C soundness or classification certificate.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {G : Type} [Group G]

structure Action (G : Type) [Group G] where
  Carrier : Type
  act : G → Carrier → Carrier
  one_act : ∀ x, act 1 x = x
  mul_act : ∀ g h x, act (g * h) x = act g (act h x)

instance : CoeSort (Action G) Type := ⟨Action.Carrier⟩

@[simp] theorem inv_act (X : Action G) (g : G) (x : X) :
    X.act g⁻¹ (X.act g x) = x := by
  rw [← X.mul_act]
  simp [X.one_act]

@[simp] theorem act_inv (X : Action G) (g : G) (x : X) :
    X.act g (X.act g⁻¹ x) = x := by
  rw [← X.mul_act]
  simp [X.one_act]

theorem act_injective (X : Action G) (g : G) : Function.Injective (X.act g) := by
  intro x y h
  have h' := congrArg (X.act g⁻¹) h
  simpa only [inv_act] using h'

def trivial (E : Type) : Action G := ⟨E, fun _ x => x, fun _ => rfl, fun _ _ _ => rfl⟩

@[reducible] def product (X Y : Action G) : Action G where
  Carrier := X × Y
  act g z := (X.act g z.1, Y.act g z.2)
  one_act z := by cases z; simp [X.one_act, Y.one_act]
  mul_act g h z := by cases z; simp [X.mul_act, Y.mul_act]

def function (X Y : Action G) : Action G where
  Carrier := X → Y
  act g f := fun x => Y.act g (f (X.act g⁻¹ x))
  one_act f := by funext x; simp [X.one_act, Y.one_act]
  mul_act g h f := by funext x; simp [X.mul_act, Y.mul_act]

def Fixes (A : Action G) (S : Set A) (g : G) : Prop := ∀ a ∈ S, A.act g a = a

def Supports (A X : Action G) (S : Set A) (x : X) : Prop :=
  ∀ g, Fixes A S g → X.act g x = x

structure SupportIdeal (A : Action G) where
  Small : Set A → Prop
  empty : Small ∅
  subset : ∀ {S T}, S ⊆ T → Small T → Small S
  union : ∀ {S T}, Small S → Small T → Small (S ∪ T)
  image : ∀ (g : G) {S}, Small S → Small (A.act g '' S)

def finiteIdeal (A : Action G) : SupportIdeal A where
  Small S := S.Finite
  empty := Set.finite_empty
  subset h hT := hT.subset h
  union hS hT := hS.union hT
  image g {S} hS := hS.image (A.act g)

def countableIdeal (A : Action G) : SupportIdeal A where
  Small S := S.Countable
  empty := Set.countable_empty
  subset h hT := hT.mono h
  union hS hT := hS.union hT
  image g {S} hS := hS.image (A.act g)

theorem supports_mono (A X : Action G) {S T : Set A} {x : X}
    (hST : S ⊆ T) (hx : Supports A X S x) : Supports A X T x :=
  fun g hg => hx g (fun a ha => hg a (hST ha))

theorem supports_translate (A X : Action G) {S : Set A} {x : X}
    (hx : Supports A X S x) (g : G) : Supports A X (A.act g '' S) (X.act g x) := by
  intro h hh
  have hk : Fixes A S (g⁻¹ * h * g) := by
    intro a ha
    have he := hh (A.act g a) ⟨a, ha, rfl⟩
    simpa only [A.mul_act, inv_act] using congrArg (A.act g⁻¹) he
  have he := hx (g⁻¹ * h * g) hk
  have he' := congrArg (X.act g) he
  simpa only [X.mul_act, act_inv] using he'

def Supported (A X : Action G) (I : SupportIdeal A) (x : X) : Prop :=
  ∃ S, I.Small S ∧ Supports A X S x

theorem supported_translate (A X : Action G) (I : SupportIdeal A)
    {x : X} (hx : Supported A X I x) (g : G) : Supported A X I (X.act g x) := by
  obtain ⟨S, hS, hs⟩ := hx
  exact ⟨A.act g '' S, I.image g hS, supports_translate A X hs g⟩

structure Nom (A : Action G) (I : SupportIdeal A) where
  obj : Action G
  supported : ∀ x : obj, Supported A obj I x

instance {A : Action G} {I : SupportIdeal A} : CoeSort (Nom A I) Type :=
  ⟨fun X => X.obj.Carrier⟩

def partAction (A X : Action G) (I : SupportIdeal A) : Action G where
  Carrier := {x : X // Supported A X I x}
  act g x := ⟨X.act g x.val, supported_translate A X I x.property g⟩
  one_act x := Subtype.ext (X.one_act x.val)
  mul_act g h x := Subtype.ext (X.mul_act g h x.val)

/-- All and only supported elements; not a selected Henkin subcollection. -/
def part (A X : Action G) (I : SupportIdeal A) : Nom A I where
  obj := partAction A X I
  supported x := by
    obtain ⟨S, hS, hx⟩ := x.property
    exact ⟨S, hS, fun g hg => Subtype.ext (hx g hg)⟩

def trivialNom (A : Action G) (I : SupportIdeal A) (E : Type) : Nom A I where
  obj := trivial E
  supported x := ⟨∅, I.empty, fun _ _ => rfl⟩

@[reducible] def productNom {A : Action G} {I : SupportIdeal A} (X Y : Nom A I) : Nom A I where
  obj := product X.obj Y.obj
  supported z := by
    obtain ⟨S, hS, hs⟩ := X.supported z.1
    obtain ⟨T, hT, ht⟩ := Y.supported z.2
    refine ⟨S ∪ T, I.union hS hT, ?_⟩
    intro g hg
    have hx := hs g (fun a ha => hg a (Or.inl ha))
    have hy := ht g (fun a ha => hg a (Or.inr ha))
    exact Prod.ext hx hy

/-- Every supported external function, with conjugation action. -/
def exponential {A : Action G} {I : SupportIdeal A} (X Y : Nom A I) : Nom A I :=
  part A (function X.obj Y.obj) I

structure Hom {A : Action G} {I : SupportIdeal A} (X Y : Nom A I) where
  fn : X → Y
  comm : ∀ g x, fn (X.obj.act g x) = Y.obj.act g (fn x)

def Hom.id {A : Action G} {I : SupportIdeal A} (X : Nom A I) : Hom X X :=
  ⟨fun x => x, fun _ _ => rfl⟩

def Hom.comp {A : Action G} {I : SupportIdeal A} {X Y Z : Nom A I}
    (f : Hom Y Z) (h : Hom X Y) : Hom X Z :=
  ⟨fun x => f.fn (h.fn x), fun g x => by rw [h.comm, f.comm]⟩

def Hom.pair {A : Action G} {I : SupportIdeal A} {X Y Z : Nom A I}
    (f : Hom X Y) (h : Hom X Z) : Hom X (productNom Y Z) :=
  ⟨fun x => (f.fn x, h.fn x), fun g x => Prod.ext (f.comm g x) (h.comm g x)⟩

def first {A : Action G} {I : SupportIdeal A} (X Y : Nom A I) : Hom (productNom X Y) X :=
  ⟨Prod.fst, fun _ _ => rfl⟩

def second {A : Action G} {I : SupportIdeal A} (X Y : Nom A I) : Hom (productNom X Y) Y :=
  ⟨Prod.snd, fun _ _ => rfl⟩

def exchange {A : Action G} {I : SupportIdeal A} (X Y : Nom A I) :
    Hom (productNom X Y) (productNom Y X) := ⟨Prod.swap, fun _ _ => rfl⟩

theorem function_support_iff {A : Action G} {I : SupportIdeal A} (X Y : Nom A I)
    (S : Set A) (f : X → Y) : Supports A (function X.obj Y.obj) S f ↔
      ∀ g, Fixes A S g → ∀ x, f (X.obj.act g x) = Y.obj.act g (f x) := by
  constructor
  · intro hs g hg x
    have he := congrFun (hs g hg) (X.obj.act g x)
    change Y.obj.act g (f (X.obj.act g⁻¹ (X.obj.act g x))) = f (X.obj.act g x) at he
    rw [inv_act] at he
    exact he.symm
  · intro hs g hg
    funext x
    have he := hs g hg (X.obj.act g⁻¹ x)
    rw [act_inv] at he
    exact he.symm

def evaluation {A : Action G} {I : SupportIdeal A} (X Y : Nom A I) :
    Hom (productNom (exponential X Y) X) Y where
  fn z := z.1.val z.2
  comm g z := by
    change Y.obj.act g (z.1.val (X.obj.act g⁻¹ (X.obj.act g z.2))) = _
    rw [inv_act]

/-- Lambda closure with a supported parameter: the parameter's support suffices. -/
def curry {A : Action G} {I : SupportIdeal A} {X Y Z : Nom A I}
    (f : Hom (productNom Z X) Y) : Hom Z (exponential X Y) where
  fn z := ⟨fun x => f.fn (z, x), by
    obtain ⟨S, hS, hz⟩ := Z.supported z
    refine ⟨S, hS, (function_support_iff X Y S _).2 ?_⟩
    intro g hg x
    have he := f.comm g (z, x)
    change f.fn (Z.obj.act g z, X.obj.act g x) = Y.obj.act g (f.fn (z, x)) at he
    rw [hz g hg] at he
    exact he⟩
  comm g z := by
    apply Subtype.ext
    funext x
    have he := f.comm g (z, X.obj.act g⁻¹ x)
    change f.fn (Z.obj.act g z, X.obj.act g (X.obj.act g⁻¹ x)) = _ at he
    rw [act_inv] at he
    exact he

@[simp] theorem curry_beta {A : Action G} {I : SupportIdeal A} {X Y Z : Nom A I}
    (f : Hom (productNom Z X) Y) (z : Z) (x : X) :
    ((curry f).fn z).val x = f.fn (z, x) := rfl

/-- A globally equivariant function is an admitted empty-supported operation. -/
def element {A : Action G} {I : SupportIdeal A} {X Y : Nom A I} (f : Hom X Y) : exponential X Y :=
  ⟨f.fn, ∅, I.empty, (function_support_iff X Y ∅ f.fn).2 (fun g _ x => f.comm g x)⟩

theorem element_fixed {A : Action G} {I : SupportIdeal A} {X Y : Nom A I}
    (f : Hom X Y) (g : G) : (exponential X Y).obj.act g (element f) = element f := by
  apply Subtype.ext
  exact (function_support_iff X Y ∅ f.fn).2 (fun g _ x => f.comm g x) g (fun _ h => h.elim)

def constant {A : Action G} {I : SupportIdeal A} (X Y : Nom A I) (y : Y)
    (hy : ∀ g, Y.obj.act g y = y) : Hom X Y := ⟨fun _ => y, fun g _ => (hy g).symm⟩

/-- An equivariant raw operation sends supported inputs to supported outputs. -/
def lift {A : Action G} {I : SupportIdeal A} (X : Nom A I) (Y : Action G)
    (f : X → Y) (hf : ∀ g x, f (X.obj.act g x) = Y.act g (f x)) : Hom X (part A Y I) where
  fn x := ⟨f x, by
    obtain ⟨S, hS, hx⟩ := X.supported x
    refine ⟨S, hS, ?_⟩
    intro g hg
    rw [← hf, hx g hg]⟩
  comm g x := Subtype.ext (hf g x)

end
end Classicism.Meta.Nominal
