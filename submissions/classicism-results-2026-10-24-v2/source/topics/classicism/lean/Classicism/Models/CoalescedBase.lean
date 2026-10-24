import Classicism.Semantics.Intensional

/-!
# A free root over two one-world intensional premodels

The root individuals (and type variables) are pairs of component individuals.
At every relational type the root has an arbitrary root extension and one admitted
relation from each component. The two outgoing arrows are the coordinate projections.
The components may be Henkin: no external fullness assumption is made on them.

This file constructs only the premodel. Term closure and the transfer of sentence
truth are separate obligations; no model condition is assumed as its own conclusion.
The construction is the two-component coalescence described in the local record
`models/coalesced-two-extensional-arithmetics-root.yaml`, "definition" (unpaginated),
with arbitrary one-world intensional components in place of its arithmetic examples.
-/

namespace Classicism.Meta.Intensional.Coalesced

open CategoryTheory

/-- A singleton category with only its identity arrow. -/
inductive One where
  | point

instance : SmallCategory One where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by intros; apply Subsingleton.elim
  comp_id := by intros; apply Subsingleton.elim
  assoc := by intros; apply Subsingleton.elim

instance (W V : One) : Subsingleton (W ⟶ V) := ⟨fun _ _ => rfl⟩

/-- The free root and its two terminal successors. -/
inductive World where
  | root
  | left
  | right
  deriving DecidableEq

inductive Hom : World → World → Type where
  | rootId : Hom .root .root
  | leftId : Hom .left .left
  | rightId : Hom .right .right
  | toLeft : Hom .root .left
  | toRight : Hom .root .right

def Hom.id : (W : World) → Hom W W
  | .root => .rootId
  | .left => .leftId
  | .right => .rightId

def Hom.comp : {U V W : World} → Hom U V → Hom V W → Hom U W
  | _, _, _, .rootId, g => g
  | _, _, _, .leftId, .leftId => .leftId
  | _, _, _, .rightId, .rightId => .rightId
  | _, _, _, .toLeft, .leftId => .toLeft
  | _, _, _, .toRight, .rightId => .toRight

instance : SmallCategory World where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros X Y f; cases f <;> rfl
  comp_id := by intros X Y f; cases f <;> rfl
  assoc := by intros X Y Z U f g h; cases f <;> cases g <;> cases h <;> rfl

instance (W V : World) : Subsingleton (W ⟶ V) :=
  ⟨by intro f g; cases f <;> cases g <;> rfl⟩

abbrev toLeft : World.root ⟶ World.left := Hom.toLeft
abbrev toRight : World.root ⟶ World.right := Hom.toRight

variable (L R : Premodel Signature.pure One)

/-- The root domains, using the actual mutual type recursor. -/
abbrev RootDom (σ : Ty) : Type :=
  @Ty.rec (fun _ => Type) (fun _ => Type)
    (L.Dom .point .e × R.Dom .point .e)
    (fun ρ A => Set A × L.Dom .point (.rel ρ) × R.Dom .point (.rel ρ))
    (fun i => L.Dom .point (.var i) × R.Dom .point (.var i))
    PUnit (fun _ _ A B => A × B) σ

/-- Arguments at the root, defined together with its domains by the mutual recursor. -/
abbrev RootArgs (ρ : RTy) : Type :=
  @RTy.rec (fun _ => Type) (fun _ => Type)
    (L.Dom .point .e × R.Dom .point .e)
    (fun τ A => Set A × L.Dom .point (.rel τ) × R.Dom .point (.rel τ))
    (fun i => L.Dom .point (.var i) × R.Dom .point (.var i))
    PUnit (fun _ _ A B => A × B) ρ

def leftProj : (σ : Ty) → RootDom L R σ → L.Dom .point σ
  | .e, x => x.1
  | .rel _, x => x.2.1
  | .var _, x => x.1

def rightProj : (σ : Ty) → RootDom L R σ → R.Dom .point σ
  | .e, x => x.2
  | .rel _, x => x.2.2
  | .var _, x => x.2

abbrev Dom (σ : Ty) : World → Type
  | .root => RootDom L R σ
  | .left => L.Dom .point σ
  | .right => R.Dom .point σ

def map (σ : Ty) : {W V : World} → (W ⟶ V) → Dom L R σ W → Dom L R σ V
  | _, _, .rootId, x => x
  | _, _, .leftId, x => x
  | _, _, .rightId, x => x
  | _, _, .toLeft, x => leftProj L R σ x
  | _, _, .toRight, x => rightProj L R σ x

/-- The action at a type: the two component projections and identities. -/
abbrev inner (σ : Ty) : World ⥤ Type where
  obj := Dom L R σ
  map h := TypeCat.ofHom (map L R σ h)
  map_id W := by cases W <;> rfl
  map_comp f g := by cases f <;> cases g <;> rfl

def rootArgsEquiv : (ρ : RTy) → Args (inner L R) ρ .root ≃ RootArgs L R ρ
  | .t => Equiv.refl _
  | .arr _ ρ => Equiv.prodCongr (Equiv.refl _) (rootArgsEquiv ρ)

def leftArgsEquiv : (ρ : RTy) → Args (inner L R) ρ .left ≃ Args L.inner ρ .point
  | .t => Equiv.refl _
  | .arr _ ρ => Equiv.prodCongr (Equiv.refl _) (leftArgsEquiv ρ)

def rightArgsEquiv : (ρ : RTy) → Args (inner L R) ρ .right ≃ Args R.inner ρ .point
  | .t => Equiv.refl _
  | .arr _ ρ => Equiv.prodCongr (Equiv.refl _) (rightArgsEquiv ρ)

/-- A component relation is determined by its sole local extension. -/
def extension (A : Premodel Signature.pure One) (ρ : RTy) (x : A.Dom .point (.rel ρ)) :
    Set (Args A.inner ρ .point) :=
  fun a => A.incl ρ .point x ⟨.point, a, 𝟙 One.point⟩

theorem extension_injective (A : Premodel Signature.pure One) (ρ : RTy) :
    Function.Injective (extension A ρ) := by
  intro x y h
  apply A.incl_injective ρ .point
  funext p
  rcases p with ⟨V, a, k⟩
  cases V
  have hk : k = 𝟙 One.point := Subsingleton.elim _ _
  subst k
  exact congrFun h a

/-- Read the appropriate coordinate along one of the five arrows. -/
def read (ρ : RTy) : (W : World) → Dom L R (.rel ρ) W →
    (V : World) → Args (inner L R) ρ V → (W ⟶ V) → Prop
  | .root, x, .root, a, .rootId => x.1 (rootArgsEquiv L R ρ a)
  | .root, x, .left, a, .toLeft => extension L ρ x.2.1 (leftArgsEquiv L R ρ a)
  | .root, x, .right, a, .toRight => extension R ρ x.2.2 (rightArgsEquiv L R ρ a)
  | .left, x, .left, a, .leftId => extension L ρ x (leftArgsEquiv L R ρ a)
  | .right, x, .right, a, .rightId => extension R ρ x (rightArgsEquiv L R ρ a)

def incl (ρ : RTy) (W : World) (x : (inner L R (.rel ρ)).obj W) :
    Intension (inner L R) ρ W :=
  fun p => read L R ρ W x p.1 p.2.1 p.2.2

@[simp] theorem incl_at_root (ρ : RTy) (x : RootDom L R (.rel ρ))
    (a : Args (inner L R) ρ .root) :
    incl L R ρ .root x ⟨.root, a, 𝟙 World.root⟩ ↔ x.1 (rootArgsEquiv L R ρ a) := Iff.rfl

@[simp] theorem incl_at_left (ρ : RTy) (x : RootDom L R (.rel ρ))
    (a : Args (inner L R) ρ .left) :
    incl L R ρ .root x ⟨.left, a, toLeft⟩ ↔
      extension L ρ x.2.1 (leftArgsEquiv L R ρ a) := Iff.rfl

@[simp] theorem incl_at_right (ρ : RTy) (x : RootDom L R (.rel ρ))
    (a : Args (inner L R) ρ .right) :
    incl L R ρ .root x ⟨.right, a, toRight⟩ ↔
      extension R ρ x.2.2 (rightArgsEquiv L R ρ a) := Iff.rfl

@[simp] theorem incl_left (ρ : RTy) (x : L.Dom .point (.rel ρ))
    (a : Args (inner L R) ρ .left) :
    incl L R ρ .left x ⟨.left, a, 𝟙 World.left⟩ ↔
      extension L ρ x (leftArgsEquiv L R ρ a) := Iff.rfl

@[simp] theorem incl_right (ρ : RTy) (x : R.Dom .point (.rel ρ))
    (a : Args (inner L R) ρ .right) :
    incl L R ρ .right x ⟨.right, a, 𝟙 World.right⟩ ↔
      extension R ρ x (rightArgsEquiv L R ρ a) := Iff.rfl

theorem incl_map (ρ : RTy) {W V : World} (h : W ⟶ V)
    (x : (inner L R (.rel ρ)).obj W) :
    incl L R ρ V ((inner L R (.rel ρ)).map h x) =
      Intension.map (inner L R) h (incl L R ρ W x) := by
  funext p
  rcases p with ⟨U, a, k⟩
  cases h <;> cases k <;> rfl

theorem incl_injective (ρ : RTy) (W : World) : Function.Injective (incl L R ρ W) := by
  intro x y h
  cases W with
  | root =>
    apply Prod.ext
    · funext a
      have e := congrFun h ⟨.root, (rootArgsEquiv L R ρ).symm a, Hom.rootId⟩
      simpa only [incl, read, Equiv.apply_symm_apply] using e
    · apply Prod.ext
      · apply extension_injective L ρ
        funext a
        have e := congrFun h ⟨.left, (leftArgsEquiv L R ρ).symm a, toLeft⟩
        simpa only [incl, read, Equiv.apply_symm_apply] using e
      · apply extension_injective R ρ
        funext a
        have e := congrFun h ⟨.right, (rightArgsEquiv L R ρ).symm a, toRight⟩
        simpa only [incl, read, Equiv.apply_symm_apply] using e
  | left =>
    apply extension_injective L ρ
    funext a
    have e := congrFun h ⟨.left, (leftArgsEquiv L R ρ).symm a, Hom.leftId⟩
    simpa only [incl, read, Equiv.apply_symm_apply] using e
  | right =>
    apply extension_injective R ρ
    funext a
    have e := congrFun h ⟨.right, (rightArgsEquiv L R ρ).symm a, Hom.rightId⟩
    simpa only [incl, read, Equiv.apply_symm_apply] using e

/-- The premodel; neither component fullness nor component term closure is needed here. -/
abbrev model : Premodel Signature.pure World where
  W₀ := .root
  inner := inner L R
  nonempty_e W := by
    cases W with
    | root =>
      obtain ⟨l⟩ := L.nonempty_e .point
      obtain ⟨r⟩ := R.nonempty_e .point
      exact ⟨(l, r)⟩
    | left => exact L.nonempty_e .point
    | right => exact R.nonempty_e .point
  incl := incl L R
  incl_map := incl_map L R
  incl_injective := incl_injective L R
  I c := nomatch c

theorem leftProj_surjective (hne : ∀ σ, Nonempty (R.Dom .point σ)) (σ : Ty) :
    Function.Surjective (leftProj L R σ) := by
  intro x
  obtain ⟨y⟩ := hne σ
  cases σ with
  | e => exact ⟨(x, y), rfl⟩
  | rel ρ => exact ⟨(∅, x, y), rfl⟩
  | var i => exact ⟨(x, y), rfl⟩

theorem rightProj_surjective (hne : ∀ σ, Nonempty (L.Dom .point σ)) (σ : Ty) :
    Function.Surjective (rightProj L R σ) := by
  intro x
  obtain ⟨y⟩ := hne σ
  cases σ with
  | e => exact ⟨(y, x), rfl⟩
  | rel ρ => exact ⟨(∅, y, x), rfl⟩
  | var i => exact ⟨(y, x), rfl⟩

theorem map_surjective
    (hL : ∀ σ, Nonempty (L.Dom .point σ))
    (hR : ∀ σ, Nonempty (R.Dom .point σ))
    (σ : Ty) {W V : World} (h : W ⟶ V) :
    Function.Surjective ((inner L R σ).map h) := by
  cases h with
  | rootId => exact Function.surjective_id
  | leftId => exact Function.surjective_id
  | rightId => exact Function.surjective_id
  | toLeft => exact leftProj_surjective L R hR σ
  | toRight => exact rightProj_surjective L R hL σ

/-! The terminal-leaf tuple and outer-domain conversions used by term evaluation. -/

def leftTupleTo (ρ : RTy) : Tuple (inner L R) ρ .left → Tuple L.inner ρ .point
  | ⟨.left, a, .leftId⟩ => ⟨.point, leftArgsEquiv L R ρ a, 𝟙 One.point⟩

def leftTupleFrom (ρ : RTy) : Tuple L.inner ρ .point → Tuple (inner L R) ρ .left
  | ⟨.point, a, _⟩ => ⟨.left, (leftArgsEquiv L R ρ).symm a, Hom.leftId⟩

def rightTupleTo (ρ : RTy) : Tuple (inner L R) ρ .right → Tuple R.inner ρ .point
  | ⟨.right, a, .rightId⟩ => ⟨.point, rightArgsEquiv L R ρ a, 𝟙 One.point⟩

def rightTupleFrom (ρ : RTy) : Tuple R.inner ρ .point → Tuple (inner L R) ρ .right
  | ⟨.point, a, _⟩ => ⟨.right, (rightArgsEquiv L R ρ).symm a, Hom.rightId⟩

def leftTupleEquiv (ρ : RTy) : Tuple (inner L R) ρ .left ≃ Tuple L.inner ρ .point where
  toFun := leftTupleTo L R ρ
  invFun := leftTupleFrom L R ρ
  left_inv p := by
    rcases p with ⟨V, a, h⟩
    cases h
    simp only [leftTupleTo, leftTupleFrom, Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨V, a, h⟩
    cases V
    have hh : h = 𝟙 One.point := Subsingleton.elim _ _
    subst h
    simp only [leftTupleTo, leftTupleFrom, Equiv.apply_symm_apply]

def rightTupleEquiv (ρ : RTy) : Tuple (inner L R) ρ .right ≃ Tuple R.inner ρ .point where
  toFun := rightTupleTo L R ρ
  invFun := rightTupleFrom L R ρ
  left_inv p := by
    rcases p with ⟨V, a, h⟩
    cases h
    simp only [rightTupleTo, rightTupleFrom, Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨V, a, h⟩
    cases V
    have hh : h = 𝟙 One.point := Subsingleton.elim _ _
    subst h
    simp only [rightTupleTo, rightTupleFrom, Equiv.apply_symm_apply]

/-- Transport predicates along an equivalence, with both inverses explicit. -/
def setEquiv {α β : Type} (e : α ≃ β) : Set α ≃ Set β where
  toFun S := fun b => S (e.symm b)
  invFun T := fun a => T (e a)
  left_inv S := by funext a; simp only [Equiv.symm_apply_apply]
  right_inv T := by funext b; simp only [Equiv.apply_symm_apply]

def leftOuter : (σ : Ty) → Outer (inner L R) σ .left ≃ Outer L.inner σ .point
  | .e => Equiv.refl _
  | .rel ρ => setEquiv (leftTupleEquiv L R ρ)
  | .var _ => Equiv.refl _

def rightOuter : (σ : Ty) → Outer (inner L R) σ .right ≃ Outer R.inner σ .point
  | .e => Equiv.refl _
  | .rel ρ => setEquiv (rightTupleEquiv L R ρ)
  | .var _ => Equiv.refl _

@[simp] theorem leftOuter_Incl (σ : Ty) (x : L.Dom .point σ) :
    leftOuter L R σ ((model L R).Incl σ .left x) = L.Incl σ .point x := by
  cases σ with
  | e => rfl
  | var i => rfl
  | rel ρ =>
    funext p
    rcases p with ⟨V, a, h⟩
    cases V
    have hh : h = 𝟙 One.point := Subsingleton.elim _ _
    subst h
    change extension L ρ x (leftArgsEquiv L R ρ ((leftArgsEquiv L R ρ).symm a)) =
      extension L ρ x a
    rw [Equiv.apply_symm_apply]

@[simp] theorem rightOuter_Incl (σ : Ty) (x : R.Dom .point σ) :
    rightOuter L R σ ((model L R).Incl σ .right x) = R.Incl σ .point x := by
  cases σ with
  | e => rfl
  | var i => rfl
  | rel ρ =>
    funext p
    rcases p with ⟨V, a, h⟩
    cases V
    have hh : h = 𝟙 One.point := Subsingleton.elim _ _
    subst h
    change extension R ρ x (rightArgsEquiv L R ρ ((rightArgsEquiv L R ρ).symm a)) =
      extension R ρ x a
    rw [Equiv.apply_symm_apply]

#print axioms model
#print axioms incl_map
#print axioms incl_injective
#print axioms map_surjective
#print axioms leftOuter_Incl
#print axioms rightOuter_Incl

end Classicism.Meta.Intensional.Coalesced
