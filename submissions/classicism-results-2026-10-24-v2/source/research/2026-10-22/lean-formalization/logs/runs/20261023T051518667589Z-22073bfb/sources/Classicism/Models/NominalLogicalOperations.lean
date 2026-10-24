import Classicism.Models.NominalSupportCore

/-!
# Supported propositions and logical operations

Propositions are exactly all small-supported subsets of the nominal world set.
Quantification ranges over the entire specified nominal domain. In particular,
no completeness of the supported powerset and no choice principle inside the
object language is assumed. Equality is rigid identity; box tests equality with
the everywhere-true proposition, not truth at just the current world.

Source: nominal-choice-classification-20261022.md §§1–2 and
support-bounds-world-geometry-20261022.md construction; local research,
unpaginated, misc. Ordinary classical model metatheory; uncompiled candidate.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

/-- All supported world predicates. -/
def propositions (W : Nom A I) : Nom A I := exponential W (trivialNom A I Prop)

def truthConst (W : Nom A I) (p : Prop) : propositions W :=
  ⟨fun _ => p, ∅, I.empty, fun _ _ => rfl⟩

@[simp] theorem truthConst_fixed (W : Nom A I) (p : Prop) (g : G) :
    (propositions W).obj.act g (truthConst W p) = truthConst W p := Subtype.ext rfl

def truthUnary (W : Nom A I) (op : Prop → Prop) :
    Hom (propositions W) (propositions W) :=
  lift (propositions W) (function W.obj (trivial Prop))
    (fun p w => op (p.val w)) (fun _ _ => rfl)

def truthBinary (W : Nom A I) (op : Prop → Prop → Prop) :
    Hom (productNom (propositions W) (propositions W)) (propositions W) :=
  lift (productNom (propositions W) (propositions W))
    (function W.obj (trivial Prop))
    (fun z w => op (z.1.val w) (z.2.val w)) (fun _ _ => rfl)

/-- Identity of whole domain elements, uniformly at every world. -/
def equality (W X : Nom A I) : Hom (productNom X X) (propositions W) :=
  lift (productNom X X) (function W.obj (trivial Prop))
    (fun z _ => z.1 = z.2) (by
      intro g z
      funext w
      apply propext
      change (X.obj.act g z.1 = X.obj.act g z.2) ↔ z.1 = z.2
      exact ⟨act_injective X.obj g, congrArg (X.obj.act g)⟩)

def forallOp (W X : Nom A I) :
    Hom (exponential X (propositions W)) (propositions W) :=
  lift (exponential X (propositions W)) (function W.obj (trivial Prop))
    (fun f w => ∀ x : X, (f.val x).val w) (by
      intro g f
      funext w
      apply propext
      change (∀ x, (f.val (X.obj.act g⁻¹ x)).val (W.obj.act g⁻¹ w)) ↔
        ∀ x, (f.val x).val (W.obj.act g⁻¹ w)
      constructor
      · intro h x
        simpa only [inv_act] using h (X.obj.act g x)
      · intro h x
        exact h (X.obj.act g⁻¹ x))

def existsOp (W X : Nom A I) :
    Hom (exponential X (propositions W)) (propositions W) :=
  lift (exponential X (propositions W)) (function W.obj (trivial Prop))
    (fun f w => ∃ x : X, (f.val x).val w) (by
      intro g f
      funext w
      apply propext
      change (∃ x, (f.val (X.obj.act g⁻¹ x)).val (W.obj.act g⁻¹ w)) ↔
        ∃ x, (f.val x).val (W.obj.act g⁻¹ w)
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨X.obj.act g⁻¹ x, hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨X.obj.act g x, by simpa only [inv_act] using hx⟩)

/-- The actual rigid equality definition of box. -/
def boxOp (W : Nom A I) : Hom (propositions W) (propositions W) :=
  (equality W (propositions W)).comp
    ((Hom.id _).pair
      (constant _ _ (truthConst W True) (truthConst_fixed W True)))

@[simp] theorem boxOp_at (W : Nom A I) (p : propositions W) (w : W) :
    ((boxOp W).fn p).val w ↔ ∀ v : W, p.val v := by
  change (p = truthConst W True) ↔ _
  constructor
  · intro h v
    rw [h]
    trivial
  · intro h
    apply Subtype.ext
    funext v
    exact propext ⟨fun _ => True.intro, fun _ => h v⟩

/-- The admitted constant function with its parameter's support. -/
def constantFunction (X Y : Nom A I) : Hom Y (exponential X Y) :=
  curry (first Y X)

def postcompose {X Y Z : Nom A I} (f : Hom Y Z) :
    Hom (exponential X Y) (exponential X Z) :=
  curry (f.comp (evaluation X Y))

/-- Pointwise lifting of a binary operation. Both input supports are retained. -/
def pointwise₂ {X Y Z : Nom A I} (f : Hom (productNom Y Y) Z) :
    Hom (productNom (exponential X Y) (exponential X Y)) (exponential X Z) :=
  curry {
    fn := fun z => f.fn (z.1.1.val z.2, z.1.2.val z.2)
    comm := by
      intro g z
      change f.fn
        (Y.obj.act g (z.1.1.val (X.obj.act g⁻¹ (X.obj.act g z.2))),
         Y.obj.act g (z.1.2.val (X.obj.act g⁻¹ (X.obj.act g z.2)))) = _
      rw [inv_act]
      exact f.comm g (z.1.1.val z.2, z.1.2.val z.2)
  }

@[simp] theorem forallOp_at (W X : Nom A I) (f : exponential X (propositions W)) (w : W) :
    ((forallOp W X).fn f).val w ↔ ∀ x, (f.val x).val w := Iff.rfl

@[simp] theorem existsOp_at (W X : Nom A I) (f : exponential X (propositions W)) (w : W) :
    ((existsOp W X).fn f).val w ↔ ∃ x, (f.val x).val w := Iff.rfl

@[simp] theorem equality_at (W X : Nom A I) (x y : X) (w : W) :
    ((equality W X).fn (x, y)).val w ↔ x = y := Iff.rfl

end
end Classicism.Meta.Nominal
