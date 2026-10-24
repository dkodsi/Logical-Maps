import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Boolean-valued equality and coherent predicate spaces

Original supporting formalization (misc), 23 October 2026, of the direct
Boolean-valued typed construction in
`research/2026-10-23/boolean-valued-finite-choice.md`, sections 3--4
(unpaginated).

These are actual equality-space and predicate-space constructors over a
complete Boolean algebra. Equality is total but can have intermediate Boolean
values. No separation, nonemptiness, mixing, finite support, model existence,
or Choice principle is assumed. Finite-support restrictions and the typed
model construction are separate obligations.
-/

namespace Classicism.Meta.ChoiceBoolean

universe u v w z

variable {B : Type u} [CompleteBooleanAlgebra B]

/-- The Boolean value of equivalence. -/
def iffValue (a b : B) : B := (a ⇨ b) ⊓ (b ⇨ a)

theorem le_iffValue_iff {q a b : B} :
    q ≤ iffValue a b ↔ q ⊓ a ≤ b ∧ q ⊓ b ≤ a := by
  rw [iffValue, le_inf_iff, le_himp_iff, le_himp_iff]

@[simp] theorem iffValue_refl (a : B) : iffValue a a = ⊤ := by
  simp [iffValue]

theorem iffValue_symm (a b : B) : iffValue a b = iffValue b a := by
  exact inf_comm _ _

theorem iffValue_trans (a b c : B) :
    iffValue a b ⊓ iffValue b c ≤ iffValue a c := by
  apply le_inf
  · exact (inf_le_inf inf_le_left inf_le_left).trans (himp_triangle a b c)
  · calc
      iffValue a b ⊓ iffValue b c ≤ (b ⇨ a) ⊓ (c ⇨ b) :=
        inf_le_inf inf_le_right inf_le_right
      _ = (c ⇨ b) ⊓ (b ⇨ a) := inf_comm _ _
      _ ≤ c ⇨ a := himp_triangle c b a

theorem iffValue_inf_left (a b : B) : iffValue a b ⊓ a ≤ b :=
  (le_iffValue_iff.mp le_rfl).1

theorem iffValue_inf_right (a b : B) : iffValue a b ⊓ b ≤ a :=
  (le_iffValue_iff.mp le_rfl).2

/-- Equivalence below a Boolean condition is equality after restriction. -/
theorem le_iffValue_iff_inf_eq {q a b : B} :
    q ≤ iffValue a b ↔ q ⊓ a = q ⊓ b := by
  constructor
  · intro h
    obtain ⟨hab, hba⟩ := le_iffValue_iff.mp h
    exact le_antisymm (le_inf inf_le_left hab) (le_inf inf_le_left hba)
  · intro h
    exact le_iffValue_iff.mpr
      ⟨h.le.trans inf_le_right, h.symm.le.trans inf_le_right⟩

theorem iffValue_eq_top_iff {a b : B} : iffValue a b = ⊤ ↔ a = b := by
  constructor
  · intro h
    have hh : (⊤ : B) ≤ iffValue a b := h.ge
    simpa only [top_inf_eq] using le_iffValue_iff_inf_eq.mp hh
  · intro h
    subst b
    exact iffValue_refl a

/-- A set with total Boolean-valued equality. This does not assert mixing. -/
structure EqualitySpace (B : Type u) [CompleteBooleanAlgebra B] where
  Carrier : Type v
  eqv : Carrier → Carrier → B
  refl : ∀ x, eqv x x = ⊤
  symm : ∀ x y, eqv x y = eqv y x
  trans : ∀ x y z, eqv x y ⊓ eqv y z ≤ eqv x z

/-- A predicate respects equality at every Boolean degree. -/
def Coherent (X : EqualitySpace.{u, v} B) (f : X.Carrier → B) : Prop :=
  ∀ x y, X.eqv x y ⊓ f x ≤ f y

theorem coherent_iff (X : EqualitySpace.{u, v} B) (f : X.Carrier → B) :
    Coherent X f ↔ ∀ x y, X.eqv x y ≤ iffValue (f x) (f y) := by
  constructor
  · intro hf x y
    apply le_iffValue_iff.mpr
    refine ⟨hf x y, ?_⟩
    rw [X.symm x y]
    exact hf y x
  · intro hf x y
    exact (le_iffValue_iff.mp (hf x y)).1

/-- A coherent predicate, retaining its actual function. -/
structure Predicate (X : EqualitySpace.{u, v} B) where
  toFun : X.Carrier → B
  coherent : Coherent X toFun

instance {X : EqualitySpace.{u, v} B} :
    CoeFun (Predicate X) (fun _ => X.Carrier → B) := ⟨Predicate.toFun⟩

theorem Predicate.ext {X : EqualitySpace.{u, v} B} {f g : Predicate X}
    (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      subst g
      rfl

theorem Predicate.congr {X : EqualitySpace.{u, v} B} (f : Predicate X)
    (x y : X.Carrier) : X.eqv x y ≤ iffValue (f x) (f y) :=
  (coherent_iff X f.toFun).mp f.coherent x y

/-- Ordinary crisp equality is one concrete equality-space constructor. -/
noncomputable def crispSpace (A : Type v) : EqualitySpace.{u, v} B := by
  classical
  exact
    { Carrier := A
      eqv := fun x y => if x = y then ⊤ else ⊥
      refl := by intro x; simp
      symm := by intro x y; simp only [eq_comm]
      trans := by
        intro x y z
        by_cases hxy : x = y
        · subst y
          simp
        · simp [hxy] }

/-- Boolean values themselves, with equivalence as equality. -/
def truthSpace : EqualitySpace.{u, u} B where
  Carrier := B
  eqv := iffValue
  refl := iffValue_refl
  symm := iffValue_symm
  trans := iffValue_trans

/-- Binary tuples use the meet of their component equality values. -/
def prod (X : EqualitySpace.{u, v} B) (Y : EqualitySpace.{u, w} B) :
    EqualitySpace.{u, max v w} B where
  Carrier := X.Carrier × Y.Carrier
  eqv p q := X.eqv p.1 q.1 ⊓ Y.eqv p.2 q.2
  refl p := by rw [X.refl, Y.refl, inf_top_eq]
  symm p q := by rw [X.symm p.1 q.1, Y.symm p.2 q.2]
  trans p q r :=
    le_inf
      ((inf_le_inf inf_le_left inf_le_left).trans (X.trans p.1 q.1 r.1))
      ((inf_le_inf inf_le_right inf_le_right).trans (Y.trans p.2 q.2 r.2))

/-- The equality space of all coherent predicates on an equality space. -/
def predicateSpace (X : EqualitySpace.{u, v} B) :
    EqualitySpace.{u, max u v} B where
  Carrier := Predicate X
  eqv f g := ⨅ x, iffValue (f x) (g x)
  refl f := by simp
  symm f g := by
    apply iInf_congr
    intro x
    exact iffValue_symm (f x) (g x)
  trans f g h := by
    apply le_iInf
    intro x
    exact (inf_le_inf (iInf_le _ x) (iInf_le _ x)).trans
      (iffValue_trans (f x) (g x) (h x))

theorem predicateEq_le {X : EqualitySpace.{u, v} B} (f g : Predicate X)
    (x : X.Carrier) :
    (predicateSpace X).eqv f g ≤ iffValue (f x) (g x) :=
  iInf_le _ x

/-- Predicate equality is separated even when the input space is not. -/
theorem predicateEq_eq_top_iff {X : EqualitySpace.{u, v} B} {f g : Predicate X} :
    (predicateSpace X).eqv f g = ⊤ ↔ f = g := by
  constructor
  · intro h
    apply Predicate.ext
    intro x
    apply iffValue_eq_top_iff.mp
    exact top_le_iff.mp (h.ge.trans (predicateEq_le f g x))
  · intro h
    subst g
    exact (predicateSpace X).refl f

/-- Evaluation simultaneously respects predicate and argument equality. -/
theorem eval_subst {X : EqualitySpace.{u, v} B} (f g : Predicate X)
    (x y : X.Carrier) :
    ((predicateSpace X).eqv f g ⊓ X.eqv x y) ⊓ f x ≤ g y := by
  have hfg : (predicateSpace X).eqv f g ⊓ f x ≤ g x :=
    (inf_le_inf_right _ (predicateEq_le f g x)).trans
      (iffValue_inf_left (f x) (g x))
  calc
    ((predicateSpace X).eqv f g ⊓ X.eqv x y) ⊓ f x
        ≤ X.eqv x y ⊓ g x :=
      le_inf (inf_le_left.trans inf_le_right)
        ((inf_le_inf_right _ inf_le_left).trans hfg)
    _ ≤ g y := g.coherent x y

theorem eval_congr {X : EqualitySpace.{u, v} B} (f g : Predicate X)
    (x y : X.Carrier) :
    (predicateSpace X).eqv f g ⊓ X.eqv x y ≤ iffValue (f x) (g y) := by
  apply le_iffValue_iff.mpr
  refine ⟨eval_subst f g x y, ?_⟩
  rw [(predicateSpace X).symm f g, X.symm x y]
  exact eval_subst g f y x

/-- Evaluation is itself an actual coherent binary predicate. -/
def evaluation (X : EqualitySpace.{u, v} B) :
    Predicate (prod (predicateSpace X) X) where
  toFun p := (p.1 : Predicate X).toFun p.2
  coherent p q := eval_subst (p.1 : Predicate X) (q.1 : Predicate X) p.2 q.2

namespace Predicate

variable {X : EqualitySpace.{u, v} B}

def const (b : B) : Predicate X where
  toFun _ := b
  coherent _ _ := inf_le_right

/-- Negation preserves coherence; symmetry supplies the reverse substitution. -/
def neg (f : Predicate X) : Predicate X where
  toFun x := (f x)ᶜ
  coherent x y := by
    change X.eqv x y ⊓ (f x)ᶜ ≤ (f y)ᶜ
    rw [← himp_bot (f y), le_himp_iff]
    have hrev : X.eqv x y ⊓ f y ≤ f x := by
      rw [X.symm x y]
      exact f.coherent y x
    calc
      (X.eqv x y ⊓ (f x)ᶜ) ⊓ f y
          = (X.eqv x y ⊓ f y) ⊓ (f x)ᶜ := inf_right_comm _ _ _
      _ ≤ f x ⊓ (f x)ᶜ := inf_le_inf_right _ hrev
      _ = ⊥ := inf_compl_eq_bot'

/-- Pointwise arbitrary meets of coherent predicates remain coherent. -/
def all {I : Type z} (f : I → Predicate X) : Predicate X where
  toFun x := ⨅ i, f i x
  coherent x y := by
    apply le_iInf
    intro i
    exact (inf_le_inf_left _ (iInf_le _ i)).trans ((f i).coherent x y)

/-- Pointwise arbitrary joins of coherent predicates remain coherent. -/
def ex {I : Type z} (f : I → Predicate X) : Predicate X where
  toFun x := ⨆ i, f i x
  coherent x y := by
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    exact ((f i).coherent x y).trans (le_iSup (fun j => f j y) i)

/-- Restricting the first argument gives an actual predicate on the second. -/
def sectionLeft {Y : EqualitySpace.{u, w} B}
    (f : Predicate (prod X Y)) (x : X.Carrier) : Predicate Y where
  toFun y := f (x, y)
  coherent y z := by
    have h := f.coherent (x, y) (x, z)
    simpa only [prod, X.refl, top_inf_eq] using h

/-- Restricting the second argument gives an actual predicate on the first. -/
def sectionRight {Y : EqualitySpace.{u, w} B}
    (f : Predicate (prod X Y)) (y : Y.Carrier) : Predicate X where
  toFun x := f (x, y)
  coherent x z := by
    have h := f.coherent (x, y) (z, y)
    simpa only [prod, Y.refl, inf_top_eq] using h

/-- Currying respects equality in its remaining argument. -/
theorem sectionLeft_congr {Y : EqualitySpace.{u, w} B}
    (f : Predicate (prod X Y)) (x z : X.Carrier) :
    X.eqv x z ≤ (predicateSpace Y).eqv (sectionLeft f x) (sectionLeft f z) := by
  apply le_iInf
  intro y
  have h := f.congr (x, y) (z, y)
  simpa only [prod, Y.refl, inf_top_eq, sectionLeft] using h

/-- Universal quantification in the second argument. -/
def forallRight {Y : EqualitySpace.{u, w} B}
    (f : Predicate (prod X Y)) : Predicate X :=
  all (sectionRight f)

/-- Existential quantification in the second argument. -/
def existsRight {Y : EqualitySpace.{u, w} B}
    (f : Predicate (prod X Y)) : Predicate X :=
  ex (sectionRight f)

end Predicate

end Classicism.Meta.ChoiceBoolean
