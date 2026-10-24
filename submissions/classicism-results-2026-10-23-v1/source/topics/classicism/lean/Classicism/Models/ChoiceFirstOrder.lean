import Classicism.Semantics.IntensionalSoundness

/-!
# A first-order relational presentation of one-world typed hierarchies

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/finite-choice-forcing-extraction-review.md` sections 2--3
(unpaginated). This is the relational presentation of E₂: each relational
sort has a predicate for its finite tuple of arguments. A block quantifier
below binds only that finite tuple of existing sorts. It is ordinary
many-sorted first-order syntax, not quantification over predicates or types.

The structure embeds into the project's actual intensional `Premodel`.
First-order comprehension is stated on the explicit syntax; it is not an
assumption of term closure or `Premodel.IsModel`. The term-interpretation
bridge is developed in `ChoiceFirstOrderTerms`. No forcing model or Choice
failure is asserted here.
-/

namespace Classicism.Meta.ChoiceFirstOrder

open CategoryTheory

/-- A category with one object and one arrow. -/
inductive World where
  | star

instance : SmallCategory World where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc _ _ _ := rfl

/-- The constant action; no nontrivial action on any sort is introduced. -/
def action (X : Type) : World ⥤ Type where
  obj _ := X
  map _ := 𝟙 X
  map_id _ := rfl
  map_comp _ _ := rfl

def inner (D : Ty → Type) (σ : Ty) : World ⥤ Type := action (D σ)

/-- The actual finite argument tuple used by the existing intensional semantics. -/
abbrev Args (D : Ty → Type) (ρ : RTy) : Type :=
  Intensional.Args (inner D) ρ World.star

def mapArgs {D E : Ty → Type} (f : ∀ σ, D σ → E σ) :
    ∀ ρ, Args D ρ → Args E ρ
  | .t, _ => PUnit.unit
  | .arr σ ρ, a => (f σ a.1, mapArgs f ρ a.2)

theorem mapArgs_id (D : Ty → Type) : ∀ ρ (a : Args D ρ),
    mapArgs (fun _ x => x) ρ a = a
  | .t, a => by cases a; rfl
  | .arr _ ρ, a => by
    change (a.1, mapArgs (fun _ x => x) ρ a.2) = a
    rw [mapArgs_id D ρ a.2]

theorem mapArgs_comp {D E F : Ty → Type}
    (f : ∀ σ, D σ → E σ) (g : ∀ σ, E σ → F σ) :
    ∀ ρ (a : Args D ρ),
      mapArgs g ρ (mapArgs f ρ a) = mapArgs (fun σ x => g σ (f σ x)) ρ a
  | .t, _ => rfl
  | .arr σ ρ, a => by
    change (g σ (f σ a.1), mapArgs g ρ (mapArgs f ρ a.2)) =
      (g σ (f σ a.1), mapArgs (fun τ x => g τ (f τ x)) ρ a.2)
    rw [mapArgs_comp f g ρ a.2]

/-- Turn the finite tuple into the existing typed assignment. -/
def argsEnv {D : Ty → Type} : ∀ ρ, Args D ρ → IEnv D ρ.args
  | .t, _ => .nil
  | .arr _ ρ, a => .cons a.1 (argsEnv ρ a.2)

/-- Variables bound by a finite argument block. -/
abbrev BlockVars (ρ : RTy) (σ : Ty) := Var ρ.args σ

def blockArgs : ∀ ρ, Args (BlockVars ρ) ρ
  | .t => PUnit.unit
  | .arr _ ρ => (.zero, mapArgs (fun _ v => Var.succ v) ρ (blockArgs ρ))

theorem mapArgs_block {D : Ty → Type} : ∀ ρ (a : Args D ρ),
    mapArgs (fun _ v => (argsEnv ρ a).get v) ρ (blockArgs ρ) = a
  | .t, a => by cases a; rfl
  | .arr σ ρ, a => by
    change (a.1, mapArgs
      (fun (τ : Ty) (v : Var (σ :: ρ.args) τ) =>
        IEnv.get v (IEnv.cons a.1 (argsEnv ρ a.2))) ρ
      (mapArgs (fun (τ : Ty) (v : Var ρ.args τ) => Var.succ v) ρ
        (blockArgs ρ))) = (a.1, a.2)
    rw [mapArgs_comp]
    change (a.1, mapArgs (fun _ v => IEnv.get v (argsEnv ρ a.2)) ρ
      (blockArgs ρ)) = (a.1, a.2)
    rw [mapArgs_block ρ a.2]

abbrev Extend (V : Ty → Type) (ρ : RTy) (σ : Ty) := V σ ⊕ BlockVars ρ σ

def liftVars {V : Ty → Type} (ρ : RTy) : ∀ σ, V σ → Extend V ρ σ :=
  fun _ => Sum.inl

def boundArgs (V : Ty → Type) (ρ : RTy) : Args (Extend V ρ) ρ :=
  mapArgs (fun _ => Sum.inr) ρ (blockArgs ρ)

def extendEnv {V D : Ty → Type} (η : ∀ σ, V σ → D σ)
    (ρ : RTy) (a : Args D ρ) : ∀ σ, Extend V ρ σ → D σ :=
  fun σ v => v.elim (η σ) (fun w => IEnv.get w (argsEnv ρ a))

theorem eval_boundArgs {V D : Ty → Type} (η : ∀ σ, V σ → D σ)
    (ρ : RTy) (a : Args D ρ) :
    mapArgs (extendEnv η ρ a) ρ (boundArgs V ρ) = a := by
  rw [boundArgs, mapArgs_comp]
  exact mapArgs_block ρ a

theorem eval_liftArgs {V D : Ty → Type} (η : ∀ σ, V σ → D σ)
    (ρ κ : RTy) (a : Args D ρ) (b : Args V κ) :
    mapArgs (extendEnv η ρ a) κ (mapArgs (liftVars ρ) κ b) = mapArgs η κ b := by
  rw [mapArgs_comp]
  rfl

/-- The relationalized E₂ language. Its binders are finite lists of sorts.
Even the empty block is allowed; it binds no variables. -/
inductive Formula : (Ty → Type) → Type 1 where
  | equal {V : Ty → Type} {σ : Ty} (x y : V σ) : Formula V
  | rel {V : Ty → Type} (ρ : RTy) (x : V (.rel ρ)) (a : Args V ρ) : Formula V
  | falsum {V : Ty → Type} : Formula V
  | neg {V : Ty → Type} : Formula V → Formula V
  | conj {V : Ty → Type} : Formula V → Formula V → Formula V
  | disj {V : Ty → Type} : Formula V → Formula V → Formula V
  | all {V : Ty → Type} (ρ : RTy) : Formula (Extend V ρ) → Formula V
  | ex {V : Ty → Type} (ρ : RTy) : Formula (Extend V ρ) → Formula V

def Formula.imp {V : Ty → Type} (p q : Formula V) : Formula V := .disj (.neg p) q
def Formula.iff {V : Ty → Type} (p q : Formula V) : Formula V :=
  .conj (p.imp q) (q.imp p)

/-- Sorts and extensional membership predicates. Nonemptiness at relational
sorts follows later from comprehension. No selection principle occurs here. -/
structure Structure where
  D : Ty → Type
  rel : ∀ ρ, D (.rel ρ) → Args D ρ → Prop
  rel_injective : ∀ ρ, Function.Injective (rel ρ)
  nonempty_e : Nonempty (D .e)

def Formula.Realize (S : Structure) :
    {V : Ty → Type} → Formula V → (∀ σ, V σ → S.D σ) → Prop
  | _, .equal x y, η => η _ x = η _ y
  | _, .rel ρ x a, η => S.rel ρ (η _ x) (mapArgs η ρ a)
  | _, .falsum, _ => False
  | _, .neg p, η => ¬ p.Realize S η
  | _, .conj p q, η => p.Realize S η ∧ q.Realize S η
  | _, .disj p q, η => p.Realize S η ∨ q.Realize S η
  | _, .all ρ p, η => ∀ a : Args S.D ρ, p.Realize S (extendEnv η ρ a)
  | _, .ex ρ p, η => ∃ a : Args S.D ρ, p.Realize S (extendEnv η ρ a)

theorem Formula.realize_imp (S : Structure) {V : Ty → Type}
    (p q : Formula V) (η : ∀ σ, V σ → S.D σ) :
    (p.imp q).Realize S η ↔ (p.Realize S η → q.Realize S η) := by
  classical
  change (¬p.Realize S η ∨ q.Realize S η) ↔ _
  constructor
  · intro h hp
    exact h.elim (fun hn => False.elim (hn hp)) id
  · intro h
    by_cases hp : p.Realize S η
    · exact Or.inr (h hp)
    · exact Or.inl hp

theorem Formula.realize_iff (S : Structure) {V : Ty → Type}
    (p q : Formula V) (η : ∀ σ, V σ → S.D σ) :
    (p.iff q).Realize S η ↔ (p.Realize S η ↔ q.Realize S η) := by
  change (p.imp q).Realize S η ∧ (q.imp p).Realize S η ↔ _
  rw [realize_imp, realize_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- Parameterized first-order comprehension on the displayed finite syntax.
The parameter family can be arbitrary; each formula mentions finitely many
variables. This is not comprehension for arbitrary external predicates. -/
def Comprehension (S : Structure) : Prop :=
  ∀ (V : Ty → Type) (ρ : RTy) (φ : Formula (Extend V ρ))
    (η : ∀ σ, V σ → S.D σ),
    ∃ X : S.D (.rel ρ), ∀ a : Args S.D ρ,
      S.rel ρ X a ↔ φ.Realize S (extendEnv η ρ a)

/-- The same domains, as an actual intensional action premodel of the pure language. -/
def Structure.model (S : Structure) : Intensional.Premodel Signature.pure World where
  W₀ := .star
  inner := inner S.D
  nonempty_e _ := S.nonempty_e
  incl ρ _ X := {p | S.rel ρ X p.2.1}
  incl_map := by
    intro ρ W V h X
    rfl
  incl_injective ρ W := by
    intro X Y h
    apply S.rel_injective ρ
    funext a
    exact congrFun h ⟨W, a, 𝟙 W⟩
  I c := nomatch c

theorem args_map_eq (D : Ty → Type) : ∀ ρ {W V : World}
    (h : W ⟶ V) (a : Intensional.Args (inner D) ρ W),
    Intensional.Args.map (inner D) ρ h a = a
  | .t, _, _, _, a => by cases a; rfl
  | .arr _ ρ, _, _, h, a => by
    change (a.1, Intensional.Args.map (inner D) ρ h a.2) = a
    rw [args_map_eq D ρ h a.2]

theorem push_eq (S : Structure) {Γ : Ctx} {W V : World}
    (h : W ⟶ V) (g : IEnv S.D Γ) : S.model.push h g = g := by
  induction g with
  | nil => rfl
  | cons x g ih => exact congrArg (IEnv.cons x) ih

/-- All intensions in a one-world premodel are determined by their actual extension. -/
theorem intension_ext (S : Structure) {ρ : RTy}
    {X Y : Intensional.Intension (inner S.D) ρ World.star}
    (h : ∀ a : Args S.D ρ,
      (⟨World.star, a, 𝟙 World.star⟩ : Intensional.Tuple (inner S.D) ρ World.star) ∈ X ↔
      (⟨World.star, a, 𝟙 World.star⟩ : Intensional.Tuple (inner S.D) ρ World.star) ∈ Y) :
    X = Y := by
  ext ⟨W, a, k⟩
  cases W
  cases k
  exact h a

/-- Comprehension admits a definable intension into the actual premodel.
This lemma assumes no `IsModel` or Choice verdict. -/
theorem admit_definable (S : Structure) (hC : Comprehension S)
    {V : Ty → Type} (ρ : RTy) (φ : Formula (Extend V ρ))
    (η : ∀ σ, V σ → S.D σ)
    (X : Intensional.Intension (inner S.D) ρ World.star)
    (hX : ∀ a : Args S.D ρ,
      (⟨World.star, a, 𝟙 World.star⟩ : Intensional.Tuple (inner S.D) ρ World.star) ∈ X ↔
      φ.Realize S (extendEnv η ρ a)) :
    X ∈ Set.range (S.model.incl ρ World.star) := by
  obtain ⟨Y, hY⟩ := hC V ρ φ η
  refine ⟨Y, intension_ext S (fun a => ?_)⟩
  exact (hY a).trans (hX a).symm

end Classicism.Meta.ChoiceFirstOrder
