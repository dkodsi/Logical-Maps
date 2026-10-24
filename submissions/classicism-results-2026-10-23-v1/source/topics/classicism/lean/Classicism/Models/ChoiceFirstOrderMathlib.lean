import Classicism.Models.ChoiceFirstOrderCountable
import Mathlib.ModelTheory.Semantics

/-!
# The small sorted syntax in Mathlib's actual first-order language

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/finite-choice-forcing-extraction-review.md` sections 2--4
(unpaginated). The domain is the tagged union of the existing typed domains.
Unary predicates test sorts; each finite-arity profile predicate checks all
argument tags and uses the original relational application. Quantifiers are
explicitly guarded by sorts. Equality is Mathlib's actual equality atom.

This is the forward syntax-and-satisfaction bridge. It asserts neither a
complete axiom theory characterizing its image nor a model-existence or
forcing-extraction theorem.
-/

namespace Classicism.Meta.ChoiceFirstOrder.MathlibBridge

inductive Relation : Nat → Type where
  | sort (σ : Ty) : Relation 1
  | profile (ρ : RTy) : Relation (ρ.args.length + 1)

private def relationFromCode : Ty ⊕ RTy → Σ n, Relation n
  | .inl σ => ⟨1, .sort σ⟩
  | .inr ρ => ⟨ρ.args.length + 1, .profile ρ⟩

instance relationSymbolsCountable : Countable (Σ n, Relation n) := by
  apply Function.Surjective.countable (f := relationFromCode)
  rintro ⟨n, r⟩
  cases r with
  | sort σ => exact ⟨Sum.inl σ, rfl⟩
  | profile ρ => exact ⟨Sum.inr ρ, rfl⟩

instance relationCountable (n : Nat) : Countable (Relation n) :=
  Function.Injective.countable
    (f := fun r : Relation n => (⟨n, r⟩ : Σ k, Relation k))
    (fun _ _ h => _root_.sigma_mk_injective h)

def language : FirstOrder.Language where
  Functions _ := Empty
  Relations := Relation

theorem language_countable : Countable language.Symbols := by
  change Countable ((Σ n : Nat, Empty) ⊕ (Σ n : Nat, Relation n))
  infer_instance

abbrev Carrier (S : Structure) := Sigma S.D

instance carrierNonempty (S : Structure) : Nonempty (Carrier S) :=
  S.nonempty_e.map (fun x => ⟨.e, x⟩)

/-- Flatten a typed finite argument tuple, without erasing its values. -/
def flatten {D : Ty → Type} {M : Type} (f : ∀ σ, D σ → M) :
    ∀ ρ, Args D ρ → Fin ρ.args.length → M
  | .t, _ => Fin.elim0
  | .arr σ ρ, a =>
      Fin.cons (α := fun _ : Fin (ρ.args.length + 1) => M) (f σ a.1) (flatten f ρ a.2)

theorem flatten_tag_injective (D : Ty → Type) : ∀ ρ,
    Function.Injective (flatten (fun σ x => (⟨σ, x⟩ : Sigma D)) ρ)
  | .t => fun _ _ _ => Subsingleton.elim _ _
  | .arr σ ρ => by
    intro a b h
    change Fin.cons (α := fun _ : Fin (ρ.args.length + 1) => Sigma D)
      ⟨σ, a.1⟩ (flatten (fun τ x => (⟨τ, x⟩ : Sigma D)) ρ a.2) =
      Fin.cons (α := fun _ : Fin (ρ.args.length + 1) => Sigma D)
        ⟨σ, b.1⟩ (flatten (fun τ x => (⟨τ, x⟩ : Sigma D)) ρ b.2) at h
    have h₁ : a.1 = b.1 := _root_.sigma_mk_injective (i := σ) (by
      simpa only [Fin.cons_zero] using congrFun h (0 : Fin (ρ.args.length + 1)))
    have h₂ : a.2 = b.2 := flatten_tag_injective D ρ (by
      funext i
      simpa only [Fin.cons_succ] using congrFun h i.succ)
    exact Prod.ext h₁ h₂

/-- Ill-sorted profile tuples are false. No formula truth predicate occurs
in the language: the nonlogical relation is exactly typed application. -/
instance taggedStructure (S : Structure) : language.Structure (Carrier S) where
  funMap f := nomatch f
  RelMap := fun {n} r => match r with
    | .sort σ => fun a => (a 0).1 = σ
    | .profile ρ => fun a =>
        ∃ X : S.D (.rel ρ), ∃ b : Args S.D ρ,
          a = Fin.cons (α := fun _ : Fin (ρ.args.length + 1) => Carrier S)
            (⟨.rel ρ, X⟩ : Carrier S)
            (flatten (fun σ x => (⟨σ, x⟩ : Carrier S)) ρ b) ∧ S.rel ρ X b

theorem profile_correct (S : Structure) (ρ : RTy) (X : S.D (.rel ρ))
    (a : Args S.D ρ) :
    FirstOrder.Language.Structure.RelMap (L := language) (Relation.profile ρ)
      (Fin.cons (α := fun _ : Fin (ρ.args.length + 1) => Carrier S)
        (⟨.rel ρ, X⟩ : Carrier S)
        (flatten (fun σ x => (⟨σ, x⟩ : Carrier S)) ρ a)) ↔ S.rel ρ X a := by
  constructor
  · rintro ⟨Y, b, h, hR⟩
    have hX : X = Y := _root_.sigma_mk_injective (i := Ty.rel ρ) (by
      simpa only [Fin.cons_zero] using congrFun h 0)
    have ha : a = b := flatten_tag_injective S.D ρ (by
      funext i
      simpa only [Fin.cons_succ] using congrFun h i.succ)
    cases hX
    cases ha
    exact hR
  · intro h
    exact ⟨X, a, rfl, h⟩

/-- Mathlib binds the last de Bruijn level. The innermost typed variable is
therefore mapped to the last position of the current context. -/
def variableIndex : ∀ {Γ : Ctx} {σ : Ty}, Var Γ σ → Fin Γ.length
  | _ :: Γ, _, .zero => Fin.last Γ.length
  | _ :: _, _, .succ v => (variableIndex v).castSucc

def variableTerm {Γ : Ctx} {σ : Ty} (v : Var Γ σ) :
    language.Term (Empty ⊕ Fin Γ.length) := .var (.inr (variableIndex v))

def envVector (S : Structure) : ∀ {Γ : Ctx}, IEnv S.D Γ → Fin Γ.length → Carrier S
  | [], .nil => Fin.elim0
  | σ :: Γ, .cons x g =>
      Fin.snoc (α := fun _ : Fin (Γ.length + 1) => Carrier S) (envVector S g) ⟨σ, x⟩

theorem variable_correct (S : Structure) : ∀ {Γ : Ctx} {σ : Ty}
    (v : Var Γ σ) (g : IEnv S.D Γ),
    (variableTerm v).realize (Sum.elim Empty.elim (envVector S g)) =
      (⟨σ, g.get v⟩ : Carrier S)
  | _, _, .zero, .cons x g => by
    change Fin.snoc (α := fun _ => Carrier S) (envVector S g) ⟨_, x⟩
      (Fin.last _) = (⟨_, x⟩ : Carrier S)
    exact Fin.snoc_last _ _
  | _, _, .succ v, .cons x g => by
    change Fin.snoc (α := fun _ => Carrier S) (envVector S g) ⟨_, x⟩
      (variableIndex v).castSucc = (⟨_, g.get v⟩ : Carrier S)
    rw [Fin.snoc_castSucc]
    exact variable_correct S v g

theorem flatten_variables_correct (S : Structure) {Γ : Ctx} (g : IEnv S.D Γ) :
    ∀ ρ (a : Args (fun σ => Var Γ σ) ρ),
    (fun i => (flatten (fun _ v => variableTerm v) ρ a i).realize
      (Sum.elim Empty.elim (envVector S g))) =
      flatten (fun σ x => (⟨σ, x⟩ : Carrier S)) ρ
        (mapArgs (fun _ v => g.get v) ρ a)
  | .t, _ => by funext i; exact i.elim0
  | .arr σ ρ, a => by
    change (fun i : Fin (ρ.args.length + 1) =>
      (Fin.cons (α := fun _ => language.Term (Empty ⊕ Fin Γ.length))
        (variableTerm a.1) (flatten (fun _ v => variableTerm v) ρ a.2) i).realize
          (Sum.elim Empty.elim (envVector S g))) =
      Fin.cons (α := fun _ => Carrier S) ⟨σ, g.get a.1⟩
        (flatten (fun τ x => (⟨τ, x⟩ : Carrier S)) ρ
          (mapArgs (fun _ v => g.get v) ρ a.2))
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using variable_correct S a.1 g
    · simpa only [Fin.cons_succ] using
        congrFun (flatten_variables_correct S g ρ a.2) j

abbrev FormulaAt (Γ : Ctx) := language.BoundedFormula Empty Γ.length

def realizeAt (S : Structure) {Γ : Ctx} (φ : FormulaAt Γ) (g : IEnv S.D Γ) : Prop :=
  φ.Realize Empty.elim (envVector S g)

def sortGuard (σ : Ty) (n : Nat) : language.BoundedFormula Empty (n + 1) :=
  .rel (.sort σ) (fun _ => .var (.inr (Fin.last n)))

def guardedAll (σ : Ty) {Γ : Ctx} (φ : FormulaAt (σ :: Γ)) : FormulaAt Γ :=
  .all ((sortGuard σ Γ.length).imp φ)

def guardedEx (σ : Ty) {Γ : Ctx} (φ : FormulaAt (σ :: Γ)) : FormulaAt Γ :=
  ((sortGuard σ Γ.length) ⊓ φ).ex

theorem guardedAll_correct (S : Structure) (σ : Ty) {Γ : Ctx}
    (φ : FormulaAt (σ :: Γ)) (g : IEnv S.D Γ) :
    realizeAt S (guardedAll σ (Γ := Γ) φ) g ↔
      ∀ x : S.D σ, realizeAt S φ (.cons x g) := by
  change (∀ z : Carrier S,
    (Fin.snoc (α := fun _ : Fin (Γ.length + 1) => Carrier S)
      (envVector S g) z (Fin.last Γ.length)).1 = σ →
      φ.Realize Empty.elim (Fin.snoc (envVector S g) z)) ↔
    ∀ x : S.D σ, φ.Realize Empty.elim (Fin.snoc (envVector S g) ⟨σ, x⟩)
  simp only [Fin.snoc_last]
  constructor
  · intro h x
    exact h ⟨σ, x⟩ rfl
  · intro h ⟨τ, x⟩ hτ
    cases hτ
    exact h x

theorem guardedEx_correct (S : Structure) (σ : Ty) {Γ : Ctx}
    (φ : FormulaAt (σ :: Γ)) (g : IEnv S.D Γ) :
    realizeAt S (guardedEx σ (Γ := Γ) φ) g ↔
      ∃ x : S.D σ, realizeAt S φ (.cons x g) := by
  simp only [realizeAt, guardedEx, FirstOrder.Language.BoundedFormula.realize_ex,
    FirstOrder.Language.BoundedFormula.realize_inf]
  change (∃ z : Carrier S,
    (Fin.snoc (α := fun _ : Fin (Γ.length + 1) => Carrier S)
      (envVector S g) z (Fin.last Γ.length)).1 = σ ∧
      φ.Realize Empty.elim (Fin.snoc (envVector S g) z)) ↔
    ∃ x : S.D σ, φ.Realize Empty.elim (Fin.snoc (envVector S g) ⟨σ, x⟩)
  simp only [Fin.snoc_last]
  constructor
  · rintro ⟨⟨τ, x⟩, hτ, h⟩
    cases hτ
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨⟨σ, x⟩, rfl, h⟩

/-- The block is bound in reverse list order, matching the de Bruijn levels.
All variables in the block are independently guarded by their actual sorts. -/
def allArgs : ∀ (ρ : RTy) (Γ : Ctx), FormulaAt (ρ.args ++ Γ) → FormulaAt Γ
  | .t, _, φ => φ
  | .arr σ ρ, Γ, φ => allArgs ρ Γ (guardedAll σ (Γ := ρ.args ++ Γ) φ)

def exArgs : ∀ (ρ : RTy) (Γ : Ctx), FormulaAt (ρ.args ++ Γ) → FormulaAt Γ
  | .t, _, φ => φ
  | .arr σ ρ, Γ, φ => exArgs ρ Γ (guardedEx σ (Γ := ρ.args ++ Γ) φ)

theorem allArgs_correct (S : Structure) : ∀ (ρ : RTy) (Γ : Ctx)
    (φ : FormulaAt (ρ.args ++ Γ)) (g : IEnv S.D Γ),
    realizeAt S (allArgs ρ Γ φ) g ↔
      ∀ a : Args S.D ρ, realizeAt S φ (appendEnv (argsEnv ρ a) g)
  | .t, _, _, _ => ⟨fun h _ => h, fun h => h PUnit.unit⟩
  | .arr σ ρ, Γ, φ, g => by
    rw [allArgs, allArgs_correct]
    constructor
    · intro h a
      exact (guardedAll_correct S σ φ (appendEnv (argsEnv ρ a.2) g)).mp (h a.2) a.1
    · intro h a
      exact (guardedAll_correct S σ φ (appendEnv (argsEnv ρ a) g)).mpr
        (fun x => h (x, a))

theorem exArgs_correct (S : Structure) : ∀ (ρ : RTy) (Γ : Ctx)
    (φ : FormulaAt (ρ.args ++ Γ)) (g : IEnv S.D Γ),
    realizeAt S (exArgs ρ Γ φ) g ↔
      ∃ a : Args S.D ρ, realizeAt S φ (appendEnv (argsEnv ρ a) g)
  | .t, _, _, _ => ⟨fun h => ⟨PUnit.unit, h⟩, fun ⟨_, h⟩ => h⟩
  | .arr σ ρ, Γ, φ, g => by
    rw [exArgs, exArgs_correct]
    constructor
    · rintro ⟨a, h⟩
      obtain ⟨x, hx⟩ := (guardedEx_correct S σ φ (appendEnv (argsEnv ρ a) g)).mp h
      exact ⟨(x, a), hx⟩
    · rintro ⟨⟨x, a⟩, h⟩
      exact ⟨a, (guardedEx_correct S σ φ (appendEnv (argsEnv ρ a) g)).mpr ⟨x, h⟩⟩

/-- A direct recursive translation into Mathlib's actual first-order syntax. -/
def translate : ∀ {Γ : Ctx}, SmallFormula Γ → FormulaAt Γ
  | _, .equal x y => .equal (variableTerm x) (variableTerm y)
  | _, .rel ρ x a => .rel (.profile ρ)
      (Fin.cons (variableTerm x) (flatten (fun _ v => variableTerm v) ρ a))
  | _, .falsum => .falsum
  | _, .neg p => (translate p).not
  | _, .conj p q => translate p ⊓ translate q
  | _, .disj p q => translate p ⊔ translate q
  | Γ, .all ρ p => allArgs ρ Γ (translate p)
  | Γ, .ex ρ p => exArgs ρ Γ (translate p)

theorem translate_correct (S : Structure) : ∀ {Γ : Ctx} (φ : SmallFormula Γ)
    (g : IEnv S.D Γ), realizeAt S (translate φ) g ↔ φ.Realize S g
  | _, .equal x y, g => by
    change (variableTerm x).realize (Sum.elim Empty.elim (envVector S g)) =
      (variableTerm y).realize (Sum.elim Empty.elim (envVector S g)) ↔ g.get x = g.get y
    rw [variable_correct, variable_correct]
    exact ⟨fun h => _root_.sigma_mk_injective h, congrArg (Sigma.mk _)⟩
  | Γ, .rel ρ x a, g => by
    change FirstOrder.Language.Structure.RelMap (L := language) (Relation.profile ρ)
      (fun i : Fin (ρ.args.length + 1) =>
        (Fin.cons (α := fun _ => language.Term (Empty ⊕ Fin Γ.length)) (variableTerm x)
        (flatten (fun _ v => variableTerm v) ρ a) i).realize
          (Sum.elim Empty.elim (envVector S g))) ↔
      S.rel ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ a)
    have hv : (fun i : Fin (ρ.args.length + 1) =>
        (Fin.cons (α := fun _ => language.Term (Empty ⊕ Fin Γ.length)) (variableTerm x)
        (flatten (fun _ v => variableTerm v) ρ a) i).realize
          (Sum.elim Empty.elim (envVector S g))) =
        Fin.cons (α := fun _ : Fin (ρ.args.length + 1) => Carrier S)
          (⟨.rel ρ, g.get x⟩ : Carrier S)
          (flatten (fun σ v => (⟨σ, v⟩ : Carrier S)) ρ
            (mapArgs (fun _ v => g.get v) ρ a)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using variable_correct S x g
      · simpa only [Fin.cons_succ] using congrFun (flatten_variables_correct S g ρ a) j
    rw [hv]
    exact profile_correct S ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ a)
  | _, .falsum, _ => Iff.rfl
  | _, .neg p, g => not_congr (translate_correct S p g)
  | _, .conj p q, g =>
      FirstOrder.Language.BoundedFormula.realize_inf.trans
        (and_congr (translate_correct S p g) (translate_correct S q g))
  | _, .disj p q, g =>
      FirstOrder.Language.BoundedFormula.realize_sup.trans
        (or_congr (translate_correct S p g) (translate_correct S q g))
  | Γ, .all ρ p, g =>
      (allArgs_correct S ρ Γ (translate p) g).trans
        (forall_congr' (fun a => translate_correct S p (appendEnv (argsEnv ρ a) g)))
  | Γ, .ex ρ p, g =>
      (exArgs_correct S ρ Γ (translate p) g).trans
        (exists_congr (fun a => translate_correct S p (appendEnv (argsEnv ρ a) g)))

/-- An actual Mathlib sentence attached to the original pure sentence. -/
def sentence (p : Sentence Signature.pure) : language.Sentence :=
  translate (smallSentenceTranslation p)

theorem sentence_correct (S : Structure) (p : Sentence Signature.pure) :
    FirstOrder.Language.Sentence.Realize (Carrier S) (sentence p) ↔
      S.model.HoldsSentence p := by
  have he : (default : Empty → Carrier S) = Empty.elim := Subsingleton.elim _ _
  have hz : (default : Fin 0 → Carrier S) = Fin.elim0 := Subsingleton.elim _ _
  change (translate (smallSentenceTranslation p)).Realize
    (default : Empty → Carrier S) (default : Fin 0 → Carrier S) ↔ _
  rw [he, hz]
  exact (translate_correct S (smallSentenceTranslation p) .nil).trans
    (smallSentenceTranslation_correct S p)

end Classicism.Meta.ChoiceFirstOrder.MathlibBridge
