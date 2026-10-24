import ClassicismZFC.InternalHierarchy
import Classicism.Models.CoalescedInternalRelations

/-!
# Actual admission and recoding of source relation graphs

Original formalization (misc), 23 October 2026. Source binary graphs use
`pair(x,y)` and source operation graphs use `pair(pair(x,y),z)`. The typed
hierarchy uses right-nested tuples ending in its unit code. Finite raw
Separation recodes those graphs and proves their exact application profiles.
The inverse unary construction represents every admitted unary test by an
internal subset of the individual set. No real-field or CH transfer is assumed.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Erdos501.FOL (L memM)
open Classicism.Meta
open Classicism.Meta.CoalescedInternalHierarchy
open ClassicismZFC.SetLaws (pairM emptyM)
open ClassicismZFC.InternalHierarchy (internalUniverse)

namespace ClassicismZFC.TupleRecoding

variable {M : Type} [L.Structure M]

abbrev unaryTy : RTy := .arr .e .t
abbrev binaryTy : RTy := .arr .e (.arr .e .t)
abbrev ternaryTy : RTy := .arr .e (.arr .e (.arr .e .t))

abbrev Base (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E) :=
  D (internalUniverse hZFC E hE) .e

abbrev Relation (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (ρ : RTy) := D (internalUniverse hZFC E hE) (.rel ρ)

def profile (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (ρ : RTy) (X : Relation hZFC E hE ρ)
    (a : ChoiceFirstOrder.Args (D (internalUniverse hZFC E hE)) ρ) : Prop :=
  rel (internalUniverse hZFC E hE) ρ X a

def unaryFormula (A : M) : RawFormula M [.e] := .mem (.var .zero) (.param A)

def binaryFormula (G : M) : RawFormula M [.e, .e] :=
  .mem (.pair (.var .zero) (.var (.succ .zero))) (.param G)

def ternaryFormula (Op : M) : RawFormula M [.e, .e, .e] :=
  .mem (.pair (.pair (.var .zero) (.var (.succ .zero)))
    (.var (.succ (.succ .zero)))) (.param Op)

def binaryLeFormula (Lt : M) : RawFormula M [.e, .e] :=
  .disj (binaryFormula Lt) (.equal (.var .zero) (.var (.succ .zero)))

set_option backward.isDefEq.respectTransparency false in
theorem unary_exists (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (A : M) : ∃ X : Relation hZFC E hE unaryTy,
      ∀ x : Base hZFC E hE,
        profile hZFC E hE unaryTy X (x, PUnit.unit) ↔ memM (M := M) x.val A := by
  obtain ⟨X, hX⟩ := rawComprehension (internalUniverse hZFC E hE) [] unaryTy
    (unaryFormula A) IEnv.nil
  refine ⟨X, ?_⟩
  intro x
  have hx := hX (x, PUnit.unit)
  dsimp only [profile, unaryFormula, unaryTy, RTy.args, RawFormula.Realize, RawTerm.eval,
    eraseArgs, eraseEnv, ChoiceFirstOrder.argsEnv, ChoiceFirstOrder.appendEnv,
    IEnv.get, internalUniverse] at hx ⊢
  simp only [RawTerm.eval, ChoiceFirstOrder.appendEnv, IEnv.get] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
theorem binary_exists (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (G : M) : ∃ X : Relation hZFC E hE binaryTy,
      ∀ x y : Base hZFC E hE,
        profile hZFC E hE binaryTy X (x, y, PUnit.unit) ↔
          memM (M := M) (pairM (M := M) x.val y.val) G := by
  obtain ⟨X, hX⟩ := rawComprehension (internalUniverse hZFC E hE) [] binaryTy
    (binaryFormula G) IEnv.nil
  refine ⟨X, ?_⟩
  intro x y
  have hx := hX (x, y, PUnit.unit)
  dsimp only [profile, binaryFormula, binaryTy, RTy.args, RawFormula.Realize, RawTerm.eval,
    eraseArgs, eraseEnv, ChoiceFirstOrder.argsEnv, ChoiceFirstOrder.appendEnv,
    IEnv.get, internalUniverse] at hx ⊢
  simp only [RawTerm.eval, ChoiceFirstOrder.appendEnv, IEnv.get] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
theorem ternary_exists (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (Op : M) : ∃ X : Relation hZFC E hE ternaryTy,
      ∀ x y z : Base hZFC E hE,
        profile hZFC E hE ternaryTy X (x, y, z, PUnit.unit) ↔
          memM (M := M) (pairM (M := M) (pairM (M := M) x.val y.val) z.val) Op := by
  obtain ⟨X, hX⟩ := rawComprehension (internalUniverse hZFC E hE) [] ternaryTy
    (ternaryFormula Op) IEnv.nil
  refine ⟨X, ?_⟩
  intro x y z
  have hx := hX (x, y, z, PUnit.unit)
  dsimp only [profile, ternaryFormula, ternaryTy, RTy.args, RawFormula.Realize, RawTerm.eval,
    eraseArgs, eraseEnv, ChoiceFirstOrder.argsEnv, ChoiceFirstOrder.appendEnv,
    IEnv.get, internalUniverse] at hx ⊢
  simp only [RawTerm.eval, ChoiceFirstOrder.appendEnv, IEnv.get] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
theorem binaryLe_exists (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (Lt : M) : ∃ X : Relation hZFC E hE binaryTy,
      ∀ x y : Base hZFC E hE,
        profile hZFC E hE binaryTy X (x, y, PUnit.unit) ↔
          memM (M := M) (pairM (M := M) x.val y.val) Lt ∨ x.val = y.val := by
  obtain ⟨X, hX⟩ := rawComprehension (internalUniverse hZFC E hE) [] binaryTy
    (binaryLeFormula Lt) IEnv.nil
  refine ⟨X, ?_⟩
  intro x y
  have hx := hX (x, y, PUnit.unit)
  dsimp only [profile, binaryLeFormula, binaryFormula, binaryTy, RTy.args, RawFormula.Realize, RawTerm.eval,
    eraseArgs, eraseEnv, ChoiceFirstOrder.argsEnv, ChoiceFirstOrder.appendEnv,
    IEnv.get, internalUniverse] at hx ⊢
  simp only [RawTerm.eval, ChoiceFirstOrder.appendEnv, IEnv.get] at hx
  exact hx

noncomputable def unary (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM (M := M) x E) (A : M) : Relation hZFC E hE unaryTy :=
  Classical.choose (unary_exists hZFC E hE A)

noncomputable def binary (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM (M := M) x E) (G : M) : Relation hZFC E hE binaryTy :=
  Classical.choose (binary_exists hZFC E hE G)

noncomputable def ternary (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM (M := M) x E) (Op : M) : Relation hZFC E hE ternaryTy :=
  Classical.choose (ternary_exists hZFC E hE Op)

noncomputable def binaryLe (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM (M := M) x E) (Lt : M) : Relation hZFC E hE binaryTy :=
  Classical.choose (binaryLe_exists hZFC E hE Lt)

theorem unary_eval (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (A : M) (x : Base hZFC E hE) :
    profile hZFC E hE unaryTy (unary hZFC E hE A) (x, PUnit.unit) ↔ memM (M := M) x.val A :=
  Classical.choose_spec (unary_exists hZFC E hE A) x

theorem binary_eval (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (G : M) (x y : Base hZFC E hE) :
    profile hZFC E hE binaryTy (binary hZFC E hE G) (x, y, PUnit.unit) ↔
      memM (M := M) (pairM (M := M) x.val y.val) G :=
  Classical.choose_spec (binary_exists hZFC E hE G) x y

theorem ternary_eval (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (Op : M) (x y z : Base hZFC E hE) :
    profile hZFC E hE ternaryTy (ternary hZFC E hE Op) (x, y, z, PUnit.unit) ↔
      memM (M := M) (pairM (M := M) (pairM (M := M) x.val y.val) z.val) Op :=
  Classical.choose_spec (ternary_exists hZFC E hE Op) x y z

theorem binaryLe_eval (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M) (hE : ∃ x, memM (M := M) x E)
    (Lt : M) (x y : Base hZFC E hE) :
    profile hZFC E hE binaryTy (binaryLe hZFC E hE Lt) (x, y, PUnit.unit) ↔
      memM (M := M) (pairM (M := M) x.val y.val) Lt ∨ x.val = y.val :=
  Classical.choose_spec (binaryLe_exists hZFC E hE Lt) x y

/-- Every admitted unary test has an internal subset of E with exactly the
same profile. This is Separation by the finite formula `pair(x,unit) ∈ F`.
It is the inverse recoding needed for universal second-order unary tests. -/
theorem unary_subset_exists (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM (M := M) x E) (F : Relation hZFC E hE unaryTy) :
    ∃ A : M, (∀ z, memM (M := M) z A → memM (M := M) z E) ∧
      ∀ x : Base hZFC E hE,
        memM (M := M) x.val A ↔ profile hZFC E hE unaryTy F (x, PUnit.unit) := by
  let φ : RawFormula M [.e] :=
    .mem (.pair (.var .zero) (.param (emptyM : M))) (.param F.val)
  obtain ⟨A, hA⟩ := (internalUniverse hZFC E hE).separation [] φ IEnv.nil E
  have hA' : ∀ z : M, memM (M := M) z A ↔ memM (M := M) z E ∧
      memM (M := M) (pairM (M := M) z emptyM) F.val := by
    intro z
    simpa only [φ, RawFormula.Realize, RawTerm.eval, IEnv.get, internalUniverse]
      using hA z
  refine ⟨A, fun z hz => ((hA' z).mp hz).1, ?_⟩
  intro x
  change memM (M := M) x.val A ↔ memM (M := M) (pairM (M := M) x.val emptyM) F.val
  exact ⟨fun hx => ((hA' x.val).mp hx).2,
    fun hx => (hA' x.val).mpr ⟨x.property, hx⟩⟩

noncomputable def unarySubset (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM (M := M) x E) (F : Relation hZFC E hE unaryTy) : M :=
  Classical.choose (unary_subset_exists hZFC E hE F)

theorem unarySubset_subset (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM (M := M) x E) (F : Relation hZFC E hE unaryTy) :
    ∀ z, memM (M := M) z (unarySubset hZFC E hE F) → memM (M := M) z E :=
  (Classical.choose_spec (unary_subset_exists hZFC E hE F)).1

theorem unarySubset_eval (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM (M := M) x E) (F : Relation hZFC E hE unaryTy) (x : Base hZFC E hE) :
    memM (M := M) x.val (unarySubset hZFC E hE F) ↔
      profile hZFC E hE unaryTy F (x, PUnit.unit) :=
  (Classical.choose_spec (unary_subset_exists hZFC E hE F)).2 x

#print axioms unary_exists
#print axioms binary_exists
#print axioms ternary_exists
#print axioms binaryLe_exists
#print axioms unary_subset_exists

end ClassicismZFC.TupleRecoding
