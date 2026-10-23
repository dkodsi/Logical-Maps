import Classicism.Results.Research.MaxAtomicitySetSemantics
import Mathlib.SetTheory.ZFC.Basic

/-!
# Concrete finite formulas for basic set operations

Direct source: the basic finite set coding required by
`research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md`,
§§3–5 (unpaginated local research, misc). These formulas and their correctness
proofs are supplied here; their existence or meaning is not an assumption.

Formula satisfaction uses the existing Type-0 semantics. The ordinary relational
predicates are universe-polymorphic, so their separate ZFSet characterizations
do not identify the entire universe of ZFSet with a Type-0 semantic carrier.
No JS algebra, code for that algebra, or inconsistency result is asserted here.
Compilation and axiom inspection belong to the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicitySetFormulaTools

open MaxAtomicitySetSyntax MaxAtomicitySetSemantics

/-- Extend a variable renaming through one fresh de Bruijn binder. -/
def liftRen {n m : Nat} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

/-- Actual structural renaming of the finite first-order syntax. -/
def rename {n m : Nat} (f : Fin n → Fin m) (φ : SetFormula n) : SetFormula m :=
  match φ with
  | .bot => .bot
  | .top => .top
  | .eq i j => .eq (f i) (f j)
  | .mem i j => .mem (f i) (f j)
  | .neg p => .neg (rename f p)
  | .conj p q => .conj (rename f p) (rename f q)
  | .disj p q => .disj (rename f p) (rename f q)
  | .imp p q => .imp (rename f p) (rename f q)
  | .iff p q => .iff (rename f p) (rename f q)
  | .all p => .all (rename (liftRen f) p)
  | .ex p => .ex (rename (liftRen f) p)

theorem comp_liftRen {D : Type*} {n m : Nat} (f : Fin n → Fin m)
    (ρ : Fin m → D) (x : D) :
    (fun i => Fin.cases x ρ (liftRen f i)) =
      Fin.cases x (fun i => ρ (f i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Renaming changes only the assignment, including under both quantifiers. -/
theorem satisfies_rename {D : Type} {n : Nat} (φ : SetFormula n)
    (R : D → D → Prop) :
    ∀ {m : Nat} (f : Fin n → Fin m) (ρ : Fin m → D),
      satisfies (rename f φ) R ρ ↔ satisfies φ R (fun i => ρ (f i)) := by
  induction φ with
  | bot => intros; rfl
  | top => intros; rfl
  | eq i j => intros; rfl
  | mem i j => intros; rfl
  | neg p ih =>
    intro m f ρ
    exact not_congr (ih f ρ)
  | conj p q ihp ihq =>
    intro m f ρ
    exact and_congr (ihp f ρ) (ihq f ρ)
  | disj p q ihp ihq =>
    intro m f ρ
    exact or_congr (ihp f ρ) (ihq f ρ)
  | imp p q ihp ihq =>
    intro m f ρ
    exact imp_congr (ihp f ρ) (ihq f ρ)
  | iff p q ihp ihq =>
    intro m f ρ
    exact iff_congr (ihp f ρ) (ihq f ρ)
  | all p ih =>
    intro m f ρ
    change (∀ x : D, satisfies (rename (liftRen f) p) R (Fin.cases x ρ)) ↔ _
    apply forall_congr'
    intro x
    rw [ih (liftRen f) (Fin.cases x ρ), comp_liftRen]
  | ex p ih =>
    intro m f ρ
    change (∃ x : D, satisfies (rename (liftRen f) p) R (Fin.cases x ρ)) ↔ _
    apply exists_congr
    intro x
    rw [ih (liftRen f) (Fin.cases x ρ), comp_liftRen]

def lift {n : Nat} (φ : SetFormula n) : SetFormula (n + 1) :=
  rename Fin.succ φ

theorem satisfies_lift {D : Type} {n : Nat} (φ : SetFormula n)
    (R : D → D → Prop) (ρ : Fin n → D) (x : D) :
    satisfies (lift φ) R (Fin.cases x ρ) ↔ satisfies φ R ρ := by
  exact satisfies_rename φ R Fin.succ (Fin.cases x ρ)

/-- Bounded quantifiers are finite abbreviations, not extra constructors. -/
def boundedAll {n : Nat} (x : Fin n) (p : SetFormula (n + 1)) : SetFormula n :=
  .all (.imp (.mem 0 x.succ) p)

def boundedEx {n : Nat} (x : Fin n) (p : SetFormula (n + 1)) : SetFormula n :=
  .ex (.conj (.mem 0 x.succ) p)

theorem satisfies_boundedAll {D : Type} {n : Nat} (x : Fin n)
    (p : SetFormula (n + 1)) (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (boundedAll x p) R ρ ↔
      ∀ z, R z (ρ x) → satisfies p R (Fin.cases z ρ) := Iff.rfl

theorem satisfies_boundedEx {D : Type} {n : Nat} (x : Fin n)
    (p : SetFormula (n + 1)) (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (boundedEx x p) R ρ ↔
      ∃ z, R z (ρ x) ∧ satisfies p R (Fin.cases z ρ) := Iff.rfl

def empty {n : Nat} (x : Fin n) : SetFormula n :=
  .all (.neg (.mem 0 x.succ))

def subset {n : Nat} (x y : Fin n) : SetFormula n :=
  .all (.imp (.mem 0 x.succ) (.mem 0 y.succ))

def singleton {n : Nat} (x s : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 s.succ) (.eq 0 x.succ))

def unorderedPair {n : Nat} (x y p : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 p.succ) (.disj (.eq 0 x.succ) (.eq 0 y.succ)))

/-- p = {{x}, {x,y}}, with both intermediate sets bound explicitly. -/
def orderedPair {n : Nat} (x y p : Fin n) : SetFormula n :=
  .ex (.ex (.conj
    (singleton x.succ.succ (0 : Fin (n + 1)).succ)
    (.conj (unorderedPair x.succ.succ y.succ.succ 0)
      (unorderedPair (0 : Fin (n + 1)).succ 0 p.succ.succ))))

/-- The ordered pair (x,y) belongs to the graph f. Functionhood is separate. -/
def graphApp {n : Nat} (f x y : Fin n) : SetFormula n :=
  .ex (.conj (orderedPair x.succ y.succ 0) (.mem 0 f.succ))

def graphOnlyPairs {n : Nat} (f : Fin n) : SetFormula n :=
  .all (.imp (.mem 0 f.succ)
    (.ex (.ex (orderedPair (0 : Fin (n + 2)).succ 0
      (0 : Fin (n + 1)).succ.succ))))

def rightUnique {n : Nat} (f : Fin n) : SetFormula n :=
  .all (.all (.all (.imp
    (.conj
      (graphApp f.succ.succ.succ (0 : Fin (n + 1)).succ.succ
        (0 : Fin (n + 2)).succ)
      (graphApp f.succ.succ.succ (0 : Fin (n + 1)).succ.succ 0))
    (.eq (0 : Fin (n + 2)).succ 0))))

/-- A graph is a function when every member is an ordered pair and outputs
are unique. No domain, range, or totality condition is hidden in this formula. -/
def functionGraph {n : Nat} (f : Fin n) : SetFormula n :=
  .conj (graphOnlyPairs f) (rightUnique f)

def graphDomain {n : Nat} (f d : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 d.succ)
    (.ex (graphApp f.succ.succ (0 : Fin (n + 1)).succ 0)))

def graphRange {n : Nat} (f r : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 r.succ)
    (.ex (graphApp f.succ.succ 0 (0 : Fin (n + 1)).succ)))

def transitive {n : Nat} (x : Fin n) : SetFormula n :=
  boundedAll x (subset 0 x.succ)

def union {n : Nat} (x u : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 u.succ)
    (.ex (.conj (.mem 0 x.succ.succ) (.mem (0 : Fin (n + 1)).succ 0))))

def powerSet {n : Nat} (x p : Fin n) : SetFormula n :=
  .all (.iff (.mem 0 p.succ) (subset 0 x.succ))

namespace Ordinary

variable {D : Type*} (R : D → D → Prop)

def Empty (x : D) : Prop := ∀ z, ¬ R z x
def Subset (x y : D) : Prop := ∀ z, R z x → R z y
def Singleton (x s : D) : Prop := ∀ z, R z s ↔ z = x
def UnorderedPair (x y p : D) : Prop := ∀ z, R z p ↔ z = x ∨ z = y
def OrderedPair (x y p : D) : Prop :=
  ∃ s t, Singleton R x s ∧ UnorderedPair R x y t ∧ UnorderedPair R s t p
def GraphApp (f x y : D) : Prop := ∃ p, OrderedPair R x y p ∧ R p f
def GraphOnlyPairs (f : D) : Prop := ∀ p, R p f → ∃ x y, OrderedPair R x y p
def RightUnique (f : D) : Prop :=
  ∀ x y z, (GraphApp R f x y ∧ GraphApp R f x z) → y = z
def FunctionGraph (f : D) : Prop := GraphOnlyPairs R f ∧ RightUnique R f
def GraphDomain (f d : D) : Prop := ∀ x, R x d ↔ ∃ y, GraphApp R f x y
def GraphRange (f r : D) : Prop := ∀ y, R y r ↔ ∃ x, GraphApp R f x y
def Transitive (x : D) : Prop := ∀ y, R y x → Subset R y x
def Union (x u : D) : Prop := ∀ z, R z u ↔ ∃ y, R y x ∧ R z y
def PowerSet (x p : D) : Prop := ∀ z, R z p ↔ Subset R z x

end Ordinary

theorem satisfies_empty {D : Type} {n : Nat} (x : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (empty x) R ρ ↔ Ordinary.Empty R (ρ x) := Iff.rfl

theorem satisfies_subset {D : Type} {n : Nat} (x y : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (subset x y) R ρ ↔ Ordinary.Subset R (ρ x) (ρ y) := Iff.rfl

theorem satisfies_singleton {D : Type} {n : Nat} (x s : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (singleton x s) R ρ ↔ Ordinary.Singleton R (ρ x) (ρ s) := Iff.rfl

theorem satisfies_unorderedPair {D : Type} {n : Nat} (x y p : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (unorderedPair x y p) R ρ ↔
      Ordinary.UnorderedPair R (ρ x) (ρ y) (ρ p) := Iff.rfl

theorem satisfies_orderedPair {D : Type} {n : Nat} (x y p : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (orderedPair x y p) R ρ ↔
      Ordinary.OrderedPair R (ρ x) (ρ y) (ρ p) := Iff.rfl

theorem satisfies_graphApp {D : Type} {n : Nat} (f x y : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (graphApp f x y) R ρ ↔
      Ordinary.GraphApp R (ρ f) (ρ x) (ρ y) := Iff.rfl

theorem satisfies_graphOnlyPairs {D : Type} {n : Nat} (f : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (graphOnlyPairs f) R ρ ↔ Ordinary.GraphOnlyPairs R (ρ f) := Iff.rfl

theorem satisfies_rightUnique {D : Type} {n : Nat} (f : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (rightUnique f) R ρ ↔ Ordinary.RightUnique R (ρ f) := Iff.rfl

theorem satisfies_functionGraph {D : Type} {n : Nat} (f : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (functionGraph f) R ρ ↔ Ordinary.FunctionGraph R (ρ f) := Iff.rfl

theorem satisfies_graphDomain {D : Type} {n : Nat} (f d : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (graphDomain f d) R ρ ↔ Ordinary.GraphDomain R (ρ f) (ρ d) := Iff.rfl

theorem satisfies_graphRange {D : Type} {n : Nat} (f r : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (graphRange f r) R ρ ↔ Ordinary.GraphRange R (ρ f) (ρ r) := Iff.rfl

theorem satisfies_transitive {D : Type} {n : Nat} (x : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (transitive x) R ρ ↔ Ordinary.Transitive R (ρ x) := Iff.rfl

theorem satisfies_union {D : Type} {n : Nat} (x u : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (union x u) R ρ ↔ Ordinary.Union R (ρ x) (ρ u) := Iff.rfl

theorem satisfies_powerSet {D : Type} {n : Nat} (x p : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (powerSet x p) R ρ ↔ Ordinary.PowerSet R (ρ x) (ρ p) := Iff.rfl

namespace Ordinary

universe u

theorem empty_zfSet (x : ZFSet.{u}) :
    Empty (fun a b : ZFSet.{u} => a ∈ b) x ↔ x = ∅ :=
  (ZFSet.eq_empty x).symm

theorem subset_zfSet (x y : ZFSet.{u}) :
    Subset (fun a b : ZFSet.{u} => a ∈ b) x y ↔ x ⊆ y := by
  constructor
  · intro h z hz
    exact h z hz
  · intro h z hz
    exact h hz

theorem singleton_zfSet (x s : ZFSet.{u}) :
    Singleton (fun a b : ZFSet.{u} => a ∈ b) x s ↔ s = {x} := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    exact (h z).trans ZFSet.mem_singleton.symm
  · rintro rfl z
    exact ZFSet.mem_singleton

theorem unorderedPair_zfSet (x y p : ZFSet.{u}) :
    UnorderedPair (fun a b : ZFSet.{u} => a ∈ b) x y p ↔ p = {x, y} := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    exact (h z).trans ZFSet.mem_pair.symm
  · rintro rfl z
    exact ZFSet.mem_pair

theorem orderedPair_zfSet (x y p : ZFSet.{u}) :
    OrderedPair (fun a b : ZFSet.{u} => a ∈ b) x y p ↔ p = ZFSet.pair x y := by
  constructor
  · rintro ⟨s, t, hs, ht, hp⟩
    have hs' : s = {x} := (singleton_zfSet x s).1 hs
    have ht' : t = {x, y} := (unorderedPair_zfSet x y t).1 ht
    have hp' : p = {s, t} := (unorderedPair_zfSet s t p).1 hp
    simpa only [hs', ht', ZFSet.pair] using hp'
  · intro hp
    refine ⟨{x}, {x, y}, ?_, ?_, ?_⟩
    · exact (singleton_zfSet x {x}).2 rfl
    · exact (unorderedPair_zfSet x y {x, y}).2 rfl
    · exact (unorderedPair_zfSet {x} {x, y} p).2 hp

theorem graphApp_zfSet (f x y : ZFSet.{u}) :
    GraphApp (fun a b : ZFSet.{u} => a ∈ b) f x y ↔ ZFSet.pair x y ∈ f := by
  constructor
  · rintro ⟨p, hp, hf⟩
    exact (orderedPair_zfSet x y p).1 hp ▸ hf
  · intro h
    exact ⟨ZFSet.pair x y, (orderedPair_zfSet x y _).2 rfl, h⟩

theorem functionGraph_zfSet (f : ZFSet.{u}) :
    FunctionGraph (fun a b : ZFSet.{u} => a ∈ b) f ↔
      (∀ p ∈ f, ∃ x y, p = ZFSet.pair x y) ∧
      (∀ x y z, (ZFSet.pair x y ∈ f ∧ ZFSet.pair x z ∈ f) → y = z) := by
  simp only [FunctionGraph, GraphOnlyPairs, RightUnique,
    orderedPair_zfSet, graphApp_zfSet]

theorem graphDomain_zfSet (f d : ZFSet.{u}) :
    GraphDomain (fun a b : ZFSet.{u} => a ∈ b) f d ↔
      ∀ x, x ∈ d ↔ ∃ y, ZFSet.pair x y ∈ f := by
  simp only [GraphDomain, graphApp_zfSet]

theorem graphRange_zfSet (f r : ZFSet.{u}) :
    GraphRange (fun a b : ZFSet.{u} => a ∈ b) f r ↔
      ∀ y, y ∈ r ↔ ∃ x, ZFSet.pair x y ∈ f := by
  simp only [GraphRange, graphApp_zfSet]

theorem union_zfSet (x u : ZFSet.{u}) :
    Union (fun a b : ZFSet.{u} => a ∈ b) x u ↔ u = ZFSet.sUnion x := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    exact (h z).trans ZFSet.mem_sUnion.symm
  · rintro rfl z
    exact ZFSet.mem_sUnion

theorem powerSet_zfSet (x p : ZFSet.{u}) :
    PowerSet (fun a b : ZFSet.{u} => a ∈ b) x p ↔ p = ZFSet.powerset x := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    exact ((h z).trans (subset_zfSet z x)).trans ZFSet.mem_powerset.symm
  · rintro rfl z
    exact ZFSet.mem_powerset.trans (subset_zfSet z x).symm

end Ordinary

end Classicism.Meta.Research.MaxAtomicitySetFormulaTools

#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.satisfies_rename
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.satisfies_lift
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.satisfies_orderedPair
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.satisfies_graphApp
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.satisfies_functionGraph
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.satisfies_graphDomain
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.satisfies_graphRange
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.Ordinary.orderedPair_zfSet
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.Ordinary.graphApp_zfSet
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.Ordinary.functionGraph_zfSet
#print axioms Classicism.Meta.Research.MaxAtomicitySetFormulaTools.Ordinary.powerSet_zfSet
