import ClassicismZFC.CHTranslation
import ClassicismZFC.Product

/-!
# Internally coded cardinal maps

Original source, misc, 23 October 2026. Every graph and subset quantified
below is an element of the actual first-order membership model. Graphs are
constructed by instances of the finite syntactic Separation scheme. No
external map on a possibly countable carrier is substituted for an internal
map. The pairing symbol is only required to satisfy its actual ZFC axiom.

This module proves graph inversion, composition, restriction to an internal
image, and the injection-to-partial-surjection implication used by the pinned
ordinal CH sentence. It does NOT assume or prove internal well-ordering,
Schroeder--Bernstein, or a cardinal identification of an internal real field.
Those are separate obligations. Source only; not compiler-certified.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.CHCardinality

open SetLaws

universe u
variable {M : Type u} [L.Structure M]

def Subset (A B : M) : Prop := ∀ x, memM x A → memM x B

def Edge (G x y : M) : Prop := memM (pairM x y) G

def Functional (G : M) : Prop := ∀ x y z, Edge G x y → Edge G x z → y = z

def Injection (A B G : M) : Prop :=
  (∀ x y, Edge G x y → memM x A ∧ memM y B) ∧
  (∀ x, memM x A → ∃ y, Edge G x y) ∧
  Functional G ∧
  (∀ x y z, Edge G x z → Edge G y z → x = y)

def Bijection (A B G : M) : Prop :=
  Injection A B G ∧ ∀ y, memM y B → ∃ x, Edge G x y

def Injects (A B : M) : Prop := ∃ G, Injection A B G

def Equinumerous (A B : M) : Prop := ∃ G, Bijection A B G

/-- Exact semantic content of the pinned `atMostF`: a subset of the larger
set carries an internally coded partial surjection onto the smaller set.
The graph need not be normalized outside its stated domain. -/
def AtMost (smaller larger : M) : Prop :=
  ∃ S G, Subset S larger ∧ Functional G ∧
    (∀ x, memM x S → ∃ y, memM y smaller ∧ Edge G x y) ∧
    (∀ y, memM y smaller → ∃ x, memM x S ∧ Edge G x y)

/-- Separation in a product, with the formula and finite parameter tuple
explicit. This is a construction theorem, not an external-definability axiom. -/
theorem graph_separation (hZFC : M ⊨ Erdos501.FOL.ZFC) (n : ℕ)
    (φ : L.BoundedFormula Empty (n + 1)) (p : Fin n → M) (A B : M) :
    ∃ G, ∀ x y, Edge G x y ↔ memM x A ∧ memM y B ∧
      φ.Realize default (Fin.snoc p (pairM x y)) := by
  obtain ⟨G, hG⟩ := Separation.separation hZFC n φ p (Product.product hZFC A B)
  refine ⟨G, ?_⟩
  intro x y
  rw [Edge, hG, Product.product_mem]
  constructor
  · rintro ⟨⟨a, b, ha, hb, hab⟩, hφ⟩
    obtain ⟨rfl, rfl⟩ := pair_injective hZFC x y a b hab
    exact ⟨ha, hb, hφ⟩
  · rintro ⟨hx, hy, hφ⟩
    exact ⟨⟨x, y, hx, hy, rfl⟩, hφ⟩

/-- `z = (x,y)` and the reversed edge `(y,x) ∈ G`; levels `G,z,x,y`. -/
def reverseFilter : L.BoundedFormula Empty 2 :=
  (exF fun x => exF fun y =>
    andF (eqF (varT 1) (pairT (varT x) (varT y)))
      (memF (pairT (varT y) (varT x)) (varT 0))) 2

theorem realize_reverseFilter (G z : M) :
    reverseFilter.Realize default (Fin.snoc ![G] z) ↔
      ∃ x y, z = pairM x y ∧ Edge G y x := by
  simp [reverseFilter, exF, andF, eqF, memF, varT, Edge, memM, Fin.snoc]

theorem reverse_graph (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B G : M) :
    ∃ H, ∀ x y, Edge H x y ↔ memM x B ∧ memM y A ∧ Edge G y x := by
  obtain ⟨H, hH⟩ := graph_separation hZFC 1 reverseFilter ![G] B A
  refine ⟨H, ?_⟩
  intro x y
  rw [hH, realize_reverseFilter]
  constructor
  · rintro ⟨hx, hy, a, b, heq, hG⟩
    obtain ⟨rfl, rfl⟩ := pair_injective hZFC x y a b heq
    exact ⟨hx, hy, hG⟩
  · rintro ⟨hx, hy, hG⟩
    exact ⟨hx, hy, x, y, rfl, hG⟩

/-- `z = (x,y)` and `G(x,w)` and `H(w,y)`; levels `G,H,z,x,y,w`. -/
def composeFilter : L.BoundedFormula Empty 3 :=
  (exF fun x => exF fun y => exF fun w =>
    andF (eqF (varT 2) (pairT (varT x) (varT y)))
      (andF (memF (pairT (varT x) (varT w)) (varT 0))
        (memF (pairT (varT w) (varT y)) (varT 1)))) 3

theorem realize_composeFilter (G H z : M) :
    composeFilter.Realize default (Fin.snoc ![G, H] z) ↔
      ∃ x y w, z = pairM x y ∧ Edge G x w ∧ Edge H w y := by
  simp [composeFilter, exF, andF, eqF, memF, varT, Edge, memM, Fin.snoc]

theorem compose_graph (hZFC : M ⊨ Erdos501.FOL.ZFC) (A C G H : M) :
    ∃ K, ∀ x z, Edge K x z ↔ memM x A ∧ memM z C ∧
      ∃ y, Edge G x y ∧ Edge H y z := by
  obtain ⟨K, hK⟩ := graph_separation hZFC 2 composeFilter ![G, H] A C
  refine ⟨K, ?_⟩
  intro x z
  rw [hK, realize_composeFilter]
  constructor
  · rintro ⟨hx, hz, a, b, y, heq, hG, hH⟩
    obtain ⟨rfl, rfl⟩ := pair_injective hZFC x z a b heq
    exact ⟨hx, hz, y, hG, hH⟩
  · rintro ⟨hx, hz, y, hG, hH⟩
    exact ⟨hx, hz, x, z, y, rfl, hG, hH⟩

/-- Finite syntax for an image: `∃x ∈ A, G(x,z)`. -/
def imageFilter : L.BoundedFormula Empty 3 :=
  (exF fun x => andF (memF (varT x) (varT 0))
    (memF (pairT (varT x) (varT 2)) (varT 1))) 3

theorem realize_imageFilter (A G z : M) :
    imageFilter.Realize default (Fin.snoc ![A, G] z) ↔
      ∃ x, memM x A ∧ Edge G x z := by
  simp [imageFilter, exF, andF, memF, varT, Edge, memM, Fin.snoc]

theorem image_set (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B G : M) :
    ∃ I, ∀ y, memM y I ↔ memM y B ∧ ∃ x, memM x A ∧ Edge G x y := by
  obtain ⟨I, hI⟩ := Separation.separation hZFC 2 imageFilter ![A, G] B
  exact ⟨I, fun y => by rw [hI y, realize_imageFilter]⟩

/-- Filtering an existing graph is also a finite syntactic instance. -/
def memberFilter : L.BoundedFormula Empty 2 := memF (varT 1) (varT 0) 2

theorem realize_memberFilter (G z : M) :
    memberFilter.Realize default (Fin.snoc ![G] z) ↔ memM z G := by
  simp [memberFilter, memF, varT, memM, Fin.snoc]

theorem restrict_graph (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B G : M) :
    ∃ H, ∀ x y, Edge H x y ↔ memM x A ∧ memM y B ∧ Edge G x y := by
  obtain ⟨H, hH⟩ := graph_separation hZFC 1 memberFilter ![G] A B
  exact ⟨H, fun x y => by rw [hH x y, realize_memberFilter]; rfl⟩

theorem inverse_bijection (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B G : M} (hG : Bijection A B G) : ∃ H, Bijection B A H := by
  obtain ⟨H, hH⟩ := reverse_graph hZFC A B G
  refine ⟨H, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y h
    exact ⟨((hH x y).mp h).1, ((hH x y).mp h).2.1⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hG.2 x hx
    exact ⟨y, (hH x y).mpr ⟨hx, (hG.1.1 y x hy).1, hy⟩⟩
  · intro x y z hxy hxz
    exact hG.1.2.2.2 y z x ((hH x y).mp hxy).2.2 ((hH x z).mp hxz).2.2
  · intro x y z hxz hyz
    exact hG.1.2.2.1 z x y ((hH x z).mp hxz).2.2 ((hH y z).mp hyz).2.2
  · intro y hy
    obtain ⟨x, hx⟩ := hG.1.2.1 y hy
    exact ⟨x, (hH x y).mpr ⟨(hG.1.1 y x hx).2, hy, hx⟩⟩

theorem compose_injection (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B C G H : M} (hG : Injection A B G) (hH : Injection B C H) :
    ∃ K, Injection A C K := by
  obtain ⟨K, hK⟩ := compose_graph hZFC A C G H
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro x z h
    exact ⟨((hK x z).mp h).1, ((hK x z).mp h).2.1⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := hG.2.1 x hx
    obtain ⟨z, hyz⟩ := hH.2.1 y (hG.1 x y hxy).2
    exact ⟨z, (hK x z).mpr ⟨hx, (hH.1 y z hyz).2, y, hxy, hyz⟩⟩
  · intro x z z' hxz hxz'
    obtain ⟨_, _, y, hxy, hyz⟩ := (hK x z).mp hxz
    obtain ⟨_, _, y', hxy', hyz'⟩ := (hK x z').mp hxz'
    have heq : y = y' := hG.2.2.1 x y y' hxy hxy'
    subst y'
    exact hH.2.2.1 y z z' hyz hyz'
  · intro x x' z hxz hxz'
    obtain ⟨_, _, y, hxy, hyz⟩ := (hK x z).mp hxz
    obtain ⟨_, _, y', hxy', hyz'⟩ := (hK x' z).mp hxz'
    have heq : y = y' := hH.2.2.2 y y' z hyz hyz'
    subst y'
    exact hG.2.2.2 x x' y hxy hxy'

theorem compose_bijection (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B C G H : M} (hG : Bijection A B G) (hH : Bijection B C H) :
    ∃ K, Bijection A C K := by
  obtain ⟨K, hK⟩ := compose_graph hZFC A C G H
  have hinj : Injection A C K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x z h
      exact ⟨((hK x z).mp h).1, ((hK x z).mp h).2.1⟩
    · intro x hx
      obtain ⟨y, hxy⟩ := hG.1.2.1 x hx
      obtain ⟨z, hyz⟩ := hH.1.2.1 y (hG.1.1 x y hxy).2
      exact ⟨z, (hK x z).mpr ⟨hx, (hH.1.1 y z hyz).2, y, hxy, hyz⟩⟩
    · intro x z z' hxz hxz'
      obtain ⟨_, _, y, hxy, hyz⟩ := (hK x z).mp hxz
      obtain ⟨_, _, y', hxy', hyz'⟩ := (hK x z').mp hxz'
      have heq : y = y' := hG.1.2.2.1 x y y' hxy hxy'
      subst y'
      exact hH.1.2.2.1 y z z' hyz hyz'
    · intro x x' z hxz hxz'
      obtain ⟨_, _, y, hxy, hyz⟩ := (hK x z).mp hxz
      obtain ⟨_, _, y', hxy', hyz'⟩ := (hK x' z).mp hxz'
      have heq : y = y' := hH.1.2.2.2 y y' z hyz hyz'
      subst y'
      exact hG.1.2.2.2 x x' y hxy hxy'
  refine ⟨K, hinj, ?_⟩
  intro z hz
  obtain ⟨y, hyz⟩ := hH.2 z hz
  obtain ⟨x, hxy⟩ := hG.2 y (hH.1.1 y z hyz).1
  exact ⟨x, (hK x z).mpr ⟨(hG.1.1 x y hxy).1, hz, y, hxy, hyz⟩⟩

/-- Restrict a coded injection to an internal subset and obtain its internal
image together with an actual internally coded bijection onto that image. -/
theorem restrict_to_image (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B G Y : M} (hG : Injection A B G) (hY : Subset Y A) :
    ∃ I H, Subset I B ∧ Bijection Y I H := by
  obtain ⟨I, hI⟩ := image_set hZFC Y B G
  obtain ⟨H, hH⟩ := restrict_graph hZFC Y I G
  refine ⟨I, H, fun y hy => ((hI y).mp hy).1, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y h
    exact ⟨((hH x y).mp h).1, ((hH x y).mp h).2.1⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := hG.2.1 x (hY x hx)
    have hy : memM y I := (hI y).mpr ⟨(hG.1 x y hxy).2, x, hx, hxy⟩
    exact ⟨y, (hH x y).mpr ⟨hx, hy, hxy⟩⟩
  · intro x y z hxy hxz
    exact hG.2.2.1 x y z ((hH x y).mp hxy).2.2 ((hH x z).mp hxz).2.2
  · intro x y z hxz hyz
    exact hG.2.2.2 x y z ((hH x z).mp hxz).2.2 ((hH y z).mp hyz).2.2
  · intro y hy
    obtain ⟨_, x, hx, hxy⟩ := (hI y).mp hy
    exact ⟨x, (hH x y).mpr ⟨hx, hy, hxy⟩⟩

/-- An internal injection supplies the precise internal partial-surjection
witness used by the ordinal CH sentence. This direction uses no choice
selection: reverse the injection on its internally constructed image. -/
theorem atMost_of_injects (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B : M} (h : Injects A B) : AtMost A B := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨I, H, hIB, hH⟩ := restrict_to_image hZFC hG (fun _ hx => hx)
  obtain ⟨J, hJ⟩ := inverse_bijection hZFC hH
  refine ⟨I, J, hIB, hJ.1.2.2.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := hJ.1.2.1 x hx
    exact ⟨y, (hJ.1.1 x y hxy).2, hxy⟩
  · intro y hy
    obtain ⟨x, hxy⟩ := hJ.2 y hy
    exact ⟨x, (hJ.1.1 x y hxy).1, hxy⟩

/-- The literal four-variable functionality presentation in `atMostF`. -/
def RawAtMost (A B : M) : Prop :=
  ∃ S G, (Subset S B ∧
    ((∀ a b c d, Edge G a c ∧ Edge G b d → a = b → c = d) ∧
      (∀ x, memM x S → ∃ y, memM y A ∧ Edge G x y))) ∧
    (∀ y, memM y A → ∃ x, memM x S ∧ Edge G x y)

theorem rawAtMost_iff (A B : M) : RawAtMost A B ↔ AtMost A B := by
  constructor
  · rintro ⟨S, G, ⟨hS, hG, ht⟩, hs⟩
    exact ⟨S, G, hS, fun x y z hxy hxz => hG x x y z ⟨hxy, hxz⟩ rfl, ht, hs⟩
  · rintro ⟨S, G, hS, hG, ht, hs⟩
    refine ⟨S, G, ⟨hS, ?_, ht⟩, hs⟩
    intro x x' y y' he hxx'
    subst x'
    exact hG x y y' he.1 he.2

/-- Exact interpretation of the pinned cardinal-comparison template. -/
theorem realize_atMost (A B : M) :
    (CHTranslation.atMostF (varT 1) (varT 0) 2).Realize default ![B, A] ↔
      AtMost A B := by
  have hraw :
      (CHTranslation.atMostF (varT 1) (varT 0) 2).Realize default ![B, A] ↔
        RawAtMost A B := by
    simp [CHTranslation.atMostF, CHTranslation.functionalGraphF,
      CHTranslation.totalGraphF, RawAtMost, Subset, Edge,
      subsetF, allF, exF, andF, impF, eqF, memF, varT, memM, Fin.snoc]
  exact hraw.trans (rawAtMost_iff A B)

#print axioms graph_separation
#print axioms reverse_graph
#print axioms compose_graph
#print axioms image_set
#print axioms restrict_to_image
#print axioms atMost_of_injects
#print axioms realize_atMost

end ClassicismZFC.CHCardinality
