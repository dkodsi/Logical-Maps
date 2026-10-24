import ClassicismZFC.CHOrdinalDirection
import ClassicismZFC.CountableInitialSegments

/-!
# Structural CH from an ordinal with countable initial segments

Original source, misc, 23 October 2026. This specializes the internal
well-order criterion to the literal ordinal predicate in the pinned source.
The membership graph and the finite sets used to exclude membership cycles
are constructed by finite syntactic Separation. No external well-foundedness
of a possibly nonstandard membership model is assumed.

For a member a of the ordinal A, its predecessor set is the actual internal
set a. Thus the supplied internal injections a -> N are precisely the
countable-initial-segment witnesses needed by the criterion. In particular,
an actual ordinal cover of P(omega), together with countable members,
suffices; no theorem representing every internal set by an ordinal is used.

Source only; no compiler has been run for this module.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.OrdinalInitialSegments

open SetLaws CHCardinality CHFieldTransport CHOrdinalDirection
open CountableInitialSegments

universe u
variable {M : Type u} [L.Structure M]

/-- Finite syntax selecting three specified points; initial levels a,b,c,z. -/
def threePointFilter : L.BoundedFormula Empty 4 :=
  orF (eqF (varT 3) (varT 0))
    (orF (eqF (varT 3) (varT 1)) (eqF (varT 3) (varT 2))) 4

theorem realize_threePointFilter (a b c z : M) :
    threePointFilter.Realize default (Fin.snoc ![a, b, c] z) ↔
      z = a ∨ z = b ∨ z = c := by
  simp [threePointFilter, orF, eqF, varT, Fin.snoc]

/-- A genuinely internal finite subset, including when some points coincide. -/
theorem threePointSet (hZFC : M ⊨ Erdos501.FOL.ZFC) {A a b c : M}
    (ha : memM a A) (hb : memM b A) (hc : memM c A) :
    ∃ B, Subset B A ∧ ∀ z, memM z B ↔ z = a ∨ z = b ∨ z = c := by
  obtain ⟨B, hB⟩ := Separation.separation hZFC 3 threePointFilter ![a, b, c] A
  refine ⟨B, fun z hz => ((hB z).mp hz).1, ?_⟩
  intro z
  rw [hB z, realize_threePointFilter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rcases h with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc

theorem ordinal_not_mem_self (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A a : M} (hA : IsOrdinal A) (ha : memM a A) : ¬ memM a a := by
  intro haa
  obtain ⟨B, hBA, hB⟩ := threePointSet hZFC ha ha ha
  have haB : memM a B := (hB a).mpr (Or.inl rfl)
  have hne : B ≠ emptyM := fun he => empty_mem hZFC a (he ▸ haB)
  obtain ⟨m, hm, hmin⟩ := hA.1.2 B hBA hne
  have hma : m = a := ((hB m).mp hm).elim id (fun h => h.elim id id)
  subst m
  exact hmin a haB haa

theorem ordinal_not_mem_cycle_two (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A a b : M} (hA : IsOrdinal A) (ha : memM a A) (hb : memM b A)
    (hab : memM a b) (hba : memM b a) : False := by
  obtain ⟨B, hBA, hB⟩ := threePointSet hZFC ha hb hb
  have haB : memM a B := (hB a).mpr (Or.inl rfl)
  have hbB : memM b B := (hB b).mpr (Or.inr (Or.inl rfl))
  have hne : B ≠ emptyM := fun he => empty_mem hZFC a (he ▸ haB)
  obtain ⟨m, hm, hmin⟩ := hA.1.2 B hBA hne
  rcases (hB m).mp hm with hm | hm | hm
  · subst m
    exact hmin b hbB hba
  · subst m
    exact hmin a haB hab
  · subst m
    exact hmin a haB hab

theorem ordinal_not_mem_cycle_three (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A a b c : M} (hA : IsOrdinal A)
    (ha : memM a A) (hb : memM b A) (hc : memM c A)
    (hab : memM a b) (hbc : memM b c) (hca : memM c a) : False := by
  obtain ⟨B, hBA, hB⟩ := threePointSet hZFC ha hb hc
  have haB : memM a B := (hB a).mpr (Or.inl rfl)
  have hbB : memM b B := (hB b).mpr (Or.inr (Or.inl rfl))
  have hcB : memM c B := (hB c).mpr (Or.inr (Or.inr rfl))
  have hne : B ≠ emptyM := fun he => empty_mem hZFC a (he ▸ haB)
  obtain ⟨m, hm, hmin⟩ := hA.1.2 B hBA hne
  rcases (hB m).mp hm with hm | hm | hm
  · subst m
    exact hmin c hcB hca
  · subst m
    exact hmin a haB hab
  · subst m
    exact hmin b hbB hbc

/-- Trichotomy and internal minimality give transitivity on the ordinal. -/
theorem ordinal_mem_trans (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A a b c : M} (hA : IsOrdinal A)
    (ha : memM a A) (hb : memM b A) (hc : memM c A)
    (hab : memM a b) (hbc : memM b c) : memM a c := by
  rcases hA.1.1 a ha c hc with (hac | hac) | hca
  · subst c
    exact False.elim (ordinal_not_mem_cycle_two hZFC hA ha hb hab hbc)
  · exact hac
  · exact False.elim (ordinal_not_mem_cycle_three hZFC hA ha hb hc hab hbc hca)

/-- Finite syntax selecting exactly the membership edges; initial level z. -/
def membershipFilter : L.BoundedFormula Empty 1 :=
  (exF fun x => exF fun y =>
    andF (eqF (varT 0) (pairT (varT x) (varT y)))
      (memF (varT x) (varT y))) 1

theorem realize_membershipFilter (z : M) :
    membershipFilter.Realize default (Fin.snoc ![] z) ↔
      ∃ x y, z = pairM x y ∧ memM x y := by
  simp [membershipFilter, exF, andF, eqF, memF, varT, memM, Fin.snoc]

/-- The membership relation on A is an actual internally coded graph. -/
theorem membership_graph (hZFC : M ⊨ Erdos501.FOL.ZFC) (A : M) :
    ∃ W, ∀ x y, Edge W x y ↔ memM x A ∧ memM y A ∧ memM x y := by
  obtain ⟨W, hW⟩ := graph_separation hZFC 0 membershipFilter ![] A A
  refine ⟨W, ?_⟩
  intro x y
  rw [hW x y, realize_membershipFilter]
  constructor
  · rintro ⟨hx, hy, a, b, heq, hab⟩
    obtain ⟨rfl, rfl⟩ := pair_injective hZFC x y a b heq
    exact ⟨hx, hy, hab⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, x, y, rfl, hxy⟩

theorem membership_wellOrder (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A W : M} (hA : IsOrdinal A)
    (hW : ∀ x y, Edge W x y ↔ memM x A ∧ memM y A ∧ memM x y) :
    InternalWellOrder A W := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact ⟨((hW x y).mp hxy).1, ((hW x y).mp hxy).2.1⟩
  · intro x hx hxx
    exact ordinal_not_mem_self hZFC hA hx ((hW x x).mp hxx).2.2
  · intro x y z hxy hyz
    have hxy' := (hW x y).mp hxy
    have hyz' := (hW y z).mp hyz
    exact (hW x z).mpr ⟨hxy'.1, hyz'.2.1,
      ordinal_mem_trans hZFC hA hxy'.1 hxy'.2.1 hyz'.2.1 hxy'.2.2 hyz'.2.2⟩
  · intro x y hx hy
    rcases hA.1.1 x hx y hy with (heq | hxy) | hyx
    · exact Or.inl heq
    · exact Or.inr (Or.inl ((hW x y).mpr ⟨hx, hy, hxy⟩))
    · exact Or.inr (Or.inr ((hW y x).mpr ⟨hy, hx, hyx⟩))
  · intro B hBA hne
    obtain ⟨a, ha, hmin⟩ := hA.1.2 B hBA hne
    refine ⟨a, ha, ?_⟩
    intro b hb hba
    exact hmin b hb ((hW b a).mp hba).2.2

/-- Each predecessor set is literally the internal ordinal element a. -/
theorem membership_countableSegments {A W N : M} (hA : IsOrdinal A)
    (hW : ∀ x y, Edge W x y ↔ memM x A ∧ memM y A ∧ memM x y)
    (hcount : ∀ a, memM a A → Injects a N) : CountableSegments A W N := by
  intro a ha
  refine ⟨a, ?_, hcount a ha⟩
  intro x
  constructor
  · intro hx
    have hxA : memM x A := hA.2 a ha x hx
    exact ⟨hxA, (hW x a).mpr ⟨hxA, ha, hx⟩⟩
  · intro hx
    exact ((hW x a).mp hx.2).2.2

/-- An ordinal cover with countable members supplies structural CH. -/
theorem structuralCH_of_ordinal_cover (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {R N A : M} (hA : IsOrdinal A)
    (hcount : ∀ a, memM a A → Injects a N) (hRA : Injects R A) :
    StructuralCH R N := by
  obtain ⟨W, hW⟩ := membership_graph hZFC A
  exact structuralCH_of_countable_segments hZFC
    (membership_wellOrder hZFC hA hW)
    (membership_countableSegments hA hW hcount) hRA

/-- The exact ordinary semantic clauses supplied by the collapse witness.
The partial surjection becomes an injection by the proved internal Zorn
selection theorem, after ordinary model extraction. -/
theorem structuralCH_of_ordinal_atMost (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A : M} (hA : IsOrdinal A)
    (hcount : ∀ a, memM a A → Injects a (omegaM : M))
    (hcover : AtMost (powerM (omegaM : M)) A) :
    StructuralCH (powerM (omegaM : M)) omegaM :=
  structuralCH_of_ordinal_cover hZFC hA hcount (injects_of_atMost hZFC hcover)

#print axioms threePointSet
#print axioms ordinal_mem_trans
#print axioms membership_graph
#print axioms membership_wellOrder
#print axioms membership_countableSegments
#print axioms structuralCH_of_ordinal_cover
#print axioms structuralCH_of_ordinal_atMost

end ClassicismZFC.OrdinalInitialSegments
