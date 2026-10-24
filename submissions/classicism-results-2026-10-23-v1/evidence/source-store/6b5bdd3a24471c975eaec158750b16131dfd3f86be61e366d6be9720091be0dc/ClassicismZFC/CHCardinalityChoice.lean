import ClassicismZFC.CHCardinalitySchroederBernstein

/-!
# Internal selection and cardinal comparison from the actual Zorn axiom

All partial graphs are elements of an internal powerset. The family of
partial one-to-one graphs is selected by an explicit finite formula. Its
chain unions and one-edge extensions are actual internal sets. Thus the
Zorn axiom of the source ZFC theory, rather than external choice on the
carrier, supplies the required maximal graph.

Original source, misc, 23 October 2026. Source only, uncompiled.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.CHCardinality

open SetLaws
universe u
variable {M : Type u} [L.Structure M]

def OneToOne (G : M) : Prop := ∀ x y z, Edge G x z → Edge G y z → x = y

def Partial (P R G : M) : Prop :=
  Subset G P ∧ Subset G R ∧ Functional G ∧ OneToOne G

def functionalF (G : Tm) : Fm := allF fun x => allF fun y => allF fun z =>
  impF (andF (memF (pairT (varT x) (varT y)) G)
    (memF (pairT (varT x) (varT z)) G)) (eqF (varT y) (varT z))

def oneToOneF (G : Tm) : Fm := allF fun x => allF fun y => allF fun z =>
  impF (andF (memF (pairT (varT x) (varT z)) G)
    (memF (pairT (varT y) (varT z)) G)) (eqF (varT x) (varT y))

/-- Initial levels `R,G`. Bounding G by P is handled by separation from P(P). -/
def partialFilter : L.BoundedFormula Empty 2 :=
  andF (subsetF (varT 1) (varT 0))
    (andF (functionalF (varT 1)) (oneToOneF (varT 1))) 2

theorem realize_partialFilter (R G : M) :
    partialFilter.Realize default (Fin.snoc ![R] G) ↔
      Subset G R ∧ Functional G ∧ OneToOne G := by
  simp [partialFilter, functionalF, oneToOneF, Subset, Functional, OneToOne,
    Edge, subsetF, allF, andF, impF, eqF, memF, varT, memM, Fin.snoc]

theorem partial_family (hZFC : M ⊨ Erdos501.FOL.ZFC) (P R : M) :
    ∃ X, ∀ G, memM G X ↔ Partial P R G := by
  obtain ⟨X, hX⟩ := Separation.separation hZFC 1 partialFilter ![R] (powerM P)
  refine ⟨X, ?_⟩
  intro G
  rw [hX G, power_mem hZFC, realize_partialFilter]
  rfl

/-- The semantic Zorn principle is extracted from the actual source sentence. -/
theorem internal_zorn (hZFC : M ⊨ Erdos501.FOL.ZFC) (X : M)
    (hne : X ≠ emptyM)
    (hchain : ∀ Y, Subset Y X →
      (∀ U V, memM U Y → memM V Y → Subset U V ∨ Subset V U) →
      memM (unionM Y) X) :
    ∃ G, memM G X ∧ ∀ H, memM H X → Subset G H → G = H := by
  have hz := hZFC.realize_of_mem zornsLemma (by simp [Erdos501.FOL.ZFC])
  have hz' : ∀ X : M, X ≠ emptyM →
      (∀ Y, Subset Y X ∧
        (∀ U V, memM U Y ∧ memM V Y → Subset U V ∨ Subset V U) →
        memM (unionM Y) X) →
      ∃ G, memM G X ∧ ∀ H, memM H X → Subset G H → G = H := by
    simpa [zornsLemma, toSentence, Subset, subsetF, allF, exF, andF, orF,
      impF, notF, eqF, memF, varT, Sentence.Realize, Formula.Realize, memM, Fin.snoc] using hz
  exact hz' X hne (fun Y hY => hchain Y hY.1 (fun U V hU hV => hY.2 U V ⟨hU, hV⟩))

theorem partial_empty (hZFC : M ⊨ Erdos501.FOL.ZFC) (P R : M) :
    Partial P R emptyM := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz; exact False.elim (empty_mem hZFC z hz)
  · intro z hz; exact False.elim (empty_mem hZFC z hz)
  · intro x y z hxy _; exact False.elim (empty_mem hZFC (pairM x y) hxy)
  · intro x y z hxz _; exact False.elim (empty_mem hZFC (pairM x z) hxz)

theorem partial_union (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {P R X Y : M} (hX : ∀ G, memM G X ↔ Partial P R G)
    (hYX : Subset Y X)
    (hchain : ∀ U V, memM U Y → memM V Y → Subset U V ∨ Subset V U) :
    Partial P R (unionM Y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨G, hGY, hzG⟩ := (union_mem hZFC Y z).mp hz
    exact ((hX G).mp (hYX G hGY)).1 z hzG
  · intro z hz
    obtain ⟨G, hGY, hzG⟩ := (union_mem hZFC Y z).mp hz
    exact ((hX G).mp (hYX G hGY)).2.1 z hzG
  · intro x y z hxy hxz
    obtain ⟨G, hGY, hxyG⟩ := (union_mem hZFC Y (pairM x y)).mp hxy
    obtain ⟨H, hHY, hxzH⟩ := (union_mem hZFC Y (pairM x z)).mp hxz
    rcases hchain G H hGY hHY with hGH | hHG
    · exact ((hX H).mp (hYX H hHY)).2.2.1 x y z (hGH _ hxyG) hxzH
    · exact ((hX G).mp (hYX G hGY)).2.2.1 x y z hxyG (hHG _ hxzH)
  · intro x y z hxz hyz
    obtain ⟨G, hGY, hxzG⟩ := (union_mem hZFC Y (pairM x z)).mp hxz
    obtain ⟨H, hHY, hyzH⟩ := (union_mem hZFC Y (pairM y z)).mp hyz
    rcases hchain G H hGY hHY with hGH | hHG
    · exact ((hX H).mp (hYX H hHY)).2.2.2 x y z (hGH _ hxzG) hyzH
    · exact ((hX G).mp (hYX G hGY)).2.2.2 x y z hxzG (hHG _ hyzH)

/-- A maximal partial one-to-one subgraph of any internally coded relation. -/
theorem maximal_partial (hZFC : M ⊨ Erdos501.FOL.ZFC) (P R : M) :
    ∃ G, Partial P R G ∧ ∀ H, Partial P R H → Subset G H → G = H := by
  obtain ⟨X, hX⟩ := partial_family hZFC P R
  have heX : memM emptyM X := (hX emptyM).mpr (partial_empty hZFC P R)
  have hne : X ≠ emptyM := fun heq => empty_mem hZFC emptyM (heq ▸ heX)
  obtain ⟨G, hGX, hmax⟩ := internal_zorn hZFC X hne
    (fun Y hYX hchain => (hX (unionM Y)).mpr (partial_union hZFC hX hYX hchain))
  exact ⟨G, (hX G).mp hGX, fun H hH hGH => hmax H ((hX H).mpr hH) hGH⟩

/-- One-edge extension by a fixed finite formula. Initial levels `G,a,b,z`. -/
def extendFilter : L.BoundedFormula Empty 4 :=
  orF (memF (varT 3) (varT 0))
    (eqF (varT 3) (pairT (varT 1) (varT 2))) 4

theorem realize_extendFilter (G a b z : M) :
    extendFilter.Realize default (Fin.snoc ![G, a, b] z) ↔
      memM z G ∨ z = pairM a b := by
  simp [extendFilter, orF, eqF, memF, varT, memM, Fin.snoc]

theorem extend_set (hZFC : M ⊨ Erdos501.FOL.ZFC) {P G a b : M}
    (hGP : Subset G P) (hab : memM (pairM a b) P) :
    ∃ H, ∀ z, memM z H ↔ memM z G ∨ z = pairM a b := by
  obtain ⟨H, hH⟩ := Separation.separation hZFC 3 extendFilter ![G, a, b] P
  refine ⟨H, ?_⟩
  intro z
  rw [hH z, realize_extendFilter]
  constructor
  · exact And.right
  · intro hz
    exact ⟨hz.elim (hGP z) (fun heq => heq.symm ▸ hab), hz⟩

theorem partial_extend (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {P R G a b : M} (hG : Partial P R G)
    (habP : memM (pairM a b) P) (habR : memM (pairM a b) R)
    (ha : ∀ y, ¬ Edge G a y) (hb : ∀ x, ¬ Edge G x b) :
    ∃ H, Partial P R H ∧ Subset G H ∧ Edge H a b := by
  obtain ⟨H, hH⟩ := extend_set hZFC hG.1 habP
  have hedge : ∀ x y, Edge H x y ↔ Edge G x y ∨ (x = a ∧ y = b) := by
    intro x y
    rw [Edge, hH, pair_eq_iff hZFC]
    rfl
  refine ⟨H, ⟨?_, ?_, ?_, ?_⟩, ?_, (hedge a b).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro z hz
    exact ((hH z).mp hz).elim (hG.1 z) (fun heq => heq.symm ▸ habP)
  · intro z hz
    exact ((hH z).mp hz).elim (hG.2.1 z) (fun heq => heq.symm ▸ habR)
  · intro x y z hxy hxz
    rcases (hedge x y).mp hxy with hxy | hxy <;>
      rcases (hedge x z).mp hxz with hxz | hxz
    · exact hG.2.2.1 x y z hxy hxz
    · exact False.elim (ha y (hxz.1 ▸ hxy))
    · exact False.elim (ha z (hxy.1 ▸ hxz))
    · exact hxy.2.trans hxz.2.symm
  · intro x y z hxz hyz
    rcases (hedge x z).mp hxz with hxz | hxz <;>
      rcases (hedge y z).mp hyz with hyz | hyz
    · exact hG.2.2.2 x y z hxz hyz
    · exact False.elim (hb x (hyz.2 ▸ hxz))
    · exact False.elim (hb y (hxz.2 ▸ hyz))
    · exact hxz.1.trans hyz.1.symm
  · intro z hz
    exact (hH z).mpr (Or.inl hz)

theorem edge_support_of_subset (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B G : M} (hG : Subset G (Product.product hZFC A B)) :
    ∀ x y, Edge G x y → memM x A ∧ memM y B := by
  intro x y hxy
  obtain ⟨a, b, ha, hb, heq⟩ := (Product.product_mem hZFC A B (pairM x y)).mp (hG _ hxy)
  obtain ⟨rfl, rfl⟩ := pair_injective hZFC x y a b heq
  exact ⟨ha, hb⟩

/-- Cardinal comparison with actual internal injection witnesses. -/
theorem injection_comparable (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B : M) :
    Injects A B ∨ Injects B A := by
  classical
  let P := Product.product hZFC A B
  obtain ⟨G, hG, hmax⟩ := maximal_partial hZFC P P
  have hsupp := edge_support_of_subset hZFC hG.1
  by_cases htotal : ∀ x, memM x A → ∃ y, Edge G x y
  · exact Or.inl ⟨G, hsupp, htotal, hG.2.2.1, hG.2.2.2⟩
  · have hsurj : ∀ y, memM y B → ∃ x, Edge G x y := by
      intro b hbB
      by_contra hnone
      obtain ⟨a, ha⟩ := not_forall.mp htotal
      have ha' : memM a A ∧ ¬ ∃ y, Edge G a y := _root_.not_imp.mp ha
      have habP : memM (pairM a b) P :=
        (Product.product_mem hZFC A B (pairM a b)).mpr ⟨a, b, ha'.1, hbB, rfl⟩
      obtain ⟨H, hH, hGH, habH⟩ := partial_extend hZFC hG habP habP
        (fun y hy => ha'.2 ⟨y, hy⟩) (fun x hx => hnone ⟨x, hx⟩)
      have heq : G = H := hmax H hH hGH
      exact ha'.2 ⟨b, heq.symm ▸ habH⟩
    obtain ⟨H, hH⟩ := reverse_graph hZFC A B G
    refine Or.inr ⟨H, ?_, ?_, ?_, ?_⟩
    · intro x y h
      exact ⟨((hH x y).mp h).1, ((hH x y).mp h).2.1⟩
    · intro x hx
      obtain ⟨y, hyx⟩ := hsurj x hx
      exact ⟨y, (hH x y).mpr ⟨hx, (hsupp y x hyx).1, hyx⟩⟩
    · intro x y z hxy hxz
      exact hG.2.2.2 y z x ((hH x y).mp hxy).2.2 ((hH x z).mp hxz).2.2
    · intro x y z hxz hyz
      exact hG.2.2.1 z x y ((hH x z).mp hxz).2.2 ((hH y z).mp hyz).2.2

/-- A coded partial surjection admits an internally coded injective inverse
selection, by the actual Zorn axiom. -/
theorem injects_of_atMost (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B : M} (h : AtMost A B) : Injects A B := by
  classical
  obtain ⟨S, F, hSB, hF, htotal, hsurj⟩ := h
  obtain ⟨R, hR⟩ := reverse_graph hZFC S A F
  let P := Product.product hZFC A B
  obtain ⟨G, hG, hmax⟩ := maximal_partial hZFC P R
  have hsupp := edge_support_of_subset hZFC hG.1
  have hGF : ∀ x y, Edge G x y → Edge F y x :=
    fun x y hxy => ((hR x y).mp (hG.2.1 _ hxy)).2.2
  refine ⟨G, hsupp, ?_, hG.2.2.1, hG.2.2.2⟩
  intro a haA
  by_contra ha
  obtain ⟨b, hbS, hba⟩ := hsurj a haA
  have hbB := hSB b hbS
  have hb : ∀ x, ¬ Edge G x b := by
    intro x hxb
    have hxa : x = a := hF b x a (hGF x b hxb) hba
    subst x
    exact ha ⟨b, hxb⟩
  have habP : memM (pairM a b) P :=
    (Product.product_mem hZFC A B (pairM a b)).mpr ⟨a, b, haA, hbB, rfl⟩
  have habR : Edge R a b := (hR a b).mpr ⟨haA, hbS, hba⟩
  obtain ⟨H, hH, hGH, habH⟩ := partial_extend hZFC hG habP habR
    (fun y hy => ha ⟨y, hy⟩) hb
  have heq : G = H := hmax H hH hGH
  exact ha ⟨b, heq.symm ▸ habH⟩

theorem atMost_iff_injects (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B : M) :
    AtMost A B ↔ Injects A B :=
  ⟨injects_of_atMost hZFC, atMost_of_injects hZFC⟩

#print axioms internal_zorn
#print axioms maximal_partial
#print axioms injection_comparable
#print axioms injects_of_atMost
#print axioms atMost_iff_injects

end ClassicismZFC.CHCardinality
