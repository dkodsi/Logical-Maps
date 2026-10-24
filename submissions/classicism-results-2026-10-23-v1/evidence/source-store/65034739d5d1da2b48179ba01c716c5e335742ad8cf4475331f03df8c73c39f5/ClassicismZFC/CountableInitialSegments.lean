import ClassicismZFC.CHFieldTransport

/-!
# Structural CH from a specific well-order with countable initial segments

Original proof by Codex (OpenAI), prompted by Daniel Kodsi, 23 October 2026.
This is an ordinary-model theorem. All sets and graphs below are internal
codes; the family used in Zorn's lemma is selected by an explicit finite
formula from an internal powerset. No order type is assigned to an arbitrary
set, and no external subset or external choice function is admitted.

The caller must supply an actual well-order witness with internally countable
proper initial segments and an internal injection of the continuum carrier
into that witness. This criterion by itself does not assert that the positive
forcing model has preserved those data. That is a separate forcing theorem.
Source only; no compiler acceptance is asserted.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.CountableInitialSegments

open SetLaws CHCardinality CHFieldTransport

universe u
variable {M : Type u} [L.Structure M]

/-- A strict well-order whose least-element clause quantifies over internal
subsets only. Each displayed clause is a finite first-order formula. -/
def InternalWellOrder (A W : M) : Prop :=
  (∀ x y, Edge W x y → memM x A ∧ memM y A) ∧
  (∀ x, memM x A → ¬ Edge W x x) ∧
  (∀ x y z, Edge W x y → Edge W y z → Edge W x z) ∧
  (∀ x y, memM x A → memM y A → x = y ∨ Edge W x y ∨ Edge W y x) ∧
  (∀ B, Subset B A → B ≠ emptyM →
    ∃ a, memM a B ∧ ∀ b, memM b B → ¬ Edge W b a)

/-- An actual internal code for every proper initial segment and an actual
internal graph injecting that segment into the specified countable carrier. -/
def CountableSegments (A W N : M) : Prop :=
  ∀ a, memM a A → ∃ I,
    (∀ x, memM x I ↔ memM x A ∧ Edge W x a) ∧ Injects I N

/-- The domain of a partial graph is closed downward in the selected order. -/
def InitialDomain (A W G : M) : Prop :=
  ∀ a y b, Edge G a y → memM b A → Edge W b a → ∃ z, Edge G b z

def InitialPartial (P A W G : M) : Prop :=
  Partial P P G ∧ InitialDomain A W G

def edgeF (G x y : Tm) : Fm := memF (pairT x y) G

/-- The finite predicate used to select the Zorn family. -/
def initialDomainF (A W G : Tm) : Fm :=
  allF fun a => allF fun y => allF fun b =>
    impF (edgeF G (varT a) (varT y))
      (impF (memF (varT b) A)
        (impF (edgeF W (varT b) (varT a))
          (exF fun z => edgeF G (varT b) (varT z))))

def initialFilter : L.BoundedFormula Empty 3 :=
  initialDomainF (varT 0) (varT 1) (varT 2) 3

theorem realize_initialFilter (A W G : M) :
    initialFilter.Realize default (Fin.snoc ![A, W] G) ↔ InitialDomain A W G := by
  simp [initialFilter, initialDomainF, edgeF, InitialDomain, Edge,
    allF, exF, impF, memF, varT, memM, Fin.snoc]

theorem initial_family (hZFC : M ⊨ Erdos501.FOL.ZFC) (P A W : M) :
    ∃ X, ∀ G, memM G X ↔ InitialPartial P A W G := by
  obtain ⟨Y, hY⟩ := partial_family hZFC P P
  obtain ⟨X, hX⟩ := Separation.separation hZFC 2 initialFilter ![A, W] Y
  refine ⟨X, fun G => ?_⟩
  exact (hX G).trans (and_congr (hY G) (realize_initialFilter A W G))

theorem initial_empty (hZFC : M ⊨ Erdos501.FOL.ZFC) (P A W : M) :
    InitialPartial P A W emptyM := by
  refine ⟨partial_empty hZFC P P, ?_⟩
  intro a y b hay _ _
  exact False.elim (empty_mem hZFC (pairM a y) hay)

theorem initial_union (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {P A W X Y : M} (hX : ∀ G, memM G X ↔ InitialPartial P A W G)
    (hYX : Subset Y X)
    (hchain : ∀ U V, memM U Y → memM V Y → Subset U V ∨ Subset V U) :
    InitialPartial P A W (unionM Y) := by
  constructor
  · obtain ⟨F, hF⟩ := partial_family hZFC P P
    exact partial_union hZFC hF
      (fun G hGY => (hF G).mpr (((hX G).mp (hYX G hGY)).1)) hchain
  · intro a y b hay hb hba
    obtain ⟨G, hGY, hayG⟩ := (union_mem hZFC Y (pairM a y)).mp hay
    obtain ⟨z, hbz⟩ := ((hX G).mp (hYX G hGY)).2 a y b hayG hb hba
    exact ⟨z, (union_mem hZFC Y (pairM b z)).mpr ⟨G, hGY, hbz⟩⟩

theorem maximal_initial (hZFC : M ⊨ Erdos501.FOL.ZFC) (P A W : M) :
    ∃ G, InitialPartial P A W G ∧
      ∀ H, InitialPartial P A W H → Subset G H → G = H := by
  obtain ⟨X, hX⟩ := initial_family hZFC P A W
  have heX : memM emptyM X := (hX emptyM).mpr (initial_empty hZFC P A W)
  have hne : X ≠ emptyM := fun heq => empty_mem hZFC emptyM (heq ▸ heX)
  obtain ⟨G, hGX, hmax⟩ := internal_zorn hZFC X hne
    (fun Y hYX hc => (hX (unionM Y)).mpr (initial_union hZFC hX hYX hc))
  exact ⟨G, (hX G).mp hGX, fun H hH hGH => hmax H ((hX H).mpr hH) hGH⟩

/-- Missing domain points are selected by one finite Separation instance. -/
def missingFilter : L.BoundedFormula Empty 2 :=
  notF (exF fun y => edgeF (varT 0) (varT 1) (varT y)) 2

theorem realize_missingFilter (G x : M) :
    missingFilter.Realize default (Fin.snoc ![G] x) ↔ ¬ ∃ y, Edge G x y := by
  simp [missingFilter, edgeF, Edge, notF, exF, memF, varT, memM, Fin.snoc]

/-- A least missing point has every strict predecessor in the domain. -/
theorem least_missing (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A W G : M} (hW : InternalWellOrder A W)
    (hmissing : ∃ a, memM a A ∧ ¬ ∃ y, Edge G a y) :
    ∃ a, memM a A ∧ (¬ ∃ y, Edge G a y) ∧
      ∀ b, memM b A → Edge W b a → ∃ z, Edge G b z := by
  classical
  obtain ⟨B, hB⟩ := Separation.separation hZFC 1 missingFilter ![G] A
  have hmem : ∀ x, memM x B ↔ memM x A ∧ ¬ ∃ y, Edge G x y :=
    fun x => by rw [hB x, realize_missingFilter]
  obtain ⟨c, hcA, hc⟩ := hmissing
  have hcB : memM c B := (hmem c).mpr ⟨hcA, hc⟩
  have hne : B ≠ emptyM := fun heq => empty_mem hZFC c (heq ▸ hcB)
  obtain ⟨a, haB, hmin⟩ := hW.2.2.2.2 B
    (fun x hx => ((hmem x).mp hx).1) hne
  refine ⟨a, ((hmem a).mp haB).1, ((hmem a).mp haB).2, ?_⟩
  intro b hb hba
  by_contra hbmiss
  exact hmin b ((hmem b).mpr ⟨hb, hbmiss⟩) hba

/-- Add the first missing argument and a fresh value. The extension is the
actual internally coded union with one pair, with its exact edge description. -/
theorem extend_initial (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {P A W G a b : M} (hG : InitialPartial P A W G)
    (habP : memM (pairM a b) P)
    (ha : ∀ y, ¬ Edge G a y) (hb : ∀ x, ¬ Edge G x b)
    (hbefore : ∀ x, memM x A → Edge W x a → ∃ y, Edge G x y) :
    ∃ H, InitialPartial P A W H ∧ Subset G H ∧ Edge H a b := by
  obtain ⟨H, hH⟩ := extend_set hZFC hG.1.1 habP
  have hedge : ∀ x y, Edge H x y ↔ Edge G x y ∨ (x = a ∧ y = b) := by
    intro x y
    rw [Edge, hH, pair_eq_iff hZFC] <;> rfl
  have hGH : Subset G H := fun z hz => (hH z).mpr (Or.inl hz)
  have hpart : Partial P P H := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      exact ((hH z).mp hz).elim (hG.1.1 z) (fun heq => heq.symm ▸ habP)
    · intro z hz
      exact ((hH z).mp hz).elim (hG.1.2.1 z) (fun heq => heq.symm ▸ habP)
    · intro x y z hxy hxz
      rcases (hedge x y).mp hxy with hxy | hxy <;>
        rcases (hedge x z).mp hxz with hxz | hxz
      · exact hG.1.2.2.1 x y z hxy hxz
      · exact False.elim (ha y (hxz.1 ▸ hxy))
      · exact False.elim (ha z (hxy.1 ▸ hxz))
      · exact hxy.2.trans hxz.2.symm
    · intro x y z hxz hyz
      rcases (hedge x z).mp hxz with hxz | hxz <;>
        rcases (hedge y z).mp hyz with hyz | hyz
      · exact hG.1.2.2.2 x y z hxz hyz
      · exact False.elim (hb x (hyz.2 ▸ hxz))
      · exact False.elim (hb y (hxz.2 ▸ hyz))
      · exact hxz.1.trans hyz.1.symm
  refine ⟨H, ⟨hpart, ?_⟩, hGH, (hedge a b).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  intro x y z hxy hz hzx
  rcases (hedge x y).mp hxy with hold | ⟨rfl, rfl⟩
  · obtain ⟨v, hzv⟩ := hG.2 x y z hold hz hzx
    exact ⟨v, hGH _ hzv⟩
  · obtain ⟨v, hzv⟩ := hbefore z hz hzx
    exact ⟨v, hGH _ hzv⟩

/-- The specialized cardinal dichotomy. Only initial domains in this one
specified well-order are used; no order type for the arbitrary target Y. -/
theorem injection_gap (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A W N : M} (hW : InternalWellOrder A W) (hseg : CountableSegments A W N)
    (Y : M) : Injects Y N ∨ Injects A Y := by
  classical
  let P := Product.product hZFC A Y
  obtain ⟨G, hG, hmax⟩ := maximal_initial hZFC P A W
  have hsupp : ∀ x y, Edge G x y → memM x A ∧ memM y Y :=
    edge_support_of_subset hZFC hG.1.1
  by_cases htotal : ∀ x, memM x A → ∃ y, Edge G x y
  · exact Or.inr ⟨G, hsupp, htotal, hG.1.2.2.1, hG.1.2.2.2⟩
  · have hmissing : ∃ a, memM a A ∧ ¬ ∃ y, Edge G a y := by
      obtain ⟨a, ha⟩ := not_forall.mp htotal
      exact ⟨a, (_root_.not_imp.mp ha).1, (_root_.not_imp.mp ha).2⟩
    obtain ⟨a, haA, ha, hbefore⟩ := least_missing hZFC hW hmissing
    have hsurj : ∀ y, memM y Y → ∃ x, Edge G x y := by
      intro b hbY
      by_contra hb
      have habP : memM (pairM a b) P :=
        (Product.product_mem hZFC A Y (pairM a b)).mpr ⟨a, b, haA, hbY, rfl⟩
      obtain ⟨H, hH, hGH, habH⟩ := extend_initial hZFC hG habP
        (fun y hy => ha ⟨y, hy⟩) (fun x hx => hb ⟨x, hx⟩) hbefore
      have heq : G = H := hmax H hH hGH
      exact ha ⟨b, heq.symm ▸ habH⟩
    obtain ⟨I, hI, hIN⟩ := hseg a haA
    have htoI : ∀ x y, Edge G x y → memM x I := by
      intro x y hxy
      have hxA := (hsupp x y hxy).1
      apply (hI x).mpr
      refine ⟨hxA, ?_⟩
      rcases hW.2.2.2.1 x a hxA haA with hxa | hxa | hax
      · subst x
        exact False.elim (ha ⟨y, hxy⟩)
      · exact hxa
      · obtain ⟨z, haz⟩ := hG.2 x y a hxy haA hax
        exact False.elim (ha ⟨z, haz⟩)
    have hbij : Bijection I Y G := by
      refine ⟨⟨?_, ?_, hG.1.2.2.1, hG.1.2.2.2⟩, hsurj⟩
      · intro x y hxy
        exact ⟨htoI x y hxy, (hsupp x y hxy).2⟩
      · intro x hxI
        exact hbefore x ((hI x).mp hxI).1 ((hI x).mp hxI).2
    have hYI : Injects Y I :=
      equinumerous_injects (equinumerous_symm hZFC ⟨G, hbij⟩)
    exact Or.inl (injects_trans hZFC hYI hIN)

/-- The positive structural-CH criterion, proved from actual internal Zorn,
finite Separation, and internal graph composition/Schroeder--Bernstein. -/
theorem structuralCH_of_countable_segments (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {R N A W : M} (hW : InternalWellOrder A W) (hseg : CountableSegments A W N)
    (hRA : Injects R A) : StructuralCH R N := by
  apply (structural_iff_injection_gap hZFC R N).mpr
  intro Y _
  exact (injection_gap hZFC hW hseg Y).elim Or.inl
    (fun hAY => Or.inr (injects_trans hZFC hRA hAY))

#print axioms maximal_initial
#print axioms injection_gap
#print axioms structuralCH_of_countable_segments

end ClassicismZFC.CountableInitialSegments
