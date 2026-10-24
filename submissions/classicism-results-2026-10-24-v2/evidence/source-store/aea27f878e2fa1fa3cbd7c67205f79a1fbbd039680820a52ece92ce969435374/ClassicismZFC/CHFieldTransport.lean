import ClassicismZFC.CHCardinalityChoice

/-!
# Structural CH and transport by internally coded bijections

The structural statement quantifies only over internal set codes and graph
codes. This file supplies the exact Flypitch injection syntax, graph
normalization, structural CH invariance, and its equivalence to a gap
statement about all internal sets. It does not replace the remaining
ordinal-representation theorem by an assumption named 'CH equivalence'.

Original source, misc, 23 October 2026. Source only, uncompiled.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder Fol

namespace ClassicismZFC.CHFieldTransport

open SetLaws CHCardinality
universe u
variable {M : Type u} [L.Structure M]

/-- This has exactly the four-quantifier form of Flypitch's `is_inj_f`. -/
def injectiveGraphF (G : Tm) : Fm :=
  allF fun a => allF fun b => allF fun c => allF fun d =>
    impF (andF
      (andF (memF (pairT (varT a) (varT c)) G)
        (memF (pairT (varT b) (varT d)) G))
      (eqF (varT c) (varT d))) (eqF (varT a) (varT b))

/-- Exact unnormalized injection syntax used by the Boolean-valued library. -/
def injectsF (A B : Tm) : Fm := exF fun G =>
  andF (andF (CHTranslation.functionalGraphF (varT G))
    (CHTranslation.totalGraphF A B (varT G)))
    (injectiveGraphF (varT G))

theorem tr_injectiveGraphF : tr (injectiveGraphF (varT 0) 1) = is_inj_f := rfl

theorem tr_injectsF : tr (injectsF (varT 0) (varT 1) 2) = injects_into_f := rfl

def RawInjection (A B G : M) : Prop :=
  ((∀ a b c d, Edge G a c ∧ Edge G b d → a = b → c = d) ∧
    (∀ a, memM a A → ∃ b, memM b B ∧ Edge G a b)) ∧
  (∀ a b c d, (Edge G a c ∧ Edge G b d) ∧ c = d → a = b)

theorem realize_injectsF_raw (A B : M) :
    (injectsF (varT 0) (varT 1) 2).Realize default ![A, B] ↔
      ∃ G, RawInjection A B G := by
  simp [injectsF, injectiveGraphF, CHTranslation.functionalGraphF,
    CHTranslation.totalGraphF, RawInjection, Edge,
    allF, exF, andF, impF, eqF, memF, varT, memM, Fin.snoc]

/-- Restriction to the internal product removes off-domain edges. -/
theorem normalize_raw (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B G : M} (h : RawInjection A B G) : Injects A B := by
  obtain ⟨H, hH⟩ := restrict_graph hZFC A B G
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact ⟨((hH x y).mp hxy).1, ((hH x y).mp hxy).2.1⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := h.1.2 x hx
    exact ⟨y, (hH x y).mpr ⟨hx, hy, hxy⟩⟩
  · intro x y z hxy hxz
    exact h.1.1 x x y z ⟨((hH x y).mp hxy).2.2, ((hH x z).mp hxz).2.2⟩ rfl
  · intro x y z hxz hyz
    exact h.2 x y z z ⟨⟨((hH x z).mp hxz).2.2, ((hH y z).mp hyz).2.2⟩, rfl⟩

theorem raw_of_injection {A B G : M} (h : Injection A B G) : RawInjection A B G := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b c d he hab
    subst b
    exact h.2.2.1 a c d he.1 he.2
  · intro a ha
    obtain ⟨b, hab⟩ := h.2.1 a ha
    exact ⟨b, (h.1 a b hab).2, hab⟩
  · intro a b c d he
    obtain ⟨⟨hac, hbd⟩, hcd⟩ := he
    subst d
    exact h.2.2.2 a b c hac hbd

/-- An actual syntax-to-internal-graph theorem, with no external function witness. -/
theorem realize_injectsF (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B : M) :
    (injectsF (varT 0) (varT 1) 2).Realize default ![A, B] ↔ Injects A B := by
  rw [realize_injectsF_raw]
  exact ⟨fun ⟨G, hG⟩ => normalize_raw hZFC hG,
    fun ⟨G, hG⟩ => ⟨G, raw_of_injection hG⟩⟩

/-- The structural CH statement with all its quantifiers internal. -/
def StructuralCH (R N : M) : Prop :=
  ∀ Y, Subset Y R → Injects Y N ∨ Equinumerous Y R

/-- Identity graph on an internal subset, obtained by finite Separation. -/
def diagonalFilter : L.BoundedFormula Empty 1 :=
  (exF fun x => eqF (varT 0) (pairT (varT x) (varT x))) 1

theorem realize_diagonalFilter (z : M) :
    diagonalFilter.Realize default (Fin.snoc ![] z) ↔ ∃ x, z = pairM x x := by
  simp [diagonalFilter, exF, eqF, varT, Fin.snoc]

theorem injects_of_subset (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B : M} (hAB : Subset A B) : Injects A B := by
  obtain ⟨G, hG⟩ := graph_separation hZFC 0 diagonalFilter ![] A B
  have hedge : ∀ x y, Edge G x y ↔ memM x A ∧ memM y B ∧ x = y := by
    intro x y
    rw [hG, realize_diagonalFilter]
    constructor
    · rintro ⟨hx, hy, z, heq⟩
      obtain ⟨hxz, hyz⟩ := pair_injective hZFC x y z z heq
      exact ⟨hx, hy, hxz.trans hyz.symm⟩
    · rintro ⟨hx, hy, rfl⟩
      exact ⟨hx, hy, x, rfl⟩
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro x y h
    exact ⟨((hedge x y).mp h).1, ((hedge x y).mp h).2.1⟩
  · intro x hx
    exact ⟨x, (hedge x x).mpr ⟨hx, hAB x hx, rfl⟩⟩
  · intro x y z hxy hxz
    exact ((hedge x y).mp hxy).2.2.symm.trans ((hedge x z).mp hxz).2.2
  · intro x y z hxz hyz
    exact ((hedge x z).mp hxz).2.2.trans ((hedge y z).mp hyz).2.2.symm

theorem injects_trans (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B C : M} (hAB : Injects A B) (hBC : Injects B C) : Injects A C := by
  obtain ⟨G, hG⟩ := hAB
  obtain ⟨H, hH⟩ := hBC
  exact compose_injection hZFC hG hH

theorem equinumerous_symm (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B : M} (h : Equinumerous A B) : Equinumerous B A := by
  obtain ⟨G, hG⟩ := h
  exact inverse_bijection hZFC hG

theorem equinumerous_trans (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B C : M} (hAB : Equinumerous A B) (hBC : Equinumerous B C) :
    Equinumerous A C := by
  obtain ⟨G, hG⟩ := hAB
  obtain ⟨H, hH⟩ := hBC
  exact compose_bijection hZFC hG hH

theorem equinumerous_injects {A B : M} (h : Equinumerous A B) : Injects A B := by
  obtain ⟨G, hG⟩ := h
  exact ⟨G, hG.1⟩

/-- A reverse injection is enough for the large alternative, because the
small subset already injects into its containing real carrier. -/
theorem structural_iff_injection_gap (hZFC : M ⊨ Erdos501.FOL.ZFC) (R N : M) :
    StructuralCH R N ↔
      ∀ Y, Subset Y R → Injects Y N ∨ Injects R Y := by
  constructor
  · intro h Y hYR
    rcases h Y hYR with hsmall | hlarge
    · exact Or.inl hsmall
    · exact Or.inr (equinumerous_injects (equinumerous_symm hZFC hlarge))
  · intro h Y hYR
    rcases h Y hYR with hsmall | hlarge
    · exact Or.inl hsmall
    · exact Or.inr (schroeder_bernstein hZFC (injects_of_subset hZFC hYR) hlarge)

/-- Invariance under ACTUAL internal cardinal maps of both distinguished
carriers. The maps themselves are not supplied by this transport theorem. -/
theorem structural_transport (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {R N R' N' : M} (hR : Equinumerous R R') (hN : Equinumerous N N') :
    StructuralCH R N ↔ StructuralCH R' N' := by
  have forward : ∀ {A B A' B' : M}, Equinumerous A A' → Equinumerous B B' →
      StructuralCH A B → StructuralCH A' B' := by
    intro A B A' B' hA hB h Y hYA'
    obtain ⟨F, hF⟩ := equinumerous_symm hZFC hA
    obtain ⟨I, G, hIA, hG⟩ := restrict_to_image hZFC hF.1 hYA'
    rcases h I hIA with hsmall | hlarge
    · exact Or.inl (injects_trans hZFC
        (injects_trans hZFC ⟨G, hG.1⟩ hsmall) (equinumerous_injects hB))
    · exact Or.inr (equinumerous_trans hZFC
        (equinumerous_trans hZFC ⟨G, hG⟩ hlarge) hA)
  exact ⟨forward hR hN,
    forward (equinumerous_symm hZFC hR) (equinumerous_symm hZFC hN)⟩

/-- The all-set gap statement uses only internally coded maps. -/
def AllSetGap (R N : M) : Prop := ∀ A, Injects A N ∨ Injects R A

/-- Internal Zorn comparison and internal CSB reduce structural CH to a
cardinal gap over all internal sets. Passing from ordinals to all sets is
still the separate internal ordinal-representation obligation. -/
theorem structural_iff_allSetGap (hZFC : M ⊨ Erdos501.FOL.ZFC) (R N : M) :
    StructuralCH R N ↔ AllSetGap R N := by
  constructor
  · intro h A
    rcases injection_comparable hZFC A R with hAR | hRA
    · obtain ⟨F, hF⟩ := hAR
      obtain ⟨I, G, hIR, hG⟩ := restrict_to_image hZFC hF (fun _ hx => hx)
      rcases h I hIR with hsmall | hlarge
      · exact Or.inl (injects_trans hZFC ⟨G, hG.1⟩ hsmall)
      · have hRI : Equinumerous R I := equinumerous_symm hZFC hlarge
        have hIA : Equinumerous I A := equinumerous_symm hZFC ⟨G, hG⟩
        exact Or.inr (equinumerous_injects (equinumerous_trans hZFC hRI hIA))
    · exact Or.inr hRA
  · intro h
    apply (structural_iff_injection_gap hZFC R N).mpr
    intro Y _
    exact h Y

#print axioms tr_injectsF
#print axioms realize_injectsF
#print axioms injects_of_subset
#print axioms structural_iff_injection_gap
#print axioms structural_transport
#print axioms structural_iff_allSetGap

end ClassicismZFC.CHFieldTransport
