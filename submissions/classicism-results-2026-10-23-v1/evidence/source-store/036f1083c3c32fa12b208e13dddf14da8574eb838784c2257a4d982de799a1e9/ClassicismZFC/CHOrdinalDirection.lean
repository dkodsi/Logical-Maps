import ClassicismZFC.CHFieldTransport

/-!
# The unconditional direction needed by the negative-CH component

Structural CH on P(omega), with omega as the countable carrier, implies the
pinned ordinal CH sentence. Consequently failure of the pinned sentence
already refutes structural CH, once the distinguished real/natural carriers
have actual internally coded cardinal identifications. This direction does
not require a theorem assigning an ordinal order type to every internal set.

Original source, misc, 23 October 2026. Source only, uncompiled.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.CHOrdinalDirection

open SetLaws CHCardinality CHFieldTransport
universe u
variable {M : Type u} [L.Structure M]

/-- The exact three semantic clauses of the source `ordF`. -/
def IsOrdinal (A : M) : Prop :=
  ((∀ y, memM y A → ∀ z, memM z A → (y = z ∨ memM y z) ∨ memM z y) ∧
    (∀ Y, Subset Y A → Y ≠ emptyM →
      ∃ z, memM z Y ∧ ∀ w, memM w Y → ¬ memM w z)) ∧
  (∀ y, memM y A → Subset y A)

theorem realize_ordF (A : M) :
    (ordF 0 1).Realize default ![A] ↔ IsOrdinal A := by
  simp [ordF, IsOrdinal, CHCardinality.Subset, subsetF, allF, exF, andF, orF, impF,
    notF, eqF, memF, varT, memM, Fin.snoc]

/-- Full semantic reading of the exact pinned ordinal CH sentence. -/
theorem realize_CH : (M ⊨ CHTranslation.CH) ↔
    ∀ A : M, IsOrdinal A → AtMost A omegaM ∨ AtMost (powerM omegaM) A := by
  have hraw : (M ⊨ CHTranslation.CH) ↔
      ∀ A : M, IsOrdinal A →
        RawAtMost A omegaM ∨ RawAtMost (powerM omegaM) A := by
    simp [CHTranslation.CH, CHTranslation.atMostF,
      CHTranslation.functionalGraphF, CHTranslation.totalGraphF,
      IsOrdinal, RawAtMost, CHCardinality.Subset, Edge, ordF, subsetF,
      toSentence, allF, exF, andF, orF, impF, notF, eqF, memF, varT,
      Sentence.Realize, Formula.Realize, memM, Fin.snoc]
  rw [hraw]
  constructor
  · intro h A hA
    exact (h A hA).elim
      (fun ha => Or.inl ((rawAtMost_iff A omegaM).mp ha))
      (fun ha => Or.inr ((rawAtMost_iff (powerM omegaM) A).mp ha))
  · intro h A hA
    exact (h A hA).elim
      (fun ha => Or.inl ((rawAtMost_iff A omegaM).mpr ha))
      (fun ha => Or.inr ((rawAtMost_iff (powerM omegaM) A).mpr ha))

/-- Same CH sentence expressed by genuinely internal injection graphs. -/
theorem realize_CH_injections (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    (M ⊨ CHTranslation.CH) ↔ ∀ A : M, IsOrdinal A →
      Injects A omegaM ∨ Injects (powerM omegaM) A := by
  rw [realize_CH]
  constructor
  · intro h A hA
    exact (h A hA).elim
      (fun ha => Or.inl (injects_of_atMost hZFC ha))
      (fun ha => Or.inr (injects_of_atMost hZFC ha))
  · intro h A hA
    exact (h A hA).elim
      (fun ha => Or.inl (atMost_of_injects hZFC ha))
      (fun ha => Or.inr (atMost_of_injects hZFC ha))

/-- The all-set gap gives the ordinal instance, without any order-type theorem. -/
theorem structural_implies_CH (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (h : StructuralCH (powerM (omegaM : M)) omegaM) : M ⊨ CHTranslation.CH := by
  apply (realize_CH_injections hZFC).mpr
  have hall := (structural_iff_allSetGap hZFC (powerM (omegaM : M)) omegaM).mp h
  intro A _
  exact hall A

/-- A genuine negative structural-CH result, conditional only on actual
internal equinumerosities of the selected carriers. No CH-equivalence
premise, no external functions, and no countability-of-the-model argument. -/
theorem not_structural_of_not_CH (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {R N : M} (hR : Equinumerous R (powerM (omegaM : M)))
    (hN : Equinumerous N (omegaM : M)) (hn : ¬ M ⊨ CHTranslation.CH) :
    ¬ StructuralCH R N := by
  intro hs
  exact hn (structural_implies_CH hZFC ((structural_transport hZFC hR hN).mp hs))

/-- Mutual internal injections suffice, because internal CSB is proved. -/
theorem not_structural_of_not_CH_injections (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {R N : M} (hRP : Injects R (powerM (omegaM : M)))
    (hPR : Injects (powerM (omegaM : M)) R)
    (hNω : Injects N (omegaM : M)) (hωN : Injects (omegaM : M) N)
    (hn : ¬ M ⊨ CHTranslation.CH) : ¬ StructuralCH R N :=
  not_structural_of_not_CH hZFC
    (schroeder_bernstein hZFC hRP hPR)
    (schroeder_bernstein hZFC hNω hωN) hn

#print axioms realize_CH
#print axioms realize_CH_injections
#print axioms structural_implies_CH
#print axioms not_structural_of_not_CH
#print axioms not_structural_of_not_CH_injections

end ClassicismZFC.CHOrdinalDirection
