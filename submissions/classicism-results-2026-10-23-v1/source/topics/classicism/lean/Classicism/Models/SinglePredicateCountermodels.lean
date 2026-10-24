import Classicism.Semantics.FullExtensionalCounting

/-!
# Concrete countermodel certificates for the central negative questions

Every package below uses the actual map schemas, and every nonentailment uses
the existing C derivation soundness theorem with the concrete Bool/Nat `Interp`.
The signature is exactly {c : e→t}; these refute signature-uniform claims, not
claims for every separately prescribed richer signature. All proofs are new
ordinary metatheory and require kernel checking; no shallow C proof is asserted.

Source: research/2026-10-22/central-questions-audit.md, twelve-row table and
signature qualification (original research, unpaginated, direct source misc).
-/

namespace Classicism.Meta.SinglePredicateFull
open FullExtensional

def strongPackage : AxiomSet signature :=
  AxiomSet.independence signature ∪
    (P.Extensionality.schemaIn ∪ (P.NecNecessityOfDistinctness.schemaIn ∪
      (P.Atomicity.schemaIn ∪ (P.FunctionalChoice.schemaIn ∪
        (P.NecFunctionalChoice.schemaIn ∪ (P.IntensionalChoice.schemaIn ∪
          (AxiomSet.noContingency signature ∪ AxiomSet.modalFreedom signature)))))))

theorem strongPackage_holds (I : Interp signature)
    (hInd : (AxiomSet.independence signature).holds I) : strongPackage.holds I := by
  intro a ha
  rcases ha with h | h | h | h | h | h | h | h | h
  · exact hInd a h
  · exact holds_extensionality I a h
  · exact holds_C5 I a h
  · exact holds_atomicity I a h
  · exact holds_functionalChoice I a h
  · exact holds_boxedFunctionalChoice I a h
  · exact holds_intensionalChoice I a h
  · exact holds_noContingency I a h
  · exact holds_modalFreedom I a h

theorem bool_strongPackage : strongPackage.holds boolModel :=
  strongPackage_holds boolModel bool_independence

theorem nat_strongPackage : strongPackage.holds natModel :=
  strongPackage_holds natModel nat_independence

theorem strongPackage_consistent : strongPackage.Consistent :=
  AxiomSet.Consistent.of_interp boolModel bool_strongPackage

theorem quantifiedInfinityE_mem :
    (P.AxiomOfInfinityE.schemaIn : AxiomSet signature) (Term.ofPure P.AxiomOfInfinityE.quoted) :=
  ⟨_, rfl, rfl⟩

theorem quantifiedInfinityT_mem :
    (P.AxiomOfInfinityT.schemaIn : AxiomSet signature) (Term.ofPure P.AxiomOfInfinityT.quoted) :=
  ⟨_, rfl, rfl⟩

theorem bool_not_quantifiedInfinityE_schema : ¬ P.AxiomOfInfinityE.schemaIn.holds boolModel :=
  fun h => bool_not_quantifiedInfinity_e (h _ quantifiedInfinityE_mem)

theorem bool_not_quantifiedInfinityT_schema : ¬ P.AxiomOfInfinityT.schemaIn.holds boolModel :=
  fun h => not_quantifiedInfinity_t boolModel (h _ quantifiedInfinityT_mem)

theorem nat_quantifiedInfinityE_schema : P.AxiomOfInfinityE.schemaIn.holds natModel := by
  rintro _ ⟨_, rfl, rfl⟩
  exact nat_quantifiedInfinity_e

/-- The full positive package and Independence are jointly consistent even with
the actual quantified individual Infinity sentence. -/
theorem strongPackage_with_individualInfinity_consistent :
    (strongPackage ∪ P.AxiomOfInfinityE.schemaIn).Consistent :=
  AxiomSet.Consistent.of_interp natModel
    (fun a ha => ha.elim (nat_strongPackage a) (nat_quantifiedInfinityE_schema a))

theorem not_entails_of_model (I : Interp signature) [Nonempty I.D]
    {Ax Target : AxiomSet signature} (hAx : Ax.holds I) (hTarget : ¬ Target.holds I) :
    ¬ (Ax ⟹ Target) :=
  fun h => hTarget (AxiomSet.Entails.holds I (C.axioms_holds I) h hAx)

theorem strongPackage_not_infinitySchema_e :
    ¬ (strongPackage ⟹ AxiomSet.infinityE signature) :=
  not_entails_of_model boolModel bool_strongPackage bool_not_infinitySchema_e

theorem strongPackage_not_infinitySchema_t :
    ¬ (strongPackage ⟹ AxiomSet.infinityT signature) :=
  not_entails_of_model boolModel bool_strongPackage (not_infinitySchema_t boolModel)

theorem strongPackage_not_quantifiedInfinity_e :
    ¬ (strongPackage ⟹ P.AxiomOfInfinityE.schemaIn) :=
  not_entails_of_model boolModel bool_strongPackage bool_not_quantifiedInfinityE_schema

theorem strongPackage_not_quantifiedInfinity_t :
    ¬ (strongPackage ⟹ P.AxiomOfInfinityT.schemaIn) :=
  not_entails_of_model boolModel bool_strongPackage bool_not_quantifiedInfinityT_schema

/-- C5 background, Independence plus boxed FC: the displayed inconsistency claim fails. -/
theorem c5_independence_boxedChoice_consistent :
    (P.NecNecessityOfDistinctness.schemaIn ∪
      (AxiomSet.independence signature ∪ P.NecFunctionalChoice.schemaIn)).Consistent := by
  apply AxiomSet.Consistent.of_interp boolModel
  intro a ha
  exact ha.elim (holds_C5 boolModel a)
    (fun h => h.elim (bool_independence a) (holds_boxedFunctionalChoice boolModel a))

theorem extensional_independence_choice_consistent :
    (P.Extensionality.schemaIn ∪
      (AxiomSet.independence signature ∪ P.FunctionalChoice.schemaIn)).Consistent := by
  apply AxiomSet.Consistent.of_interp boolModel
  intro a ha
  exact ha.elim (holds_extensionality boolModel a)
    (fun h => h.elim (bool_independence a) (holds_functionalChoice boolModel a))

theorem extensional_independence_choice_not_infinity :
    ¬ ((P.Extensionality.schemaIn ∪
      (AxiomSet.independence signature ∪ P.FunctionalChoice.schemaIn)) ⟹
        P.AxiomOfInfinityE.schemaIn) := by
  apply not_entails_of_model boolModel _ bool_not_quantifiedInfinityE_schema
  intro a ha
  exact ha.elim (holds_extensionality boolModel a)
    (fun h => h.elim (bool_independence a) (holds_functionalChoice boolModel a))

theorem c5_atomic_independence_noContingency_not_schemaInfinity_t :
    ¬ ((P.NecNecessityOfDistinctness.schemaIn ∪ (P.Atomicity.schemaIn ∪
      (AxiomSet.independence signature ∪ AxiomSet.noContingency signature))) ⟹
        AxiomSet.infinityT signature) := by
  apply not_entails_of_model boolModel _ (not_infinitySchema_t boolModel)
  intro a ha
  rcases ha with h | h | h | h
  · exact holds_C5 boolModel a h
  · exact holds_atomicity boolModel a h
  · exact bool_independence a h
  · exact holds_noContingency boolModel a h

theorem c5_atomic_independence_noContingency_not_quantifiedInfinity_t :
    ¬ ((P.NecNecessityOfDistinctness.schemaIn ∪ (P.Atomicity.schemaIn ∪
      (AxiomSet.independence signature ∪ AxiomSet.noContingency signature))) ⟹
        P.AxiomOfInfinityT.schemaIn) := by
  apply not_entails_of_model boolModel _ bool_not_quantifiedInfinityT_schema
  intro a ha
  rcases ha with h | h | h | h
  · exact holds_C5 boolModel a h
  · exact holds_atomicity boolModel a h
  · exact bool_independence a h
  · exact holds_noContingency boolModel a h

theorem c5_atomic_independence_modalFreedom_not_schemaInfinity_t :
    ¬ ((P.NecNecessityOfDistinctness.schemaIn ∪ (P.Atomicity.schemaIn ∪
      (AxiomSet.independence signature ∪ AxiomSet.modalFreedom signature))) ⟹
        AxiomSet.infinityT signature) := by
  apply not_entails_of_model boolModel _ (not_infinitySchema_t boolModel)
  intro a ha
  rcases ha with h | h | h | h
  · exact holds_C5 boolModel a h
  · exact holds_atomicity boolModel a h
  · exact bool_independence a h
  · exact holds_modalFreedom boolModel a h

theorem c5_atomic_independence_intensionalChoice_not_schemaInfinity_t :
    ¬ ((P.NecNecessityOfDistinctness.schemaIn ∪ (P.Atomicity.schemaIn ∪
      (AxiomSet.independence signature ∪ P.IntensionalChoice.schemaIn))) ⟹
        AxiomSet.infinityT signature) := by
  apply not_entails_of_model boolModel _ (not_infinitySchema_t boolModel)
  intro a ha
  rcases ha with h | h | h | h
  · exact holds_C5 boolModel a h
  · exact holds_atomicity boolModel a h
  · exact bool_independence a h
  · exact holds_intensionalChoice boolModel a h

theorem c5_independence_choice_consistent :
    (P.NecNecessityOfDistinctness.schemaIn ∪
      (AxiomSet.independence signature ∪ P.FunctionalChoice.schemaIn)).Consistent := by
  apply AxiomSet.Consistent.of_interp boolModel
  intro a ha
  exact ha.elim (holds_C5 boolModel a)
    (fun h => h.elim (bool_independence a) (holds_functionalChoice boolModel a))

theorem c5_atomic_independence_collapse_consistent :
    (P.NecNecessityOfDistinctness.schemaIn ∪ (P.Atomicity.schemaIn ∪
      (AxiomSet.independence signature ∪ P.DistinctnessPreservingCollapse.schemaIn))).Consistent := by
  apply AxiomSet.Consistent.of_interp boolModel
  intro a ha
  rcases ha with h | h | h | h
  · exact holds_C5 boolModel a h
  · exact holds_atomicity boolModel a h
  · exact bool_independence a h
  · exact holds_distinctnessPreservingCollapse boolModel a h

theorem extensional_independence_infinity_consistent :
    (P.Extensionality.schemaIn ∪
      (AxiomSet.independence signature ∪ P.AxiomOfInfinityE.schemaIn)).Consistent := by
  apply AxiomSet.Consistent.of_interp natModel
  intro a ha
  exact ha.elim (holds_extensionality natModel a)
    (fun h => h.elim (nat_independence a) (nat_quantifiedInfinityE_schema a))

theorem extensional_independence_schemaInfinity_consistent :
    (P.Extensionality.schemaIn ∪
      (AxiomSet.independence signature ∪ AxiomSet.infinityE signature)).Consistent := by
  apply AxiomSet.Consistent.of_interp natModel
  intro a ha
  exact ha.elim (holds_extensionality natModel a)
    (fun h => h.elim (nat_independence a) (nat_infinitySchema_e a))

theorem extensional_independence_not_infinity :
    ¬ ((P.Extensionality.schemaIn ∪ AxiomSet.independence signature) ⟹
      P.AxiomOfInfinityE.schemaIn) := by
  apply not_entails_of_model boolModel _ bool_not_quantifiedInfinityE_schema
  intro a ha
  exact ha.elim (holds_extensionality boolModel a) (bool_independence a)

/-- The complete theory is the set of sentences true in the actual interpretation. -/
def theory (I : Interp signature) : AxiomSet signature := fun p => p.holds I

theorem theory_consistent (I : Interp signature) [Nonempty I.D] : (theory I).Consistent :=
  AxiomSet.Consistent.of_interp I (fun _ h => h)

theorem theory_complete (I : Interp signature) : (theory I).Complete := by
  intro p _
  rcases Classical.em (p.holds I) with hp | hp
  · exact Or.inl (Derivable.axiom (Or.inr hp))
  · exact Or.inr (Derivable.axiom (Or.inr hp))

theorem theory_entails_iff (I : Interp signature) [Nonempty I.D] (Ax : AxiomSet signature) :
    (theory I ⟹ Ax) ↔ Ax.holds I :=
  ⟨fun h => AxiomSet.Entails.holds I (C.axioms_holds I) h (fun _ h => h),
    fun h p hp => Derivable.axiom (Or.inr (h p hp))⟩

/-- One complete consistent theory jointly witnesses all four finite Infinity
failures while satisfying the full positive package and actual Independence. -/
theorem bool_complete_countermodel :
    ∃ Ax : AxiomSet signature, Ax.Consistent ∧ Ax.Complete ∧
      (Ax ⟹ strongPackage) ∧
      ¬ (Ax ⟹ AxiomSet.infinityE signature) ∧
      ¬ (Ax ⟹ AxiomSet.infinityT signature) ∧
      ¬ (Ax ⟹ P.AxiomOfInfinityE.schemaIn) ∧
      ¬ (Ax ⟹ P.AxiomOfInfinityT.schemaIn) := by
  refine ⟨theory boolModel, theory_consistent boolModel, theory_complete boolModel,
    (theory_entails_iff boolModel _).2 bool_strongPackage, ?_, ?_, ?_, ?_⟩
  · exact fun h => bool_not_infinitySchema_e ((theory_entails_iff boolModel _).1 h)
  · exact fun h => not_infinitySchema_t boolModel ((theory_entails_iff boolModel _).1 h)
  · exact fun h => bool_not_quantifiedInfinityE_schema ((theory_entails_iff boolModel _).1 h)
  · exact fun h => bool_not_quantifiedInfinityT_schema ((theory_entails_iff boolModel _).1 h)

theorem nat_complete_countermodel :
    ∃ Ax : AxiomSet signature, Ax.Consistent ∧ Ax.Complete ∧
      (Ax ⟹ strongPackage) ∧ (Ax ⟹ AxiomSet.infinityE signature) ∧
      (Ax ⟹ P.AxiomOfInfinityE.schemaIn) ∧ ¬ (Ax ⟹ AxiomSet.infinityT signature) := by
  refine ⟨theory natModel, theory_consistent natModel, theory_complete natModel,
    (theory_entails_iff natModel _).2 nat_strongPackage,
    (theory_entails_iff natModel _).2 nat_infinitySchema_e,
    (theory_entails_iff natModel _).2 nat_quantifiedInfinityE_schema, ?_⟩
  exact fun h => not_infinitySchema_t natModel ((theory_entails_iff natModel _).1 h)

end Classicism.Meta.SinglePredicateFull
