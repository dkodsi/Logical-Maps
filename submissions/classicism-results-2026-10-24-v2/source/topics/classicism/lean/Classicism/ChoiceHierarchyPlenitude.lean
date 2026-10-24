import Classicism.Results.ChoiceHierarchySchemas
import Classicism.Results.Records.C5
import Classicism.Results.Records.Extensionality
import Classicism.Results.Records.Comprehension

/-!
# The exact boxed Plenitude base for the hierarchy

The single instance `□Plenitude_(t,t)` supplies all boxed Plenitude instances.
The output-arity step uses the library's vectorization theorem, including the
empty argument list; it is not a quantifier over types in the object language.
All boxed implications below necessitate discharged C theorems, using S4 for
the already boxed ND premise where a second box is needed.
-/

namespace Classicism.ChoiceHierarchyPlenitude

theorem necFunctionality_of_tt {σ τ : Type} [Ty σ] [Rel τ] :
    P.NecPlenitude Prop Prop → P.NecFunctionality σ τ := fun hp =>
  Proofs.necessary_barcan_r_implies_necessary_functionality_r
    (Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r
      (Proofs.necessary_plenitude_r_implies_necessary_distinctness_necessary_r hp))

theorem necND_of_tt {σ : Type} [Ty σ] :
    P.NecPlenitude Prop Prop → P.NecNecessityOfDistinctness σ := fun hp =>
  modal_K _ _ (nec% (Proofs.nd_of_nd_t (σ := σ)))
    (Proofs.necessary_plenitude_r_implies_necessary_distinctness_necessary_r hp)

theorem necRigid_predicate_of_tt {σ : Type} [Ty σ] :
    P.NecPlenitude Prop Prop → P.NecRigidComprehension (σ → Prop) := fun hp =>
  modal_K _ _
    (modal_K _ _ (nec% (Proofs.c5_and_actuality_imply_rigid_comprehension (σ := σ)))
      (Proofs.necessary_plenitude_r_implies_necessary_actuality hp))
    (modal_four _ (Proofs.necessary_plenitude_r_implies_necessary_distinctness_necessary_r hp))

theorem necWeak_of_necRigid {τ : Type} [Rel τ] :
    P.NecRigidComprehension τ → P.NecWeakRigidComprehension τ :=
  Proofs.necessary_rigid_comprehension_implies_necessary_weak_rigid_comprehension

/-- Output argument type first: the generated list rule vectorizes this one. -/
theorem necPlen_predicate_of_necWeak_ND {υ σ : Type} [Ty υ] [Ty σ] :
    P.NecWeakRigidComprehension (σ → (υ → Prop) → Prop) →
    P.NecNecessityOfDistinctness σ → P.NecPlenitude σ (υ → Prop) := fun hr hn =>
  modal_K _ _
    (modal_K _ _
      (nec% (Proofs.weak_rigid_comprehension_and_nd_imply_plenitude (σ' := υ) (σ := σ))) hr) hn

theorem tt_of_necSelector :
    ChoiceHierarchy.NecSelector Prop → P.NecPlenitude Prop Prop := fun hs =>
  Proofs.necessary_functional_choice_r_implies_necessary_plenitude_r
    (ChoiceHierarchy.boxed_functionalChoice_of_boxed_selector hs)

end Classicism.ChoiceHierarchyPlenitude

#classicism_check
  Classicism.ChoiceHierarchyPlenitude.necFunctionality_of_tt
  Classicism.ChoiceHierarchyPlenitude.necND_of_tt
  Classicism.ChoiceHierarchyPlenitude.necRigid_predicate_of_tt
  Classicism.ChoiceHierarchyPlenitude.necWeak_of_necRigid
  Classicism.ChoiceHierarchyPlenitude.necPlen_predicate_of_necWeak_ND
  Classicism.ChoiceHierarchyPlenitude.tt_of_necSelector

#classicism_types
  Classicism.ChoiceHierarchyPlenitude.necFunctionality_of_tt
  Classicism.ChoiceHierarchyPlenitude.necND_of_tt
  Classicism.ChoiceHierarchyPlenitude.necRigid_predicate_of_tt
  Classicism.ChoiceHierarchyPlenitude.necWeak_of_necRigid
  Classicism.ChoiceHierarchyPlenitude.necPlen_predicate_of_necWeak_ND
  Classicism.ChoiceHierarchyPlenitude.tt_of_necSelector

#classicism_certify
  Classicism.ChoiceHierarchyPlenitude.necFunctionality_of_tt
  Classicism.ChoiceHierarchyPlenitude.necND_of_tt
  Classicism.ChoiceHierarchyPlenitude.necRigid_predicate_of_tt
  Classicism.ChoiceHierarchyPlenitude.necWeak_of_necRigid
  Classicism.ChoiceHierarchyPlenitude.necPlen_predicate_of_necWeak_ND
  Classicism.ChoiceHierarchyPlenitude.tt_of_necSelector

namespace Classicism.Meta.ChoiceHierarchy

open AxiomSet Classicism.ChoiceHierarchyPlenitude

def plenitudeBase : AxiomSet Signature.pure :=
  single (P.NecPlenitude.quoted Ty.t .t)

theorem plenitudeBase_axiom :
    Theorem (C.axioms ∪ plenitudeBase) (P.NecPlenitude.quoted Ty.t .t) :=
  Theorem.ax rfl

theorem plenitudeBase_functionality (σ : Ty) (ρ : RTy) :
    Theorem (C.axioms ∪ plenitudeBase) (P.NecFunctionality.quoted σ ρ) :=
  (Theorem.ofC (necFunctionality_of_tt.rule σ ρ)).mp plenitudeBase_axiom

/-- The output may have arbitrary finite arity, including arity zero. -/
theorem plenitudeBase_plenitude (σ : Ty) (ρ : RTy) (hσ : σ.Closed) (_hρ : ρ.Closed) :
    Theorem (C.axioms ∪ plenitudeBase) (P.NecPlenitude.quoted σ ρ) := by
  let q := RTy.ofArgs ρ.args
  have hr : Theorem (C.axioms ∪ plenitudeBase)
      (P.NecRigidComprehension.quoted (.arr σ (.arr (.rel q) .t))) :=
    (Theorem.ofC (necRigid_predicate_of_tt.listRule [σ, .rel q])).mp plenitudeBase_axiom
  have hw : Theorem (C.axioms ∪ plenitudeBase)
      (P.NecWeakRigidComprehension.quoted (.arr σ (.arr (.rel q) .t))) :=
    (Theorem.ofC (necWeak_of_necRigid.rule (.arr σ (.arr (.rel q) .t)))).mp hr
  have hn : Theorem (C.axioms ∪ plenitudeBase) (P.NecNecessityOfDistinctness.quoted σ) :=
    (Theorem.ofC (necND_of_tt.rule σ)).mp plenitudeBase_axiom
  have hp : Theorem (C.axioms ∪ plenitudeBase) (P.NecPlenitude.quoted σ q) :=
    (Theorem.ofC (necPlen_predicate_of_necWeak_ND.listRule ρ.args σ hσ)).mp₂ hw hn
  exact hp.cast (by
    change P.NecPlenitude.quoted σ (RTy.ofArgs ρ.args) = _
    rw [RTy.ofArgs_args])

theorem plenitudeBase_entails_schema : plenitudeBase ⟹ P.NecPlenitude.schema := by
  rintro a ⟨σ, ρ, hσ, hρ, rfl⟩
  exact plenitudeBase_plenitude σ ρ hσ hρ

theorem plenitudeSchema_entails_base : P.NecPlenitude.schema ⟹ plenitudeBase := by
  intro a ha
  change a = P.NecPlenitude.quoted Ty.t .t at ha
  subst a
  exact Theorem.ax ⟨Ty.t, .t, trivial, trivial, rfl⟩

/-- Every selector stage supplies the exact base used by the recursive proof. -/
theorem selectorStage_entails_plenitudeBase (n : Nat) : selectorStage n ⟹ plenitudeBase := by
  intro a ha
  change a = P.NecPlenitude.quoted Ty.t .t at ha
  subst a
  have hs0 : Theorem (C.axioms ∪ selectorStage n)
      (Classicism.ChoiceHierarchy.NecSelector.quoted (tower 0)) :=
    stage_entails_of_le (Nat.zero_le n) _ rfl
  have hst : Theorem (C.axioms ∪ selectorStage n)
      (Classicism.ChoiceHierarchy.NecSelector.quoted .t) :=
    (Theorem.ofC Classicism.ChoiceHierarchy.necSelector_prop_of_et.rule).mp hs0
  exact (Theorem.ofC tt_of_necSelector.rule).mp hst

end Classicism.Meta.ChoiceHierarchy
