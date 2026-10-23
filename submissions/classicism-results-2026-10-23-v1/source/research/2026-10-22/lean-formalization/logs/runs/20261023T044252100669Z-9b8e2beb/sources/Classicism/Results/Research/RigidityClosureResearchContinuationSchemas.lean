import Classicism.Results.Research.RigidityClosureResearchRetractionsCertificates

/-! Full-schema assembly for tracked rigidity.02, rigidity.08, rigidity.11.
Every lemma depends on actual translated C certificates; no semantic interface
or proof hypothesis stands in for the missing mathematical argument. -/
namespace Classicism.Meta.Research.RigidityClosure
open AxiomSet

private theorem full_relation_subset_list (q : RTy → Sentence Signature.pure) :
    (fun a => ∃ ρ : RTy, ρ.Closed ∧ a = q ρ) ⊆
      (fun a => ∃ σs : List Ty, Ty.AllClosed σs ∧ a = q (σs ⇒* .t)) :=
  fun _ ⟨ρ, hρ, h⟩ =>
    ⟨ρ.args, RTy.closed_args hρ, h.trans (congrArg q (RTy.ofArgs_args ρ).symm)⟩

abbrev BoundedPropagation := Classicism.Research.RigidityClosure.BoundedTamePropagation.listSchema

/-- Atomicity and RC at all relational types imply full WRP. -/
theorem atomicity_rc_weak_power : P.Atomicity.schema ∪ P.RigidComprehension.schema ⟹
    P.WeaklyRigidPower.schema :=
  Entails.mono_right (full_relation_subset_list _)
    Classicism.Research.RigidityClosure.atomicity_rc_implies_weak_power.listEntails

/-- Forward bounded-propagation decomposition. RP uses WRP at its next property type. -/
theorem weak_power_decomposition : P.WeaklyRigidPower.schema ⟹
    (P.TameRigidity.schema ∪ P.RigidPower.schema) ∪ BoundedPropagation :=
  have hp := Entails.refl P.WeaklyRigidPower.schema
  have hrp := Entails.trans (Entails.union hp hp)
    Classicism.Proofs.weakly_rigid_power_implies_rigid_power.entails
  Entails.union
    (Entails.union Classicism.Proofs.weakly_rigid_power_implies_tame_rigidity.entails hrp)
    Classicism.Research.RigidityClosure.weak_power_bounded_propagation.listEntails

theorem decomposition_weak_power :
    (P.TameRigidity.schema ∪ P.RigidPower.schema) ∪ BoundedPropagation ⟹
      P.WeaklyRigidPower.schema :=
  Entails.mono_right (full_relation_subset_list _)
    Classicism.Research.RigidityClosure.tame_power_bounded_implies_weak_power.listEntails

/-- This is the exact all-schema equivalence, not an unsupported one-type RP claim. -/
theorem weak_power_decomposition_equivalent :
    (P.WeaklyRigidPower.schema ⟹
      (P.TameRigidity.schema ∪ P.RigidPower.schema) ∪ BoundedPropagation) ∧
    (((P.TameRigidity.schema ∪ P.RigidPower.schema) ∪ BoundedPropagation) ⟹
      P.WeaklyRigidPower.schema) := ⟨weak_power_decomposition, decomposition_weak_power⟩

abbrev UniformWeak := Classicism.Research.RigidityClosure.UniformWeakRigidComprehension.schema
abbrev UniformRigid := Classicism.Research.RigidityClosure.UniformRigidComprehension.schema

theorem uniform_weak_implies_nd_comprehension : UniformWeak ⟹
    P.NecessityOfDistinctness.schema ∪ P.WeakRigidComprehension.schema :=
  Entails.union
    Classicism.Research.RigidityClosure.uniform_weak_t_implies_nd.entails
    Classicism.Research.RigidityClosure.uniform_weak_implies_comprehension.entails

theorem nd_comprehension_implies_uniform_weak :
    P.NecessityOfDistinctness.schema ∪ P.WeakRigidComprehension.schema ⟹ UniformWeak :=
  have nd := Entails.union_left P.NecessityOfDistinctness.schema P.WeakRigidComprehension.schema
  have rc := Entails.union_right P.NecessityOfDistinctness.schema P.WeakRigidComprehension.schema
  Entails.mono_right (full_relation_subset_list _)
    (Entails.trans (Entails.union (Entails.union nd rc) rc)
      Classicism.Research.RigidityClosure.nd_weak_comprehension_uniform.listEntails)

theorem uniform_rigid_implies_nd_comprehension : UniformRigid ⟹
    P.NecessityOfDistinctness.schema ∪ P.RigidComprehension.schema :=
  Entails.union
    Classicism.Research.RigidityClosure.uniform_rigid_t_implies_nd.entails
    Classicism.Research.RigidityClosure.uniform_rigid_implies_comprehension.entails

theorem nd_comprehension_implies_uniform_rigid :
    P.NecessityOfDistinctness.schema ∪ P.RigidComprehension.schema ⟹ UniformRigid :=
  have nd := Entails.union_left P.NecessityOfDistinctness.schema P.RigidComprehension.schema
  have rc := Entails.union_right P.NecessityOfDistinctness.schema P.RigidComprehension.schema
  Entails.mono_right (full_relation_subset_list _)
    (Entails.trans (Entails.union (Entails.union nd rc) rc)
      Classicism.Research.RigidityClosure.nd_rigid_comprehension_uniform.listEntails)

theorem uniform_weak_equivalent :
    (UniformWeak ⟹ P.NecessityOfDistinctness.schema ∪ P.WeakRigidComprehension.schema) ∧
    ((P.NecessityOfDistinctness.schema ∪ P.WeakRigidComprehension.schema) ⟹ UniformWeak) :=
  ⟨uniform_weak_implies_nd_comprehension, nd_comprehension_implies_uniform_weak⟩

theorem uniform_rigid_equivalent :
    (UniformRigid ⟹ P.NecessityOfDistinctness.schema ∪ P.RigidComprehension.schema) ∧
    ((P.NecessityOfDistinctness.schema ∪ P.RigidComprehension.schema) ⟹ UniformRigid) :=
  ⟨uniform_rigid_implies_nd_comprehension, nd_comprehension_implies_uniform_rigid⟩

end Classicism.Meta.Research.RigidityClosure

#print axioms Classicism.Meta.Research.RigidityClosure.atomicity_rc_weak_power
#print axioms Classicism.Meta.Research.RigidityClosure.weak_power_decomposition_equivalent
#print axioms Classicism.Meta.Research.RigidityClosure.uniform_weak_equivalent
#print axioms Classicism.Meta.Research.RigidityClosure.uniform_rigid_equivalent
