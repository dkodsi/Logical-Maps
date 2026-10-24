import Classicism.Models.FixedPointEntranceRoot
import Classicism.Models.FixedPointEntranceActuality
import Classicism.Models.FixedPointEntranceRelationalBarcan
import Classicism.Models.QualitativeLinksTameWitness

/-!
# The fixed-point entrance separates root rigidity from boxed rigidity

Original assembly (misc), 23 October 2026. Direct source:
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, sections 1--6
(unpaginated). The concrete model satisfies the full root schemas for
Atomicity, Boolean Completeness, Rigid Comprehension, Relational Choice,
Tame Rigidity, Rigid Power, and Weakly Rigid Power, together with boxed
Strong Actuality and individual Barcan. Its admitted qualitative fibre
predicate refutes Tame Rigidity at the tail, hence boxed Tame Rigidity
at the root. Barcan fails at every relational argument type, and ND_t
fails at the root. No modelhood or semantic verdict is a hypothesis.

Strong Leibniz is not included in this assembly. Formal verification is
the responsibility of the shared serial integrator.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative

open CategoryTheory AxiomSet

/-- Boxed Tame Rigidity fails in the original rooted model, by its actual
entrance arrow and the admitted predicate at type (tt)t. -/
theorem root_not_box_tame :
    ¬ model.HoldsSentence (Term.box (P.TameRigidity.quoted TameWitness.ut)) := by
  intro h
  have ht := (model.holds_box isModel (𝟙 (A tail))
    (P.TameRigidity.quoted TameWitness.ut) .nil).1 h (entrance tail)
  apply TameWitness.not_tail_tame
  exact Eq.mp (congrArg
    (fun k : A tail ⟶ B tail =>
      model.Holds k (P.TameRigidity.quoted TameWitness.ut) .nil)
    (Category.id_comp (entrance tail))) ht

theorem holds_necessary_strongActuality_schema :
    model.HoldsAx P.NecStrongActuality.schema := by
  intro p hp
  change p = P.NecStrongActuality.quoted at hp
  subst p
  exact Actuality.necessary_strongActuality

/-- All seven type-parametric premises are full schemas. Only Strong
Actuality is boxed here; individual Barcan is one closed instance. -/
abbrev Background : AxiomSet Signature.pure :=
  P.Atomicity.schema ∪
    (P.BooleanCompleteness.schema ∪
    (P.RigidComprehension.schema ∪
    (P.RelationalChoice.schema ∪
    (P.TameRigidity.schema ∪
    (P.RigidPower.schema ∪
    (P.WeaklyRigidPower.schema ∪
    (P.NecStrongActuality.schema ∪ AxiomSet.single (Sentence.bf .e))))))))

theorem holds_background : model.HoldsAx Background := by
  apply model.holdsAx_union Atomicity.holds_atomicity_schema
  apply model.holdsAx_union Completeness.holds_bc_schema
  apply model.holdsAx_union Comprehension.holds_rigid_comprehension_schema
  apply model.holdsAx_union RelationalChoice.holds_relational_choice_schema
  apply model.holdsAx_union Rigidity.holds_tame_schema
  apply model.holdsAx_union Powers.holds_rigid_power_schema
  apply model.holdsAx_union Powers.holds_weak_power_schema
  exact model.holdsAx_union holds_necessary_strongActuality_schema
    (model.holdsAx_single Distinctness.bf_e)

theorem background_consistent : Background.Consistent :=
  AxiomSet.Consistent.of_model model isModel holds_background

theorem not_theorem_box_tame :
    ¬ Theorem (Classicism.Meta.C.axioms ∪ Background)
      (Term.box (P.TameRigidity.quoted TameWitness.ut)) :=
  model.not_theorem_of_model isModel holds_background root_not_box_tame

theorem not_entails_box_tame : ¬ (Background ⟹ P.NecTameRigidity.schema) :=
  fun h => not_theorem_box_tame
    (h _ ⟨TameWitness.ut, ⟨⟨trivial, trivial⟩, trivial⟩, rfl⟩)

/-- The assembled separator, with all relational Barcan failures and
propositional distinctness failure. Its positive background is defined
above entirely by actual quoted schemas and a closed singleton axiom. -/
theorem complete_countermodel :
    model.IsModel ∧
    (∀ W : cone.Ob, Subsingleton (model.Dom W .e)) ∧
    model.HoldsAx Background ∧
    ¬ model.HoldsSentence (Term.box (P.TameRigidity.quoted TameWitness.ut)) ∧
    ¬ model.Holds (entrance tail) (P.TameRigidity.quoted TameWitness.ut) .nil ∧
    (∀ ρ : RTy, ¬ model.HoldsSentence (P.Barcan.quoted (.rel ρ))) ∧
    ¬ model.HoldsSentence (Sentence.nd (.rel .t)) :=
  ⟨isModel, individual_singleton, holds_background, root_not_box_tame,
    TameWitness.not_tail_tame, RelationalBarcan.not_barcan_relational,
    Distinctness.not_nd_t⟩

end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative
