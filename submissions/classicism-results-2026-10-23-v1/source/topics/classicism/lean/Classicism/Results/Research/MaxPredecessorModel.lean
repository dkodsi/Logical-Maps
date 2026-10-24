import Classicism.Results.Research.MaxPredecessorCertificates
import Classicism.Results.SentenceSchemas.PossibilityDistinctness

/-!
# Exact pure-Max certificate for predecessor at counting type e

Direct source: relational-coding-recursion-20261022.md §38 (original research,
unpaginated, misc). The consistency side condition is discharged in the full
one-world Henkin interpretation with a singleton individual domain. All uses
of Lean's extensionality here are in the metatheory of that model, after the
object-language proof has passed the C gate and been translated.
-/

namespace Classicism.Meta.Research.MaxPredecessorModel
open Classicism.Research.MaxPredecessor AxiomSet

private instance : Classicism.Ty Unit := ⟨()⟩
private instance : Nonempty (Interp.ofDomain Unit).D := ⟨()⟩

/-- In the full singleton interpretation no property has two members. -/
theorem two_empty : Two Unit = (fun _ => False) := by
  funext X
  apply propext
  constructor
  · rintro ⟨y, _, z, hz, _⟩
    exact hz.2 (Subsingleton.elim z y)
  · exact False.elim

theorem three_empty : Three Unit = (fun _ => False) := by
  change Classicism.SucCard (Two Unit) = (fun _ => False)
  rw [two_empty]
  exact Classicism.Research.FregeNoncollapse.successor_bottom

theorem one_not_two : Classicism.Research.MaxPredecessor.One Unit ≠ Two Unit := by
  intro he
  have hone : Classicism.Research.MaxPredecessor.One Unit (fun _ => True) :=
    ⟨(), True.intro, fun u hu => hu.2 (Subsingleton.elim u ())⟩
  have htwo : Two Unit (fun _ => True) := he ▸ hone
  rw [two_empty] at htwo
  exact htwo

theorem collision_holds_singleton :
    Sentence.holds (Interp.ofDomain Unit) (Collision.term Ty.e) := by
  change Two Unit = Three Unit ∧ Classicism.Research.MaxPredecessor.One Unit ≠ Two Unit
  exact ⟨two_empty.trans three_empty.symm, one_not_two⟩

theorem collision_consistent :
    Consistent (empty ∪ single (Collision.term Ty.e)) :=
  Consistent.of_interp (Interp.ofDomain Unit) (fun _ h =>
    h.elim False.elim (fun he => he ▸ collision_holds_singleton))

theorem collision_closedTypes : (Collision.term Ty.e).closedTypes = true := rfl

theorem maximalism_possible_collision :
    Theorem (C.axioms ∪ maximalist) (Term.dia (Collision.term Ty.e)) :=
  maximalist_entails_possibility _ (possibility_mem collision_closedTypes collision_consistent)

/-- The principal result: the actual pure-Max theory proves the negation of
the exact unboxed predecessor-operation sentence. No consistency or model
premise remains in this theorem. -/
theorem maximalism_no_predecessor_e :
    Theorem (C.axioms ∪ maximalist) (Term.neg (PredOp.term Ty.e)) := by
  have hc : Theorem (C.axioms ∪ maximalist)
      (Term.imp (Term.dia (Collision.term Ty.e)) (Term.neg (PredOp.term Ty.e))) :=
    Derivable.conv (Theorem.ofCMinus (possible_collision_excludes_predecessor.derivable Ty.e))
      (Conv.of_nf 64 _ _ rfl)
  exact Theorem.mp hc maximalism_possible_collision

end Classicism.Meta.Research.MaxPredecessorModel

#print axioms Classicism.Meta.Research.MaxPredecessorModel.collision_holds_singleton
#print axioms Classicism.Meta.Research.MaxPredecessorModel.collision_consistent
#print axioms Classicism.Meta.Research.MaxPredecessorModel.maximalism_possible_collision
#print axioms Classicism.Meta.Research.MaxPredecessorModel.maximalism_no_predecessor_e
#check Classicism.Meta.Research.MaxPredecessorModel.maximalism_no_predecessor_e
