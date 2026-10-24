import Classicism.Results.Research.MaxPredecessorGraphCertificates
import Classicism.Results.Research.MaxPredecessorModel
import Classicism.Certified.Arithmetic
import Mathlib.Data.Set.Finite.Basic

/-!
# Pure Max: the predecessor graph exists, but no operation realizes it (at e)

Direct source: relational-coding-recursion-20261022.md §38, misc. The external
Nat-model Infinity proof below follows the existing semantic proof
Consistency.axiomOfInfinityE_holds_nat in Results/Consistency/Consistency.lean.
It is reproduced here to avoid importing unrelated countermodel families.
The theorem for every counting type remains MaxPredecessorSchema's no-operation
result; this stronger graph certificate is explicitly restricted to e.
-/

namespace Classicism.Meta.Research.MaxPredecessorGraphModel
open Classicism.Research.MaxPredecessor Classicism.Research.MaxPredecessorGraph AxiomSet

private instance : Nonempty (Interp.ofDomain Nat).D := inferInstanceAs (Nonempty Nat)

theorem infinity_holds_nat :
    Sentence.holds (Interp.ofDomain Nat) P.AxiomOfInfinityE.quoted := by
  classical
  simp only [Sentence.holds, Term.denote, Var.denote, top_eq, imp_eq]
  change ¬ ∃ Z : (Nat → Prop) → Prop, (∀ W : ((Nat → Prop) → Prop) → Prop,
      (W (fun X => ∀ u, ¬ X u) ∧ ∀ Y, W Y → W (fun X => ∃ y, X y ∧ Y (fun u => X u ∧ ¬ u = y))) → W Z) ∧
      Z (fun _ => True)
  rintro ⟨Z, hZ, hZt⟩
  have key := hZ (fun Z => ∀ X : Nat → Prop, Z X → {u | X u}.Finite)
    ⟨fun X hX => Set.finite_empty.subset fun u hu => hX u hu,
     fun Y hY X ⟨y, _, hYX⟩ => ((hY _ hYX).insert y).subset fun u hu => by
       by_cases h : u = y
       · exact Or.inl h
       · exact Or.inr ⟨hu, h⟩⟩
  exact Set.infinite_univ (key _ hZt)

theorem infinity_implies_peano_C :
    C.TheoremMinus (Term.imp P.AxiomOfInfinityE.quoted (Peano.term Ty.e)) :=
  Derivable.conv (infinity_to_peano.derivable Ty.e) (Conv.of_nf 64 _ _ rfl)

theorem peano_holds_nat : Sentence.holds (Interp.ofDomain Nat) (Peano.term Ty.e) := by
  have h := C.TheoremMinus.holds (Interp.ofDomain Nat) infinity_implies_peano_C
  change (¬ Sentence.holds (Interp.ofDomain Nat) P.AxiomOfInfinityE.quoted ∨
    Sentence.holds (Interp.ofDomain Nat) (Peano.term Ty.e)) at h
  exact h.elim (fun hn => (hn infinity_holds_nat).elim) id

theorem peano_consistent : Consistent (empty ∪ single (Peano.term Ty.e)) :=
  Consistent.of_interp (Interp.ofDomain Nat) (fun _ h =>
    h.elim False.elim (fun he => he ▸ peano_holds_nat))

/-- This is precisely ArithmeticI_e: the possibility of IStar_e. -/
theorem maximalism_arithmeticI_e :
    Theorem (C.axioms ∪ maximalist) (Term.dia (Peano.term Ty.e)) :=
  maximalist_entails_possibility _ (possibility_mem rfl peano_consistent)

/-- The displayed total unique graph exists, and no operation realizes it.
Both Max's noncollapse condition and the no-operation premise are discharged. -/
theorem maximalism_graph_without_operation_e :
    Theorem (C.axioms ∪ maximalist) (GraphClaim.term Ty.e) := by
  have h : C.TheoremMinus
      (Term.imp (Term.dia (Peano.term Ty.e))
        (Term.imp (Term.neg (PredOp.term Ty.e)) (GraphClaim.term Ty.e))) :=
    Derivable.conv (possible_peano_gives_graph.derivable Ty.e) (Conv.of_nf 64 _ _ rfl)
  exact Theorem.mp (Theorem.mp (Theorem.ofCMinus h) maximalism_arithmeticI_e)
    MaxPredecessorModel.maximalism_no_predecessor_e

theorem maximalism_not_plenitude_e_numbers :
    Theorem (C.axioms ∪ maximalist)
      (Term.neg (P.Plenitude.quoted (Ty.nu Ty.e) ((Ty.e ⇒ RTy.t) ⇒ RTy.t))) := by
  have h : C.TheoremMinus
      (Term.imp (Term.dia (Peano.term Ty.e))
        (Term.imp (Term.neg (PredOp.term Ty.e))
          (Term.neg (P.Plenitude.quoted (Ty.nu Ty.e) ((Ty.e ⇒ RTy.t) ⇒ RTy.t))))) :=
    Derivable.conv (possible_peano_refutes_plenitude.derivable Ty.e) (Conv.of_nf 64 _ _ rfl)
  exact Theorem.mp (Theorem.mp (Theorem.ofCMinus h) maximalism_arithmeticI_e)
    MaxPredecessorModel.maximalism_no_predecessor_e

end Classicism.Meta.Research.MaxPredecessorGraphModel

#print axioms Classicism.Meta.Research.MaxPredecessorGraphModel.infinity_holds_nat
#print axioms Classicism.Meta.Research.MaxPredecessorGraphModel.peano_consistent
#print axioms Classicism.Meta.Research.MaxPredecessorGraphModel.maximalism_arithmeticI_e
#print axioms Classicism.Meta.Research.MaxPredecessorGraphModel.maximalism_graph_without_operation_e
#print axioms Classicism.Meta.Research.MaxPredecessorGraphModel.maximalism_not_plenitude_e_numbers
