import Classicism.Results.Research.MaxPredecessorModel
import Classicism.Certified.Arithmetic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finite.Prod

/-!
# No numerical predecessor operation at any closed counting type

Direct source: relational-coding-recursion-20261022.md §38, misc.
This certificate uses an equivalent finite-orbit witness: the singleton full
model has a finite numerical domain, so its numeral orbit cannot have injective
successor while zero is outside the successor range. Two external numeral
indices therefore supply a finite, closed, pure collision sentence. No
consistency hypothesis remains in the principal theorem.
-/

namespace Classicism.Meta.Research.MaxPredecessorSchema
open Classicism.Research.MaxPredecessor AxiomSet
noncomputable section

def numeral (σ : Ty) : Nat → Term Signature.pure [] (Ty.nu σ)
  | 0 => Classicism.Arith.zero.term σ
  | n + 1 => .app (Classicism.Arith.suc.term σ) (numeral σ n)

def number (σ : Ty) (n : Nat) : Sentence Signature.pure :=
  .app (Classicism.Arith.N.term σ) (numeral σ n)

def collision (σ : Ty) (i j : Nat) : Sentence Signature.pure :=
  Term.conj (Term.eq' (numeral σ (i + 1)) (numeral σ (j + 1)))
    (Term.neg (Term.eq' (numeral σ i) (numeral σ j)))

theorem numeral_closedTypes (σ : Ty) (hσ : σ.Closed) :
    ∀ n, (numeral σ n).closedTypes = true
  | 0 => Arith.zero_closedTypes hσ
  | n + 1 => by
    simp only [numeral, Term.closedTypes, Arith.suc_closedTypes hσ,
      numeral_closedTypes σ hσ n, Bool.and_self]

theorem collision_closedTypes (σ : Ty) (hσ : σ.Closed) (i j : Nat) :
    (collision σ i j).closedTypes = true := by
  simp [collision, numeral_closedTypes σ hσ]

def successorStatement (σ : Ty) : Sentence Signature.pure :=
  Term.forall' (σ := Ty.nu σ)
    (Term.imp (.app (Classicism.Arith.N.term σ).close Term.v0)
      (.app (Classicism.Arith.N.term σ).close
        (.app (Classicism.Arith.suc.term σ).close Term.v0)))

theorem successor_rule (σ : Ty) : C.TheoremMinus (successorStatement σ) :=
  Derivable.conv (Classicism.finiteCardinality_suc.derivable σ)
    (Conv.of_nf 32 _ _ rfl)

theorem numeral_is_number (σ : Ty) : ∀ n, C.TheoremMinus (number σ n)
  | 0 => Derivable.conv (Classicism.finiteCardinality_zero.derivable σ)
      (Conv.of_nf 32 _ _ rfl)
  | n + 1 => by
    have hs : C.TheoremMinus
        (Term.imp (number σ n) (number σ (n + 1))) :=
      Derivable.allEβ (successor_rule σ) (numeral σ n)
    exact Derivable.impE hs (numeral_is_number σ n)

def collisionStatement (σ : Ty) : Sentence Signature.pure :=
  Term.forall' (σ := Ty.nu σ) (Term.forall' (σ := Ty.nu σ)
    (Term.imp (.app (Classicism.Arith.N.term σ).close Term.v1)
      (Term.imp (.app (Classicism.Arith.N.term σ).close Term.v0)
        (Term.imp (Term.dia
          (Term.conj
            (Term.eq' (.app (Classicism.Arith.suc.term σ).close Term.v1)
              (.app (Classicism.Arith.suc.term σ).close Term.v0))
            (Term.neg (Term.eq' Term.v1 Term.v0))))
          (Term.neg (PredOp.term σ).close)))))

theorem collision_general_rule (σ : Ty) : C.TheoremMinus (collisionStatement σ) :=
  Derivable.conv (collision_excludes_predecessor.derivable σ)
    (Conv.of_nf 64 _ _ rfl)

theorem collision_rule (σ : Ty) (i j : Nat) :
    C.TheoremMinus (Term.imp (Term.dia (collision σ i j)) (Term.neg (PredOp.term σ))) := by
  have h : C.TheoremMinus
      (Term.imp (number σ i) (Term.imp (number σ j)
        (Term.imp (Term.dia (collision σ i j)) (Term.neg (PredOp.term σ))))) :=
    Derivable.allE₂β (collision_general_rule σ) (numeral σ i) (numeral σ j)
  exact Derivable.impE (Derivable.impE h (numeral_is_number σ i)) (numeral_is_number σ j)

mutual
  theorem finite_type : ∀ σ : Ty, _root_.Finite (σ.denote Unit)
    | .e => inferInstance
    | .var _ => inferInstance
    | .rel ρ => finite_rel ρ
  theorem finite_rel : ∀ ρ : RTy, _root_.Finite (ρ.denote Unit)
    | .t => inferInstance
    | .arr σ ρ => by
      letI := finite_type σ
      letI := finite_rel ρ
      exact inferInstanceAs (_root_.Finite (σ.denote Unit → ρ.denote Unit))
end

local instance (σ : Ty) : Classicism.Ty (σ.denote Unit) := ⟨()⟩

def value (σ : Ty) : Nat → (σ.denote Unit → Prop) → Prop
  | 0 => Classicism.ZeroCard (σ.denote Unit)
  | n + 1 => Classicism.SucCard (value σ n)

theorem numeral_denote (σ : Ty) : ∀ n,
    (numeral σ n).denote (Interp.ofDomain Unit) .nil = value σ n
  | 0 => rfl
  | n + 1 => congrArg (@Classicism.SucCard (σ.denote Unit) ⟨()⟩) (numeral_denote σ n)

/-- Finiteness is used only in the external singleton model. The witnesses
are indices of actual finite terms, not arbitrary model elements. -/
theorem finite_orbit_collision (σ : Ty) :
    ∃ i j, value σ (i + 1) = value σ (j + 1) ∧ value σ i ≠ value σ j := by
  classical
  letI := finite_type (Ty.nu σ)
  let O := {x : (σ.denote Unit → Prop) → Prop // ∃ n, value σ n = x}
  let z : O := ⟨value σ 0, 0, rfl⟩
  let s : O → O := fun x => ⟨Classicism.SucCard x.val, by
    obtain ⟨n, hn⟩ := x.property
    exact ⟨n + 1, congrArg Classicism.SucCard hn⟩⟩
  by_contra hn
  have hi : Function.Injective s := by
    intro x y hxy
    apply Subtype.ext
    obtain ⟨i, hi⟩ := x.property
    obtain ⟨j, hj⟩ := y.property
    by_contra hne
    apply hn
    refine ⟨i, j, ?_, ?_⟩
    · exact (congrArg Classicism.SucCard hi).trans
        ((congrArg Subtype.val hxy).trans (congrArg Classicism.SucCard hj).symm)
    · intro he
      exact hne (hi.symm.trans (he.trans hj))
  obtain ⟨x, hx⟩ := _root_.Finite.surjective_of_injective hi z
  exact Classicism.Research.frege_zero_ne_suc x.val (congrArg Subtype.val hx).symm

theorem collision_holds (σ : Ty) (i j : Nat)
    (h : value σ (i + 1) = value σ (j + 1) ∧ value σ i ≠ value σ j) :
    Sentence.holds (Interp.ofDomain Unit) (collision σ i j) := by
  change ((numeral σ (i + 1)).denote (Interp.ofDomain Unit) .nil =
      (numeral σ (j + 1)).denote (Interp.ofDomain Unit) .nil) ∧
    ((numeral σ i).denote (Interp.ofDomain Unit) .nil ≠
      (numeral σ j).denote (Interp.ofDomain Unit) .nil)
  constructor
  · exact (numeral_denote σ (i + 1)).trans (h.1.trans (numeral_denote σ (j + 1)).symm)
  · intro he
    exact h.2 ((numeral_denote σ i).symm.trans (he.trans (numeral_denote σ j)))

private instance : Nonempty (Interp.ofDomain Unit).D := ⟨()⟩

/-- Every fixed admitted counting type has a fully discharged pure Max(C)
certificate. The type parameter is metalinguistic, never an object quantifier. -/
theorem maximalism_no_predecessor (σ : Ty) (hσ : σ.Closed) :
    Theorem (C.axioms ∪ maximalist) (Term.neg (PredOp.term σ)) := by
  obtain ⟨i, j, h⟩ := finite_orbit_collision σ
  have hc : Consistent (empty ∪ single (collision σ i j)) :=
    Consistent.of_interp (Interp.ofDomain Unit) (fun _ ha =>
      ha.elim False.elim (fun he => he ▸ collision_holds σ i j h))
  have hp : Theorem (C.axioms ∪ maximalist) (Term.dia (collision σ i j)) :=
    maximalist_entails_possibility _ (possibility_mem (collision_closedTypes σ hσ i j) hc)
  exact Theorem.mp (Theorem.ofCMinus (collision_rule σ i j)) hp

end
end Classicism.Meta.Research.MaxPredecessorSchema

#print axioms Classicism.Meta.Research.MaxPredecessorSchema.finite_orbit_collision
#print axioms Classicism.Meta.Research.MaxPredecessorSchema.numeral_is_number
#print axioms Classicism.Meta.Research.MaxPredecessorSchema.collision_rule
#print axioms Classicism.Meta.Research.MaxPredecessorSchema.maximalism_no_predecessor
#check Classicism.Meta.Research.MaxPredecessorSchema.maximalism_no_predecessor
