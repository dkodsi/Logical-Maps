import Classicism.Semantics.FullPureEquivariance
import Classicism.Syntax.WitnessedPossibility

/-!
# Full one-world models with exactly one nonlogical predicate

The admitted signature is precisely {c : e→t}. The interpretations are the
existing full `Interp` semantics, with E=Bool or E=Nat and c={0}. In particular,
the truth domain is Lean Prop with extensional equality, not a disconnected
Boolean toy model. Independence is the actual `AxiomSet.independence` schema.

Source: research/2026-10-22/central-questions-audit.md, "The signature and the
two models", "Independence holds", and "Signature qualification"; original
research, unpaginated, direct source misc. New ordinary Lean metatheory.
-/

namespace Classicism.Meta.SinglePredicateFull
open FullPure

def signature : Signature := ⟨Unit, fun _ => Ty.e ⇒ RTy.t⟩

theorem signature_admitted : signature.Admitted := by
  constructor
  · intro c
    exact ⟨True.intro, True.intro⟩
  · exact ⟨(), by intro h; cases h⟩

def boolModel : Interp signature := ⟨Bool, fun _ x => x = false⟩
def natModel : Interp signature := ⟨Nat, fun _ x => x = 0⟩

instance boolModel_nonempty : Nonempty boolModel.D := ⟨false⟩
instance natModel_nonempty : Nonempty natModel.D := ⟨0⟩

def boolSwap : Perm Bool :=
  ⟨Bool.not, Bool.not, fun x => by cases x <;> rfl, fun x => by cases x <;> rfl⟩

def swapZeroOne : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

theorem swapZeroOne_twice : ∀ n, swapZeroOne (swapZeroOne n) = n
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

def natSwap : Perm Nat := ⟨swapZeroOne, swapZeroOne, swapZeroOne_twice, swapZeroOne_twice⟩

theorem bool_predicate_moved :
    moveR boolSwap (.arr .e .t) (fun x : Bool => x = false) ≠ (fun x => x = false) := by
  intro h
  have e := congrFun h false
  change (true = false) = (false = false) at e
  have bad : (true : Bool) = false := Eq.mpr e rfl
  cases bad

theorem nat_predicate_moved :
    moveR natSwap (.arr .e .t) (fun x : Nat => x = 0) ≠ (fun x => x = 0) := by
  intro h
  have e := congrFun h 0
  change (1 = 0) = (0 = 0) at e
  have bad : (1 : Nat) = 0 := Eq.mpr e rfl
  cases bad

theorem bool_closed_pure_ne (A : Term Signature.pure [] (Ty.e ⇒ RTy.t)) :
    boolModel.const () ≠ (Term.ofPure A).denote boolModel .nil :=
  Ne.symm (moved_predicate_not_pure boolModel boolSwap _ bool_predicate_moved
    (Term.ofPure A) (Term.pure_ofPure A))

theorem nat_closed_pure_ne (A : Term Signature.pure [] (Ty.e ⇒ RTy.t)) :
    natModel.const () ≠ (Term.ofPure A).denote natModel .nil :=
  Ne.symm (moved_predicate_not_pure natModel natSwap _ nat_predicate_moved
    (Term.ofPure A) (Term.pure_ofPure A))

/-- With this exact signature, a distinct list of other constants must be empty. -/
theorem other_constants_nil (c : signature.Const) (ds : List signature.Const)
    (h : (c :: ds).Nodup) : ds = [] := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    have hn := (List.nodup_cons.mp h).1
    have he : c = d := @Subsingleton.elim Unit inferInstance c d
    exact (hn (List.mem_cons.mpr (Or.inl he))).elim

theorem independence_of_pure_ne (I : Interp signature)
    (hI : ∀ A : Term Signature.pure [] (Ty.e ⇒ RTy.t),
      I.const () ≠ (Term.ofPure A).denote I .nil) :
    (AxiomSet.independence signature).holds I := by
  rintro a ⟨_, c, ds, ρ, ht, A, hd, rfl⟩
  have hn := other_constants_nil c ds hd
  subst ds
  cases c
  have hr : ρ = RTy.arr Ty.e RTy.t := Ty.rel.inj ht.symm
  subst ρ
  change I.const () ≠ (Term.ofPure A).denote I .nil
  exact hI A

theorem bool_independence : (AxiomSet.independence signature).holds boolModel :=
  independence_of_pure_ne boolModel bool_closed_pure_ne

theorem nat_independence : (AxiomSet.independence signature).holds natModel :=
  independence_of_pure_ne natModel nat_closed_pure_ne

theorem bool_C : C.axioms.holds boolModel := C.axioms_holds boolModel
theorem nat_C : C.axioms.holds natModel := C.axioms_holds natModel

/-- Exact-schema consistency; the semantic soundness theorem supplies the C bridge. -/
theorem independence_consistent : (AxiomSet.independence signature).Consistent :=
  AxiomSet.Consistent.of_interp boolModel bool_independence

end Classicism.Meta.SinglePredicateFull
