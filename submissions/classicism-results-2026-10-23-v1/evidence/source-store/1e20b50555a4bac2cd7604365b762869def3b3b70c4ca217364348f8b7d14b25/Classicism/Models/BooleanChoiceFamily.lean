import Classicism.Models.BooleanChoiceCutoff
import Classicism.Models.BooleanSelectorObstruction

/-!
# The concrete higher column family at a finite Choice cutoff

Original supporting formalization (misc), 23 October 2026, of sections 7--8
of `research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
The actual cutoff embedding into the ground domain of `tower m` is padded
by PUnit, giving ground argument tuples for `tower (m+1)`. The canonical
ground checks and actual Boolean coordinate profiles then construct the
higher column family, with its proved action and zero pairwise equality.

No injection or family-existence hypothesis remains. This module supplies
the concrete family to the separate typed selector-failure translation;
it does not itself claim a final object-language Choice verdict.
-/

namespace Classicism.Meta.ChoiceBoolean.ChoiceFamily

open ChoiceCutoff ColumnAlgebra GroundChecks TypedHierarchy SelectorObstruction

noncomputable section

/-- The relational type whose arguments contain the preceding ground tower. -/
abbrev higherType (m : Nat) : RTy := ChoiceHierarchy.tower (m + 1)

abbrev argumentSpace (m : Nat) : ActionSpace (action (cutoff m)) :=
  TupleSpace (action (cutoff m)) Nat (higherType m)

/-- An actual embedding into the flattened ground argument tuple. -/
def rowEmbedding (m : Nat) :
    (cutoff m).out ↪ ChoiceFirstOrder.Full.Tuple Nat (higherType m) where
  toFun r := (groundInjection m r, PUnit.unit)
  inj' := by
    intro i j h
    exact (groundInjection m).injective (congrArg Prod.fst h)

theorem rowEmbedding_apply (m : Nat) (r : (cutoff m).out) :
    rowEmbedding m r = (groundInjection m r, PUnit.unit) := rfl

abbrev groundArguments (m : Nat) :
    GroundMap (argumentSpace m) (ChoiceFirstOrder.Full.Tuple Nat (higherType m)) :=
  tupleMap (action (cutoff m)) Nat (higherType m)

/-- The constructed column profiles live in the actual relational domain. -/
def family (m : Nat) :
    ColumnFamily (DomSpace (action (cutoff m)) Nat (.rel (higherType m))) :=
  profileFamily (cutoff_regular m).aleph0_le (groundArguments m)
    (rowEmbedding m) (rowEmbedding m).injective

theorem family_equivariant (m : Nat) (π : Equiv.Perm (cutoff m).out)
    (i : (cutoff m).out) :
    (DomSpace (action (cutoff m)) Nat (.rel (higherType m))).action.act π
        ((family m).entry i) = (family m).entry (π i) :=
  (family m).equivariant π i

theorem family_separated (m : Nat) (i j : (cutoff m).out) (hij : i ≠ j) :
    (DomSpace (action (cutoff m)) Nat (.rel (higherType m))).space.eqv
        ((family m).entry i) ((family m).entry j) = ⊥ :=
  (family m).separated i j hij

/-- Evaluation at the embedded checked row gives the actual coordinate bit. -/
theorem family_coordinate (m : Nat) (i r : (cutoff m).out) :
    Predicate.toFun (X := (argumentSpace m).space) ((family m).entry i).val
      ((groundArguments m).check (rowEmbedding m r)) =
      ColumnCoordinates.coordinate (cutoff_regular m).aleph0_le i r :=
  IndexedProfiles.column_check (cutoff_regular m).aleph0_le (groundArguments m)
    (rowEmbedding m) (rowEmbedding m).injective i r

/-- Direct specialization to the cutoff chosen for a finite type collection. -/
def fragmentFamily (Ω : Finset Ty) :
    ColumnFamily (DomSpace (action (cutoff (finiteRank Ω))) Nat
      (.rel (higherType (finiteRank Ω)))) :=
  family (finiteRank Ω)

end

end Classicism.Meta.ChoiceBoolean.ChoiceFamily
