import Classicism.Models.BooleanColumnDistributivity
import Classicism.Models.BooleanGroundCoverage

/-!
# Protected ground coverage for the concrete column hierarchy

Original supporting formalization (misc), 23 October 2026, of section 5
of `research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
The actual small-table theorem supplies `BinaryTables`; the actual ground
checks then cover every type whose relational subtypes have small ground
argument tables. The recursive protection condition is purely cardinal:
it assumes no coverage, comprehension, model, or Choice verdict.

The size bound is on argument tuples, not the resulting predicate domain.
Thus a protected relational domain may itself have cardinality at least κ.
Choosing a cardinal for a particular finite fragment and deriving typed
selection/separation are separate obligations.
-/

namespace Classicism.Meta.ChoiceBoolean.ProtectedCoverage

open TypedHierarchy GroundChecks ColumnAlgebra

noncomputable section

private theorem bitValue_eq_if {κ : Cardinal} (b : Values κ) (v : Bool) :
    ColumnDistributivity.bitValue b v = if v then b else bᶜ := by
  cases v <;> rfl

/-- The concrete column algebra supplies the exact table equation used
by the generic ground-coverage theorem. -/
theorem binaryTables {κ : Cardinal} (hκ : κ.IsRegular) (G : Type)
    (hG : Cardinal.mk G < κ) : BinaryTables (Values κ) G := by
  intro f
  simpa only [bitValue_eq_if] using
    (ColumnDistributivity.binary_distributivity hκ hG f)

mutual
  /-- Every relational subtype must have fewer than κ ground argument
  tuples. Base types impose no size restriction, since their checks are
  already the identity. -/
  def Protected (κ : Cardinal) (E : Type) : Ty → Prop
    | .e => True
    | .rel ρ => ProtectedArgs κ E ρ ∧
        Cardinal.mk (ChoiceFirstOrder.Full.Tuple E ρ) < κ
    | .var _ => True

  /-- The input types in a flattened tuple are recursively protected. -/
  def ProtectedArgs (κ : Cardinal) (E : Type) : RTy → Prop
    | .t => True
    | .arr σ ρ => Protected κ E σ ∧ ProtectedArgs κ E ρ
end

variable (κ : Cardinal) (E : Type)

mutual
  /-- Actual canonical ground checks cover every recursively protected
  domain of the concrete supported hierarchy. -/
  theorem dom_covers (hκ : κ.IsRegular) :
      ∀ σ, Protected κ E σ → Covers (domMap (action κ) E σ)
    | .e, _ => crisp_covers (action κ) E
    | .rel ρ, h =>
        predicate_covers (tupleMap (action κ) E ρ)
          (tuple_covers hκ ρ h.1)
          (binaryTables hκ (ChoiceFirstOrder.Full.Tuple E ρ) h.2)
    | .var _, _ => crisp_covers (action κ) E

  /-- Tuple coverage follows by finite products of the component coverage
  identities; it adds no table-size or distributivity premise. -/
  theorem tuple_covers (hκ : κ.IsRegular) :
      ∀ ρ, ProtectedArgs κ E ρ → Covers (tupleMap (action κ) E ρ)
    | .t, _ => crisp_covers (action κ) PUnit
    | .arr σ ρ, h =>
        product_covers (domMap (action κ) E σ) (tupleMap (action κ) E ρ)
          (dom_covers hκ σ h.1) (tuple_covers hκ ρ h.2)
end

/-- The coverage equation, stated directly with the actual typed domain
and the actual canonical ground names. -/
theorem ground_coverage (hκ : κ.IsRegular) (σ : Ty) (hσ : Protected κ E σ)
    (x : Dom (action κ) E σ) :
    (⨆ g : ChoiceFirstOrder.Full.Dom E σ,
      (DomSpace (action κ) E σ).space.eqv x (check (action κ) E σ g)) = ⊤ :=
  dom_covers κ E hκ σ hσ x

theorem ground_tuple_coverage (hκ : κ.IsRegular) (ρ : RTy)
    (hρ : ProtectedArgs κ E ρ) (x : Tuple (action κ) E ρ) :
    (⨆ g : ChoiceFirstOrder.Full.Tuple E ρ,
      (TupleSpace (action κ) E ρ).space.eqv x ((tupleMap (action κ) E ρ).check g)) = ⊤ :=
  tuple_covers κ E hκ ρ hρ x

end

end Classicism.Meta.ChoiceBoolean.ProtectedCoverage
