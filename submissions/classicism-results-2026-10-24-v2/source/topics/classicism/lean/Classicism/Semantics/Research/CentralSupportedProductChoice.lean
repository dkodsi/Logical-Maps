import Classicism.Semantics.Research.CentralLogicalNecessity
import Classicism.Semantics.Research.CentralProductChoice

/-!
# Actual choice and the strengthened finite-signature separator

The supported product admits every constant extension profile. Consequently
it is extensionally full, although it is not an intensionally full model.
The existing, independently stated extensionally-full-model theorems yield
all-type boxed Relational Choice. They do not yield Boolean Completeness.
Source: `followup/central-map.md`, §§1–2; the semantic choice proof is the
existing `FullModels.holds_rc` theorem in classical metatheory.
Uncompiled author draft, 22 October 2026.
-/


namespace Classicism.Meta.Intensional.Central.OneConstant
open Product

theorem holds_boxed_relationalChoice_schema : B.HoldsAx P.NecRelationalChoice.schemaIn := by
  apply (B.holdsAx_ofPure P.NecRelationalChoice.schema).2
  rw [reduct_eq]
  rintro p ⟨σ, τ, _, _, rfl⟩
  exact pure_holds_box_rc (Set Nat) Label σ τ

theorem holds_boxed_barcan_schema : B.HoldsAx P.NecBarcan.schemaIn := by
  rintro p ⟨q, ⟨σ, _, rfl⟩, rfl⟩
  change B.HoldsSentence (Term.box (Sentence.bf σ))
  exact holds_all_boxed_barcan σ

def package : AxiomSet signature :=
  (AxiomSet.logicalNecessity signature ∪ P.NecBarcan.schemaIn) ∪
    P.NecRelationalChoice.schemaIn

theorem holds_package : B.HoldsAx package :=
  B.holdsAx_union (B.holdsAx_union holds_logicalNecessity holds_boxed_barcan_schema)
    holds_boxed_relationalChoice_schema

theorem package_consistent : package.Consistent :=
  AxiomSet.Consistent.of_model B B_isModel holds_package

/-- The full map Actuality schema fails as a consequence of the stated package. -/
theorem package_not_entails_actuality : ¬ (package ⟹ P.Actuality.schemaIn) :=
  B.not_entails_of_model B_isModel holds_package
    (a := Term.ofPure P.Actuality.quoted) ⟨P.Actuality.quoted, rfl, rfl⟩ not_holds_actuality

end Classicism.Meta.Intensional.Central.OneConstant
