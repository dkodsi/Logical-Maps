import Classicism.Semantics.Research.CentralSupportedProductChoice

open Classicism.Meta
open Classicism.Meta.Intensional.Central.OneConstant

-- Model construction, exact package satisfaction, and failure are all checked.
example : B.IsModel ∧ B.HoldsAx package ∧
    ¬ B.HoldsSentence (Term.ofPure Classicism.P.Actuality.quoted) :=
  ⟨B_isModel, holds_package, not_holds_actuality⟩

example : package.Consistent ∧ ¬ (package ⟹ Classicism.P.Actuality.schemaIn) :=
  ⟨package_consistent, package_not_entails_actuality⟩

#print axioms Classicism.Meta.Intensional.Central.model_isModel
#print axioms Classicism.Meta.Intensional.Central.OneConstant.B_isModel
#print axioms Classicism.Meta.Intensional.Central.OneConstant.holds_logicalNecessity
#print axioms Classicism.Meta.Intensional.Central.OneConstant.holds_package
#print axioms Classicism.Meta.Intensional.Central.OneConstant.package_consistent
#print axioms Classicism.Meta.Intensional.Central.OneConstant.package_not_entails_actuality
