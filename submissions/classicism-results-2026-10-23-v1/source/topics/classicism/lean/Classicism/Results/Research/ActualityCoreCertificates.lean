import Classicism.Results.Research.ActualityCore
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Requested checks, not a claim that they have run. Only the serial compiler
owner may execute these commands. The `#check` declarations intentionally make
missing tuple certificates a failure rather than silently downgrading scope. -/

#classicism_audit Classicism.Results.Research.ActualityCore
#classicism_types_audit Classicism.Results.Research.ActualityCore

#classicism_schema Classicism.Research.ActualityCore.Localization
  Classicism.Research.ActualityCore.IntervalCompleteness
  Classicism.Research.ActualityCore.LocalAtomCoverage

#classicism_certify Classicism.Research.ActualityCore.localization_law
  Classicism.Research.ActualityCore.interval_completeness_law
  Classicism.Research.ActualityCore.local_atom_coverage_law

#check Classicism.Research.ActualityCore.localization_law.rule
#check Classicism.Research.ActualityCore.interval_completeness_law.listRule
#check Classicism.Research.ActualityCore.local_atom_coverage_law.listRule
#print axioms Classicism.Research.ActualityCore.localization_law.rule
#print axioms Classicism.Research.ActualityCore.interval_completeness_law.listRule
#print axioms Classicism.Research.ActualityCore.local_atom_coverage_law.listRule
