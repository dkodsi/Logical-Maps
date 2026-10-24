import Classicism.Results.Research.CoalescedCHVocabulary
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema
import Classicism.Tools.Translate

/-! Quotation and gate checks for the exact relational CH vocabulary. No
consistency or model-existence assertion is introduced here. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option pp.maxSteps 100

#eval (do
  let out ← IO.getStdout
  out.putStrLn "CH vocabulary: imports ready"
  out.flush : IO Unit)

#classicism_audit Classicism.Results.Research.CoalescedCHVocabulary
#classicism_types_audit Classicism.Results.Research.CoalescedCHVocabulary

#eval (do
  let out ← IO.getStdout
  out.putStrLn "CH vocabulary: gate and type audits complete"
  out.flush : IO Unit)

#classicism_schema
  Classicism.Research.CoalescedCH.StructuralCH
  Classicism.Research.CoalescedCH.HasRealCH
  Classicism.Research.CoalescedCH.HasRealNotCH
  Classicism.Research.CoalescedCH.NonContingency

#eval (do
  let out ← IO.getStdout
  out.putStrLn "CH vocabulary: schemas complete"
  out.flush : IO Unit)

set_option Classicism.Meta.Translate.profile true in
#classicism_derive Classicism.Research.CoalescedCH.normal_form

#eval (do
  let out ← IO.getStdout
  out.putStrLn "CH vocabulary: normal-form translation complete"
  out.flush : IO Unit)

#print axioms Classicism.Research.CoalescedCH.HasRealCH.reflect
#print axioms Classicism.Research.CoalescedCH.HasRealNotCH.reflect
#print axioms Classicism.Research.CoalescedCH.NonContingency.reflect
#print axioms Classicism.Research.CoalescedCH.normal_form.derivable
