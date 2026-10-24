import Classicism.Results.Research.ChoiceCodeTowers
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-!
Direct source: `continuation-code-operations.md`, §§1–2 (`misc`, 23 October 2026;
unpaginated). Main tuple targets cover every relational source type, including
the nullary proposition type. Chooser outputs retain the unrestricted `Ty` scope.
No record verification status is set by this standalone research module.
-/

#classicism_audit Classicism.Results.Research.ChoiceCodeTowers
#classicism_types_audit Classicism.Results.Research.ChoiceCodeTowers
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.ChoiceCodeTowers

#classicism_schema Classicism.Research.ChoiceCodeTowers.ClassCodeSplit
  Classicism.Research.ChoiceCodeTowers.ClassCodeAmbiguity
#classicism_certify Classicism.Research.ChoiceCodeTowers.class_code_split
  Classicism.Research.ChoiceCodeTowers.class_code_ambiguity

#check Classicism.Research.ChoiceCodeTowers.class_code_split.listRule
#check Classicism.Research.ChoiceCodeTowers.class_code_ambiguity.listRule
#print axioms Classicism.Research.ChoiceCodeTowers.class_code_split.listRule
#print axioms Classicism.Research.ChoiceCodeTowers.class_code_ambiguity.listRule
#print axioms Classicism.Research.ChoiceCodeTowers.codeSplit_comp.derivable
#print axioms Classicism.Research.ChoiceCodeTowers.codeSplit_ambiguity.derivable
#print axioms Classicism.Research.ChoiceCodeTowers.class_code_split_t.derivable
#print axioms Classicism.Research.ChoiceCodeTowers.class_code_ambiguity_t.derivable
