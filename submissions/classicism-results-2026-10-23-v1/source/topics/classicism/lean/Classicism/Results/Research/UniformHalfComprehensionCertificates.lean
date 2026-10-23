import Classicism.Results.Research.UniformHalfComprehension
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-!
Gate, relational-type audit, and object-language C derivations for the uniform
half-comprehension family. This is a research certificate, not a YAML/map status edit.
Source proofs and scope: the two imported research modules' docstrings.
-/

#classicism_audit Classicism.Results.Research.Evaluator
  Classicism.Results.Research.UniformHalfComprehension
#classicism_types_audit Classicism.Results.Research.Evaluator
  Classicism.Results.Research.UniformHalfComprehension

#classicism_schema Classicism.P.Existence

#classicism_derive Classicism.Research.positiveEvaluator_actualWorld
  Classicism.Research.actualEvaluator_positive
  Classicism.Research.actualWorld_unique
  Classicism.Research.actualWorld_all
  Classicism.Research.empty_weaklyInextensible

#classicism_certify Classicism.Research.positiveEvaluator_actuality
  Classicism.Research.actuality_positiveEvaluator
  Classicism.Research.uniformPersistent_weak
  Classicism.Research.uniformInextensible_weak
  Classicism.Research.actuality_uniformPersistent
  Classicism.Research.actuality_uniformWeakPersistent
  Classicism.Research.actuality_uniformWeakInextensible
  Classicism.Research.uniformWeakPersistent_actuality
  Classicism.Research.uniformPersistent_actuality
  Classicism.Research.uniformWeakInextensible_actuality
  Classicism.Research.uniformInextensible_actuality
  Classicism.Research.actuality_uniformPersistent_t
  Classicism.Research.actuality_uniformWeakInextensible_t
  Classicism.Research.uniformWeakPersistent_actuality_t
  Classicism.Research.uniformWeakInextensible_actuality_t

#print axioms Classicism.Research.positiveEvaluator_actualWorld.derivable
#print axioms Classicism.Research.actualWorld_all.derivable
#print axioms Classicism.Research.actuality_uniformPersistent.rule
#print axioms Classicism.Research.uniformWeakInextensible_actuality.rule
