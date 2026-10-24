import Classicism.Results.Research.AtomicProbabilityCutNegation
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

#classicism_audit Classicism.Results.Research.AtomicProbabilityCutNegation
#classicism_types_audit Classicism.Results.Research.AtomicProbabilityCutNegation

#classicism_derive Classicism.Research.ProbabilityCuts.cutNeg_is_cut
  Classicism.Research.ProbabilityCuts.cutNeg_antitone
  Classicism.Research.ProbabilityCuts.cutNeg_involutive
  Classicism.Research.ProbabilityCuts.cutAdd_neg_below_zero

#print axioms Classicism.Research.ProbabilityCuts.cutNeg_is_cut.derivable
#print axioms Classicism.Research.ProbabilityCuts.cutNeg_involutive.derivable
#print axioms Classicism.Research.ProbabilityCuts.cutAdd_neg_below_zero.derivable
