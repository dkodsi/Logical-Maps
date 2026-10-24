import Classicism.Results.Research.AtomicProbabilityCutArithmetic
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

#classicism_audit Classicism.Results.Research.AtomicProbabilityCutArithmetic
#classicism_types_audit Classicism.Results.Research.AtomicProbabilityCutArithmetic

#classicism_derive Classicism.Research.ProbabilityCuts.principal_is_cut
  Classicism.Research.ProbabilityCuts.cut_member_below_nonmember
  Classicism.Research.ProbabilityCuts.cut_principal_upper_bound
  Classicism.Research.ProbabilityCuts.cuts_comparable
  Classicism.Research.ProbabilityCuts.principal_injective_coextension
  Classicism.Research.ProbabilityCuts.codeAdd_strict_both
  Classicism.Research.ProbabilityCuts.cutAdd_is_cut
  Classicism.Research.ProbabilityCuts.codeAdd_below_split
  Classicism.Research.ProbabilityCuts.principalCut_add
  Classicism.Research.ProbabilityCuts.cutAdd_zero

#print axioms Classicism.Research.ProbabilityCuts.cuts_comparable.derivable
#print axioms Classicism.Research.ProbabilityCuts.cutAdd_is_cut.derivable
#print axioms Classicism.Research.ProbabilityCuts.principalCut_add.derivable
#print axioms Classicism.Research.ProbabilityCuts.cutAdd_zero.derivable
