import Classicism.Results.Research.AtomicProbabilityCutAddition
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-!
Requested C-language checks for the logical cut infrastructure only.
Conditional extensional-code premises remain premises in the translated proofs.
This does not certify the external algebra modules or the real-field interpretation.
-/

#classicism_audit Classicism.Results.Research.AtomicProbabilityCuts
  Classicism.Results.Research.AtomicProbabilityCutAddition
#classicism_types_audit Classicism.Results.Research.AtomicProbabilityCuts
  Classicism.Results.Research.AtomicProbabilityCutAddition

#classicism_derive Classicism.Research.ProbabilityCuts.union_is_lub
  Classicism.Research.ProbabilityCuts.union_is_cut
  Classicism.Research.ProbabilityCuts.cut_sup_exists
  Classicism.Research.ProbabilityCuts.lub_unique_coextension
  Classicism.Research.ProbabilityCuts.lowerCut_transport
  Classicism.Research.ProbabilityCuts.lub_transport
  Classicism.Research.ProbabilityCuts.coded_sup_unique
  Classicism.Research.ProbabilityCuts.coded_sup_exists
  Classicism.Research.ProbabilityCuts.coded_sup_graph_total_functional
  Classicism.Research.ProbabilityCuts.cutAdd_mono
  Classicism.Research.ProbabilityCuts.cutAdd_transport
  Classicism.Research.ProbabilityCuts.cutAdd_union_left
  Classicism.Research.ProbabilityCuts.cutAdd_union_right
  Classicism.Research.ProbabilityCuts.cutAdd_comm
  Classicism.Research.ProbabilityCuts.cutAdd_assoc

#print axioms Classicism.Research.ProbabilityCuts.cut_sup_exists.derivable
#print axioms Classicism.Research.ProbabilityCuts.coded_sup_graph_total_functional.derivable
#print axioms Classicism.Research.ProbabilityCuts.cutAdd_union_left.derivable
#print axioms Classicism.Research.ProbabilityCuts.cutAdd_assoc.derivable
