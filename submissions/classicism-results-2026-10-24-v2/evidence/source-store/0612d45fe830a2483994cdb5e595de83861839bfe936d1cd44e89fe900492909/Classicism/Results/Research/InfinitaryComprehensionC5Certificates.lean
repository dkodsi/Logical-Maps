import Classicism.Results.Records.C5
import Classicism.Certified.Schemas

/-!
# The two existing C5-to-Barcan certificates used by the infinitary bridge

This selective certificate support translates precisely the existing proofs
in `Classicism.Results.Records.C5`. It retains their canonical generated names,
closed-type schema interpretation, and object-language derivation assumptions.
No new mathematical premise or theorem is introduced. The bridge needs these
two arrows; compiling every record in `Certified.Derivations` is unnecessary.
-/

#classicism_derive
  Classicism.Proofs.necessary_nd_implies_bf
  Classicism.Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r

#classicism_entails
  Classicism.Proofs.necessary_nd_implies_bf
  Classicism.Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r

#print axioms Classicism.Proofs.necessary_nd_implies_bf.entails
#print axioms Classicism.Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r.entails
