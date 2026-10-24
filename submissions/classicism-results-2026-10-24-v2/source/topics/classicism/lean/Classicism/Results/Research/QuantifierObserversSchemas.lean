import Classicism.Results.Research.QuantifierObserversCertificates
import Classicism.Certified.Signatures

/-!
# Quantifier-observer characterizations as sentence schemas

Direct source: operator-separation-new-results.txt, section 2, Theorem 2
(misc, original research, 23 October 2026, unpaginated).

Type quantification here is metalinguistic. Each schema consists of the
individual fixed-type sentences. The theorem does not replace finite
conjunctions of qualifications by an infinitary object-language condition.
-/

#classicism_schema Classicism.Research.QuantifierObservers.Separation
  Classicism.Research.QuantifierObservers.WeakSeparation

#classicism_certify Classicism.Research.QuantifierObservers.barcan_separation
  Classicism.Research.QuantifierObservers.separation_barcan
  Classicism.Research.QuantifierObservers.barcan_weak_separation
  Classicism.Research.QuantifierObservers.weak_separation_barcan

#classicism_entails Classicism.Research.QuantifierObservers.barcan_separation
  Classicism.Research.QuantifierObservers.separation_barcan
  Classicism.Research.QuantifierObservers.barcan_weak_separation
  Classicism.Research.QuantifierObservers.weak_separation_barcan

namespace Classicism.Meta.Research.QuantifierObservers
open AxiomSet Classicism.Research.QuantifierObservers

theorem separation_iff_barcan_schema (Ax : AxiomSet Signature.pure) :
    (Ax ⟹ Separation.schema) ↔ (Ax ⟹ P.Barcan.schema) :=
  ⟨fun h => Entails.trans h separation_barcan.entails,
    fun h => Entails.trans h barcan_separation.entails⟩

theorem weak_separation_iff_barcan_schema (Ax : AxiomSet Signature.pure) :
    (Ax ⟹ WeakSeparation.schema) ↔ (Ax ⟹ P.Barcan.schema) :=
  ⟨fun h => Entails.trans h weak_separation_barcan.entails,
    fun h => Entails.trans h barcan_weak_separation.entails⟩

private theorem transport {Sig : Signature} {A B : AxiomSet Signature.pure}
    (h : A ⟹ B) : AxiomSet.ofPure (Sig := Sig) A ⟹ AxiomSet.ofPure B := by
  rintro a ⟨p, hp, rfl⟩
  exact Derivable.mono (ofPure_union_subset A) (Theorem.ofPure (h p hp))

abbrev SeparationIn {Sig : Signature} : AxiomSet Sig :=
  AxiomSet.ofPure Separation.schema

abbrev WeakSeparationIn {Sig : Signature} : AxiomSet Sig :=
  AxiomSet.ofPure WeakSeparation.schema

theorem separation_iff_barcan_in {Sig : Signature} (Ax : AxiomSet Sig) :
    (Ax ⟹ SeparationIn) ↔ (Ax ⟹ P.Barcan.schemaIn) :=
  ⟨fun h => Entails.trans h (transport separation_barcan.entails),
    fun h => Entails.trans h (transport barcan_separation.entails)⟩

theorem weak_separation_iff_barcan_in {Sig : Signature} (Ax : AxiomSet Sig) :
    (Ax ⟹ WeakSeparationIn) ↔ (Ax ⟹ P.Barcan.schemaIn) :=
  ⟨fun h => Entails.trans h (transport weak_separation_barcan.entails),
    fun h => Entails.trans h (transport barcan_weak_separation.entails)⟩

end Classicism.Meta.Research.QuantifierObservers

#print axioms Classicism.Meta.Research.QuantifierObservers.separation_iff_barcan_in
#print axioms Classicism.Meta.Research.QuantifierObservers.weak_separation_iff_barcan_in
