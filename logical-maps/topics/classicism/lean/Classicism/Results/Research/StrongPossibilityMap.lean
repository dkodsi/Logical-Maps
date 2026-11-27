import Classicism.StrongPossibility.ArbitrarySignatureLicences
import Classicism.StrongPossibility.Predecessor
import Classicism.StrongPossibility.ProxyCanonical
import Classicism.Statements

/-! The private predecessor supplies the term-separation theorem at both
individual-marker signatures. Their descriptor roots license incompatible
returns in the original language. -/

namespace Classicism.Meta.StrongPossibilityMap

open ProxyDiagonal

/-- No theory in the pure language can consistently assert all the instances of SP. -/
theorem pure_inconsistent : ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Signature.pure) :=
  pure_from_predecessors (predecessors _) (predecessors _)

/-- Strong Possibility (pure) implies a contradiction in any admitted ambient signature. -/
theorem strong_possibility_r_inconsistent : Classicism.Statements.strong_possibility_r_inconsistent := by
  intro Sig _ Ax ent cons
  exact AxiomSet.not_consistent_ofPure pure_inconsistent (AxiomSet.Consistent.of_entails ent cons)

/-- The two-colour argument for a countable closed signature with a public individual
name and a public relation name. -/
theorem named_inconsistent {Sig : Signature} [Countable Sig.Const] (hS : Sig.Closed)
    (hn : Nonempty (Coalesced.DistinguishedDefinable.names (Sig := Sig) .e))
    (c : Sig.Const) {ρ : RTy} (hc : Sig.typeOf c = .rel ρ) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) :=
  named_from_predecessors hS hn (predecessors Sig) c hc

/-- Lift uniform object-theory inconsistency to the generated signature map statement. -/
theorem signature_map_of_inconsistent
    (h : ∀ {Sig : Signature}, Sig.Admitted → ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig)) :
    Classicism.Statements.strong_possibility_signature_r_inconsistent := by
  intro Sig adm Ax ent cons
  exact h adm (AxiomSet.Consistent.of_entails ent cons)

/-- The signature-level map statement, including signatures of arbitrary cardinality
and signatures without a public individual name. -/
theorem strong_possibility_signature_r_inconsistent :
    Classicism.Statements.strong_possibility_signature_r_inconsistent :=
  signature_map_of_inconsistent (fun hs => inconsistent_in_admitted_signature hs)

end Classicism.Meta.StrongPossibilityMap
