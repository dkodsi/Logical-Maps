import Classicism.Results.Research.FullLogicalObserversFiniteQualificationCertificates
import Classicism.Syntax.Entailment
import Classicism.Syntax.Vectorize
import Classicism.Syntax.Normalize

set_option Elab.async false
set_option stderrAsMessages false

/-!
# Simultaneous full logical separation for arbitrary finite type lists

Direct source: `research/2026-10-23/operator-characterizations/positive-operator-representation.txt`,
sections 1--3, especially display (B) (misc, original research, 23 October 2026,
unpaginated).

Delta is a metalogical list of object types. The object-language predicate
`qualification Delta` is the conjunction of all of its full quantifier
qualifications. There is one quantified observer, satisfying every conjunct.
This is not the vectorized list form of a single quantifier qualification.

All derivations below are assembled from the gated shallow constructions.
The recursion combines qualifications of the same `PatchedPrincipal a`.
It assumes no extraction, separation, or representation lemma as a meta axiom.
The necessary version uses the separately translated boxed combinators.
-/

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: imports complete"
  err.flush : IO Unit)

abbrev OperatorType : RTy := .arr (.rel .t) .t
abbrev QualificationType : RTy := .arr (.rel OperatorType) .t

/-- A single object predicate requiring every listed quantifier identity. -/
noncomputable def qualification : List Ty → Term Signature.pure [] QualificationType
  | [] => TrueQualification.term
  | σ :: Δ => .app (.app ConjoinQualification.term (QuantifierCondition.term σ))
      (qualification Δ)

noncomputable def qualifiedAtoms (Δ : List Ty) : Sentence Signature.pure :=
  .app AtomQualification.term (qualification Δ)

noncomputable def separation (Δ : List Ty) : Sentence Signature.pure :=
  .app SeparationCondition.term (qualification Δ)

noncomputable def necessarySeparation (Δ : List Ty) : Sentence Signature.pure :=
  Term.box (separation Δ)

def FullFiniteSchema : AxiomSet Signature.pure :=
  fun p => ∃ Δ : List Ty, Ty.AllClosed Δ ∧ p = separation Δ

def NecessaryFullFiniteSchema : AxiomSet Signature.pure :=
  fun p => ∃ Δ : List Ty, Ty.AllClosed Δ ∧ p = necessarySeparation Δ

def Background : AxiomSet Signature.pure :=
  single C5Condition.term ∪ single ActualCondition.term

-- The quoter already unfolds definitions and head-beta-reduces applications.
-- Here only the explicit qualification, conjunction/quantifier and observer
-- application layers remain. Use four parallel passes instead of repeatedly
-- traversing the large quoted formulas and symbolic list tails 32 times.
-- Conv.of_nf does not require a complete normal form: rfl still checks exact
-- equality after these passes, so insufficient fuel cannot certify a conversion.
-- Retain finite local elaboration budgets; the markers locate any next failure.

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
