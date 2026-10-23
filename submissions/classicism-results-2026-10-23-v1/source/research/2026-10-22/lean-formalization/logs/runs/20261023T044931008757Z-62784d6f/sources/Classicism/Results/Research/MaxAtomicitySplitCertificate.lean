import Classicism.Results.Research.BoundedSplitter
import Classicism.Results.Research.MaxAtomicityReduction

/-!
# The object-language splitter obstruction to unboxed Atomicity

Direct sources: `research/2026-10-22/followup/max-atomicity-rigid-selector.md`,
§1, and `max-atomicity-selector-audit.md`, §§8–9.

For each closed pure term `F : t → t`, this module defines the finite pure sentence

    split(F) := ∀p. p ≠ ⊥ → ((p ∧ Fp) ≠ ⊥ ∧ (p ∧ ¬Fp) ≠ ⊥)

and derives its identity with bottom from the actual unboxed Atomicity schema.
The derivation instantiates `BoundedSplitter.atomicity_guard_zero.derivable`;
the zero-identity derivation is not a hypothesis. A single elementary C identity
removes the bound `⊤` and the outer conjunction with `⊤`.

The final inconsistency theorem is CONDITIONAL on non-theoremhood of this exact
identity. This module does not construct a rigid Boolean algebra, a coded order,
a selector, or a separating interpretation. In particular no semantic premise
is used to obtain the positive identity under Atomicity.

Compilation and axiom auditing are pending the designated serial checker.
-/

namespace Classicism.Research.MaxAtomicitySplitCertificate

open Classicism.Paper

/-- A closed Logical Equivalence instance removes the tautological bound.
Only the term parameter `F`, and no proper axiom or proof hypothesis, occurs
free in the proof passed to `propext`. -/
theorem guard_eq_split (F : Prop → Prop) :
    (True ∧ BoundedSplitter.Split True F) =
      (∀ p : Prop, p ≠ False →
        ((p ∧ F p) ≠ False ∧ (p ∧ ¬ F p) ≠ False)) :=
  propext
    ⟨fun h p hp => h.2 p ⟨hp, le_top_prop p⟩,
      fun h => ⟨True.intro, fun p hp => h p hp.1⟩⟩

end Classicism.Research.MaxAtomicitySplitCertificate

#classicism_check Classicism.Research.MaxAtomicitySplitCertificate.guard_eq_split
#classicism_types Classicism.Research.MaxAtomicitySplitCertificate.guard_eq_split
#classicism_derive Classicism.Research.MaxAtomicitySplitCertificate.guard_eq_split

namespace Classicism.Meta.Research.MaxAtomicitySplitCertificate

open AxiomSet

abbrev SplitterTy : RTy := Ty.t ⇒ RTy.t

/-- Both Boolean parts of `p` determined by `F p` are nonzero. -/
def splitParts {Γ : Ctx} (p : Formula Signature.pure Γ)
    (F : Term Signature.pure Γ SplitterTy) : Formula Signature.pure Γ :=
  Term.conj
    (Term.neg (Term.eq' (Term.conj p (.app F p)) Term.bot))
    (Term.neg (Term.eq' (Term.conj p (Term.neg (.app F p))) Term.bot))

/-- The exact global splitter sentence; the context-polymorphic definition
also permits its use under the quantifier in the imported certificate. -/
def split {Γ : Ctx} (F : Term Signature.pure Γ SplitterTy) :
    Formula Signature.pure Γ :=
  Term.forall' (σ := Ty.t)
    (Term.imp (Term.neg (Term.eq' Term.v0 Term.bot))
      (splitParts Term.v0 F.weaken))

/-- The bounded assertion in the existing certificate. At type t the order
`p ≤ b` is precisely the identity `b = p ∨ b`. -/
def boundedSplit {Γ : Ctx} (b : Formula Signature.pure Γ)
    (F : Term Signature.pure Γ SplitterTy) : Formula Signature.pure Γ :=
  Term.forall' (σ := Ty.t)
    (Term.imp
      (Term.conj
        (Term.neg (Term.eq' Term.v0 Term.bot))
        (Term.eq' b.weaken (Term.disj Term.v0 b.weaken)))
      (splitParts Term.v0 F.weaken))

def guard {Γ : Ctx} (b : Formula Signature.pure Γ)
    (F : Term Signature.pure Γ SplitterTy) : Formula Signature.pure Γ :=
  Term.conj b (boundedSplit b F)

/-- No type variable is introduced by the splitter sentence. The empty term
context already ensures closure in object variables; this additional hypothesis
ensures that every type appearing inside the arbitrary term `F` is closed. -/
theorem split_closedTypes (F : Term Signature.pure [] SplitterTy)
    (hF : F.closedTypes = true) : (split F).closedTypes = true := by
  simp [split, splitParts, Term.closedTypes, Term.weaken,
    Term.closedTypes_rename, hF]

/-- Purity follows from the empty nonlogical signature, without an axiom. -/
theorem split_pure (F : Term Signature.pure [] SplitterTy) :
    (split F).pure = true :=
  (split F).pure_of_pureSig

/-- The exact identity to which pure Max(C)'s distinctness clause applies. -/
theorem split_identity_closedTypes (F : Term Signature.pure [] SplitterTy)
    (hF : F.closedTypes = true) :
    (Term.eq' (split F) Term.bot).closedTypes = true := by
  simpa only [Term.closedTypes_eq', Term.closedTypes_bot, Bool.and_true]
    using split_closedTypes F hF

/-- C plus the actual unboxed Atomicity_t schema proves `split(F) = ⊥`.

The imported certificate has an Atomicity implication followed by the two
object quantifiers `∀b ∀F`. We discharge its antecedent with the schema axiom,
then instantiate both quantifiers simultaneously, at `⊤` and the specified
closed term `F`. This is UI and β-conversion, not an assumed obstruction.
The certificate may be recorded in C⁻ or C; both are included in C+Atomicity.
-/
theorem split_zero_under_atomicity (F : Term Signature.pure [] SplitterTy) :
    Theorem (C.axioms ∪ P.AtomicityT.schema) (Term.eq' (split F) Term.bot) := by
  have hbounded : Theorem (C.axioms ∪ P.AtomicityT.schema)
      (Term.imp P.AtomicityT.quoted
        (Term.forall' (σ := Ty.t)
          (Term.forall' (σ := SplitterTy)
            (Term.eq' (guard Term.v1 Term.v0) Term.bot)))) := by
    first
    | exact Theorem.ofCMinus
        Classicism.Research.BoundedSplitter.atomicity_guard_zero.derivable
    | exact Theorem.ofC
        Classicism.Research.BoundedSplitter.atomicity_guard_zero.derivable
  have hat : Theorem (C.axioms ∪ P.AtomicityT.schema) P.AtomicityT.quoted :=
    Theorem.ax rfl
  have hguard : Theorem (C.axioms ∪ P.AtomicityT.schema)
      (Term.eq' (guard Term.top F) Term.bot) :=
    Derivable.allE₂β (Theorem.mp hbounded hat) Term.top F
  have hbridge : Theorem (C.axioms ∪ P.AtomicityT.schema)
      (Term.forall' (σ := SplitterTy)
        (Term.eq' (guard Term.top Term.v0) (split Term.v0))) := by
    first
    | exact Theorem.ofCMinus
        Classicism.Research.MaxAtomicitySplitCertificate.guard_eq_split.derivable
    | exact Theorem.ofC
        Classicism.Research.MaxAtomicitySplitCertificate.guard_eq_split.derivable
  have hident : Theorem (C.axioms ∪ P.AtomicityT.schema)
      (Term.eq' (guard Term.top F) (split F)) :=
    Derivable.allEβ hbridge F
  exact Derivable.eqTrans (Derivable.eqSymm hident) hguard

/-- Supply the positive identity field from the derivation above. The only
remaining mathematical certificate is non-theoremhood of this exact identity.
This is a conditional constructor, not an assertion that a selector exists. -/
def separatorOfNonTheorem (F : Term Signature.pure [] SplitterTy)
    (hF : F.closedTypes = true)
    (hnot : ¬ C.Theorem (Term.eq' (split F) Term.bot)) :
    MaxAtomicityReduction.AtomicitySeparator where
  sentence := split F
  closedTypes := split_closedTypes F hF
  not_zero_theorem := hnot
  zero_under_atomicity := split_zero_under_atomicity F

/-- CONDITIONAL: a closed pure splitter term with this non-theorem certificate
makes Max(C)+Atomicity_t inconsistent. The reference theory in `hnot` is bare C;
the argument does not replace it by C+Atomicity or by an enriched language. -/
theorem inconsistent_of_split_not_zero_theorem
    (F : Term Signature.pure [] SplitterTy) (hF : F.closedTypes = true)
    (hnot : ¬ C.Theorem (Term.eq' (split F) Term.bot)) :
    ¬ Consistent (maximalist ∪ P.AtomicityT.schema) :=
  (separatorOfNonTheorem F hF hnot).inconsistent

end Classicism.Meta.Research.MaxAtomicitySplitCertificate

#print axioms Classicism.Research.MaxAtomicitySplitCertificate.guard_eq_split.derivable
#print axioms Classicism.Meta.Research.MaxAtomicitySplitCertificate.split_closedTypes
#print axioms Classicism.Meta.Research.MaxAtomicitySplitCertificate.split_pure
#print axioms Classicism.Meta.Research.MaxAtomicitySplitCertificate.split_zero_under_atomicity
#print axioms Classicism.Meta.Research.MaxAtomicitySplitCertificate.separatorOfNonTheorem
#print axioms Classicism.Meta.Research.MaxAtomicitySplitCertificate.inconsistent_of_split_not_zero_theorem
