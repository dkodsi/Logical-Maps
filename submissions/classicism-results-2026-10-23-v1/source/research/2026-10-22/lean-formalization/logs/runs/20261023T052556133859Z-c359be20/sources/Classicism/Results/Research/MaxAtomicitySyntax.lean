import Classicism.Syntax.SentenceSchemas

/-!
# Finite pure syntax for the universe-code predicate

Direct source: `research/2026-10-22/followup/max-atomicity-selector-audit.md`, §2.
These are terms of the actual object language, not shallow Lean predicates.
The propositions about their syntax are metalogical. No Mostowski, cardinality,
rigidity, soundness, or Max/Atomicity incompatibility theorem is asserted here.
Compilation and axiom reports are pending the designated serial build owner.
-/

namespace Classicism.Meta.Research.MaxAtomicitySyntax

abbrev U : RTy := Ty.t ⇒ RTy.t
abbrev UP : RTy := (U : Ty) ⇒ RTy.t
abbrev ER : RTy := (U : Ty) ⇒ (U : Ty) ⇒ RTy.t

abbrev PT (Γ : Ctx) (σ : Ty) := Term Signature.pure Γ σ

/-- Explicit left-nested application of the coded membership relation. -/
def member {Γ : Ctx} (E : PT Γ ER) (x y : PT Γ U) : Formula Signature.pure Γ :=
  .app (.app E x) y

/-- A subset predicate has only the literal proposition values bottom and top. -/
def crisp {Γ : Ctx} (X : PT Γ UP) : Formula Signature.pure Γ :=
  Term.forall' (σ := U)
    (Term.disj
      (Term.eq' (.app X.weaken Term.v0) Term.bot)
      (Term.eq' (.app X.weaken Term.v0) Term.top))

/-- Injection of the extension of X into the proposition domain.
The witness f is NOT required to be crisp. -/
def small {Γ : Ctx} (X : PT Γ UP) : Formula Signature.pure Γ :=
  Term.exists' (σ := UP) (Term.forall' (σ := U) (Term.forall' (σ := U)
    (Term.imp
      (Term.conj
        (Term.conj (.app X.weaken.weaken.weaken Term.v1)
          (.app X.weaken.weaken.weaken Term.v0))
        (Term.eq' (.app Term.v2 Term.v1) (.app Term.v2 Term.v0)))
      (Term.eq' Term.v1 Term.v0))))

def crispRelation {Γ : Ctx} (E : PT Γ ER) : Formula Signature.pure Γ :=
  Term.forall' (σ := U) (Term.forall' (σ := U)
    (Term.disj
      (Term.eq' (member E.weaken.weaken Term.v1 Term.v0) Term.bot)
      (Term.eq' (member E.weaken.weaken Term.v1 Term.v0) Term.top)))

def extensional {Γ : Ctx} (E : PT Γ ER) : Formula Signature.pure Γ :=
  Term.forall' (σ := U) (Term.forall' (σ := U)
    (Term.imp
      (Term.forall' (σ := U)
        (Term.iff (member E.weaken.weaken.weaken Term.v0 Term.v2)
          (member E.weaken.weaken.weaken Term.v0 Term.v1)))
      (Term.eq' Term.v1 Term.v0)))

/-- Full well-foundedness only in a full interpretation; syntactically the
subset quantifier is restricted by Crisp exactly as in the research note. -/
def wellFounded {Γ : Ctx} (E : PT Γ ER) : Formula Signature.pure Γ :=
  Term.forall' (σ := UP)
    (Term.imp
      (Term.conj (crisp Term.v0)
        (Term.exists' (σ := U) (.app Term.v1 Term.v0)))
      (Term.exists' (σ := U)
        (Term.conj (.app Term.v1 Term.v0)
          (Term.forall' (σ := U)
            (Term.imp (member E.weaken.weaken.weaken Term.v0 Term.v1)
              (Term.neg (.app Term.v2 Term.v0)))))))

def fill {Γ : Ctx} (E : PT Γ ER) : Formula Signature.pure Γ :=
  Term.forall' (σ := UP)
    (Term.imp (Term.conj (crisp Term.v0) (small Term.v0))
      (Term.exists' (σ := U) (Term.forall' (σ := U)
        (Term.eq' (member E.weaken.weaken.weaken Term.v0 Term.v1)
          (.app Term.v2 Term.v0)))))

def cover {Γ : Ctx} (E : PT Γ ER) : Formula Signature.pure Γ :=
  Term.conj (crispRelation E)
    (Term.conj (extensional E) (Term.conj (wellFounded E) (fill E)))

/-- One closed pure term of type (U → U → t) → t. -/
def coverCode : Term Signature.pure [] ((ER : Ty) ⇒ RTy.t) :=
  .lam (cover Term.v0)

theorem coverCode_closedTypes : coverCode.closedTypes = true := rfl

theorem coverCode_pure : coverCode.pure = true := coverCode.pure_of_pureSig

end Classicism.Meta.Research.MaxAtomicitySyntax

#print axioms Classicism.Meta.Research.MaxAtomicitySyntax.coverCode_closedTypes
#print axioms Classicism.Meta.Research.MaxAtomicitySyntax.coverCode_pure
