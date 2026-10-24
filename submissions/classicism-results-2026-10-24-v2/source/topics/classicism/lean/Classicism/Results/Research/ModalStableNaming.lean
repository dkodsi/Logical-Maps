import Init

/-!
# Guarded conservativity for a stable, globally necessitable definition

This is an independent syntactic metatheorem, not a theorem in `C.Derivable`.
The object language has primitive implication, box, and quantifier binders.
There is no object-language lambda or choice operator. Necessitation applies
only to an inductively supplied theorem derivation; there is no local-context
necessitation rule.

The main theorem transforms a proof after adjoining the global axiom `D`
into a base proof of `D → A`, provided the base proves `D → □D` and every
variable generalized in the extended proof is fresh in `D`. The subsequent
existential elimination uses explicit syntactic freshness of the parameter
in the conclusion. No conservativity statement is an input field.

Atoms and their free-variable relation are parameters. Connecting these
atoms to a particular typed applicative term syntax, and verifying the
fresh-constant replacement map, are separate integration obligations.
`Derivation.map` supplies the proof-preservation induction for that map.
-/

namespace Classicism.Research.ModalStableNaming

universe u v u' v'

inductive Formula (Atom : Type u) (Var : Type v) : Type (max u v) where
  | atom : Atom → Formula Atom Var
  | imp : Formula Atom Var → Formula Atom Var → Formula Atom Var
  | box : Formula Atom Var → Formula Atom Var
  | all : Var → Formula Atom Var → Formula Atom Var
  | ex : Var → Formula Atom Var → Formula Atom Var

namespace Formula

variable {Atom : Type u} {Var : Type v}
  {Atom' : Type u'} {Var' : Type v'}

/-- Syntactic freshness, with the atom-level support relation explicit. -/
def Fresh (occurs : Var → Atom → Prop) (x : Var) : Formula Atom Var → Prop
  | atom a => ¬ occurs x a
  | imp p q => Fresh occurs x p ∧ Fresh occurs x q
  | box p => Fresh occurs x p
  | all y p => x = y ∨ Fresh occurs x p
  | ex y p => x = y ∨ Fresh occurs x p

/-- Uniform translation of primitive constructors, atoms, and binder names. -/
def map (atomMap : Atom → Atom') (varMap : Var → Var') :
    Formula Atom Var → Formula Atom' Var'
  | atom a => atom (atomMap a)
  | imp p q => imp (map atomMap varMap p) (map atomMap varMap q)
  | box p => box (map atomMap varMap p)
  | all x p => all (varMap x) (map atomMap varMap p)
  | ex x p => ex (varMap x) (map atomMap varMap p)

/-- One sufficient condition for a relabeling to preserve freshness. -/
theorem fresh_map
    {occurs : Var → Atom → Prop} {occurs' : Var' → Atom' → Prop}
    (atomMap : Atom → Atom') (varMap : Var → Var')
    (support : ∀ x a, occurs' (varMap x) (atomMap a) → occurs x a)
    {x : Var} {p : Formula Atom Var} (hp : Fresh occurs x p) :
    Fresh occurs' (varMap x) (map atomMap varMap p) := by
  induction p with
  | atom a => exact fun h => hp (support x a h)
  | imp p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | box p ih => exact ih hp
  | all y p ih =>
      rcases hp with h | h
      · exact Or.inl (congrArg varMap h)
      · exact Or.inr (ih h)
  | ex y p ih =>
      rcases hp with h | h
      · exact Or.inl (congrArg varMap h)
      · exact Or.inr (ih h)

end Formula

open Formula

variable {Atom : Type u} {Var : Type v}

/-- Only the logical axiom instances needed by the proof transformation.
Additional logical or nonlogical axioms may be supplied through `Ax`.
Both quantifier axioms have their ordinary explicit freshness conditions. -/
inductive LogicalAxiom (occurs : Var → Atom → Prop) : Formula Atom Var → Prop where
  | propK (p q) : LogicalAxiom occurs (imp p (imp q p))
  | propS (p q r) : LogicalAxiom occurs
      (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  | modalK (p q) : LogicalAxiom occurs
      (imp (box (imp p q)) (imp (box p) (box q)))
  | allGuard (x p q) (fresh : Fresh occurs x p) : LogicalAxiom occurs
      (imp (all x (imp p q)) (imp p (all x q)))
  | existsElim (x p q) (fresh : Fresh occurs x q) : LogicalAxiom occurs
      (imp (all x (imp p q)) (imp (ex x p) q))

/-- Global theorem derivations. `allowed` records which variables a proof
may generalize; all derivation premises are theorem derivations, including
the premise of `nec`. There are no open local assumptions in this type. -/
inductive Derivation (occurs : Var → Atom → Prop)
    (Ax : Formula Atom Var → Prop) (allowed : Var → Prop) :
    Formula Atom Var → Prop where
  | logical {p} : LogicalAxiom occurs p → Derivation occurs Ax allowed p
  | theory {p} : Ax p → Derivation occurs Ax allowed p
  | mp {p q} : Derivation occurs Ax allowed (imp p q) →
      Derivation occurs Ax allowed p → Derivation occurs Ax allowed q
  | nec {p} : Derivation occurs Ax allowed p →
      Derivation occurs Ax allowed (box p)
  | gen {x p} : allowed x → Derivation occurs Ax allowed p →
      Derivation occurs Ax allowed (all x p)

/-- The base system permits generalization on every variable. -/
abbrev Theorem (occurs : Var → Atom → Prop) (Ax : Formula Atom Var → Prop)
    (p : Formula Atom Var) : Prop := Derivation occurs Ax (fun _ => True) p

/-- Adjoining a global axiom, which is eligible for theorem necessitation. -/
def adjoin (Ax : Formula Atom Var → Prop) (D : Formula Atom Var) :
    Formula Atom Var → Prop := fun p => Ax p ∨ p = D

namespace Derivation

variable {occurs : Var → Atom → Prop} {Ax : Formula Atom Var → Prop}
  {allowed : Var → Prop}

theorem imp_self (p : Formula Atom Var) :
    Derivation occurs Ax allowed (imp p p) := by
  have h₁ : Derivation occurs Ax allowed (imp p (imp (imp p p) p)) :=
    .logical (.propK p (imp p p))
  have h₂ : Derivation occurs Ax allowed (imp p (imp p p)) :=
    .logical (.propK p p)
  exact .mp (.mp (.logical (.propS p (imp p p) p)) h₁) h₂

theorem weaken {p : Formula Atom Var} (hp : Derivation occurs Ax allowed p)
    (q : Formula Atom Var) : Derivation occurs Ax allowed (imp q p) :=
  .mp (.logical (.propK p q)) hp

theorem imp_trans {p q r : Formula Atom Var}
    (hpq : Derivation occurs Ax allowed (imp p q))
    (hqr : Derivation occurs Ax allowed (imp q r)) :
    Derivation occurs Ax allowed (imp p r) :=
  .mp (.mp (.logical (.propS p q r)) (weaken hqr p)) hpq

/-- Proof preservation is proved by induction, not assumed. A later
fresh-constant replacement must supply the atom translation, its logical
axiom-instance verification, its theory-axiom map and its generalization
side conditions. The logical map may target derived theorems. -/
theorem map
    {Atom' : Type u'} {Var' : Type v'}
    {occurs' : Var' → Atom' → Prop} {Ax' : Formula Atom' Var' → Prop}
    {allowed' : Var' → Prop}
    (atomMap : Atom → Atom') (varMap : Var → Var')
    (logicalMap : ∀ p, LogicalAxiom occurs p →
      Derivation occurs' Ax' allowed' (Formula.map atomMap varMap p))
    (axiomMap : ∀ p, Ax p →
      Derivation occurs' Ax' allowed' (Formula.map atomMap varMap p))
    (allowedMap : ∀ x, allowed x → allowed' (varMap x))
    {p : Formula Atom Var} (hp : Derivation occurs Ax allowed p) :
    Derivation occurs' Ax' allowed' (Formula.map atomMap varMap p) := by
  induction hp with
  | logical h => exact logicalMap _ h
  | theory h => exact axiomMap _ h
  | mp _ _ ihpq ihp => exact .mp ihpq ihp
  | nec _ ih => exact .nec ih
  | gen hx _ ih => exact .gen (allowedMap _ hx) ih

end Derivation

namespace LogicalAxiom

/-- Freshness preservation suffices to check all logical axiom instances
of a constructor-preserving relabeling. -/
theorem map
    {Atom' : Type u'} {Var' : Type v'}
    {occurs : Var → Atom → Prop} {occurs' : Var' → Atom' → Prop}
    (atomMap : Atom → Atom') (varMap : Var → Var')
    (freshMap : ∀ x p, Fresh occurs x p →
      Fresh occurs' (varMap x) (Formula.map atomMap varMap p))
    {p : Formula Atom Var} (hp : LogicalAxiom occurs p) :
    LogicalAxiom occurs' (Formula.map atomMap varMap p) := by
  cases hp with
  | propK p q => exact .propK _ _
  | propS p q r => exact .propS _ _ _
  | modalK p q => exact .modalK _ _
  | allGuard x p q h => exact .allGuard _ _ _ (freshMap x p h)
  | existsElim x p q h => exact .existsElim _ _ _ (freshMap x q h)

end LogicalAxiom

/-- The stable-guard deduction transformation, including its critical
necessitation case. The freshness premise is only about variables allowed
in generalization steps; a fresh replacement parameter may occur in `D`. -/
theorem guarded_transform
    {occurs : Var → Atom → Prop} {Ax : Formula Atom Var → Prop}
    {allowed : Var → Prop} {D A : Formula Atom Var}
    (stable : Theorem occurs Ax (imp D (box D)))
    (fresh : ∀ x, allowed x → Fresh occurs x D)
    (proof : Derivation occurs (adjoin Ax D) allowed A) :
    Theorem occurs Ax (imp D A) := by
  induction proof with
  | logical h => exact Derivation.weaken (.logical h) D
  | theory h =>
      rcases h with h | h
      · exact Derivation.weaken (.theory h) D
      · cases h
        exact Derivation.imp_self _
  | mp _ _ ihpq ihp =>
      exact .mp (.mp (.logical (.propS _ _ _)) ihpq) ihp
  | nec _ ih =>
      have hbox := Derivation.mp (.logical (.modalK _ _)) (.nec ih)
      exact Derivation.imp_trans stable hbox
  | gen hx _ ih =>
      exact .mp (.logical (.allGuard _ _ _ (fresh _ hx))) (.gen True.intro ih)

/-- After replacing a new closed name by a fresh parameter `h`, a base
existence theorem eliminates the stable guard. Freshness of the conclusion
is explicitly required; the theorem does not assert a syntax-replacement
lemma for an unspecified applicative language. -/
theorem recover_of_exists_fresh
    {occurs : Var → Atom → Prop} {Ax : Formula Atom Var → Prop}
    {allowed : Var → Prop} {D A : Formula Atom Var} (h : Var)
    (stable : Theorem occurs Ax (imp D (box D)))
    (freshGuard : ∀ x, allowed x → Fresh occurs x D)
    (freshConclusion : Fresh occurs h A)
    (existsGuard : Theorem occurs Ax (ex h D))
    (proof : Derivation occurs (adjoin Ax D) allowed A) :
    Theorem occurs Ax A := by
  have guarded := guarded_transform stable freshGuard proof
  have universal : Theorem occurs Ax (all h (imp D A)) :=
    .gen True.intro guarded
  have conditional : Theorem occurs Ax (imp (ex h D) A) :=
    .mp (.logical (.existsElim h D A freshConclusion)) universal
  exact .mp conditional existsGuard

/-- The usual closed-name application: after replacement, the defining
guard can contain only the fresh parameter `h`, and the translated proof
does not generalize that parameter. This specializes the preceding result
without a generalization-policy abstraction at its call site. -/
theorem recover_with_one_fresh_parameter
    {occurs : Var → Atom → Prop} {Ax : Formula Atom Var → Prop}
    {D A : Formula Atom Var} (h : Var)
    (stable : Theorem occurs Ax (imp D (box D)))
    (guardSupport : ∀ x, x ≠ h → Fresh occurs x D)
    (freshConclusion : Fresh occurs h A)
    (existsGuard : Theorem occurs Ax (ex h D))
    (proof : Derivation occurs (adjoin Ax D) (fun x => x ≠ h) A) :
    Theorem occurs Ax A :=
  recover_of_exists_fresh h stable guardSupport freshConclusion existsGuard proof

#print axioms guarded_transform
#print axioms recover_of_exists_fresh
#print axioms recover_with_one_fresh_parameter
#print axioms Derivation.map
#print axioms Formula.fresh_map

end Classicism.Research.ModalStableNaming
