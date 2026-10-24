import Classicism.Results.Research.ModalStableNaming
import Classicism.Syntax.Types

/-!
# Erasing a fresh representation name

Original metatheory, 23 October 2026; direct source `misc`.

This assembles syntax relabeling and stable-guard elimination into one proof
transformation. The inputs describe an atom-level name-to-parameter map,
ordinary freshness, and preservation of AXIOM INSTANCES. Preservation of
arbitrary proofs and conservativity are conclusions, not input fields.

The theorem is parametric in atomic syntax. Its application to a concrete
typed applicative language must supply that language's atom relabeling and
verify the displayed syntactic side conditions. No concrete translation of
the complete existing C syntax is asserted here.
-/

namespace Classicism.Research.ModalStableNaming

universe u v u' v'

open Formula

/-- Erase a new name by a constructor-preserving syntax map. The translated
defining axiom has a stable guard and an existential witness in the base.
No open hypothesis is necessitated in the resulting base derivation. -/
theorem erase_stable_name
    {Atom : Type u} {Var : Type v} {Atom' : Type u'} {Var' : Type v'}
    {occurs : Var → Atom → Prop} {occurs' : Var' → Atom' → Prop}
    {Ax : Formula Atom Var → Prop} {Ax' : Formula Atom' Var' → Prop}
    {allowed : Var → Prop} {D A : Formula Atom Var}
    (atomMap : Atom → Atom') (varMap : Var → Var') (h : Var')
    (freshMap : ∀ x p, Fresh occurs x p →
      Fresh occurs' (varMap x) (Formula.map atomMap varMap p))
    (axiomMap : ∀ p, Ax p → Ax' (Formula.map atomMap varMap p))
    (stable : Theorem occurs' Ax'
      (imp (Formula.map atomMap varMap D) (box (Formula.map atomMap varMap D))))
    (freshGuard : ∀ x, allowed x →
      Fresh occurs' (varMap x) (Formula.map atomMap varMap D))
    (freshConclusion : Fresh occurs' h (Formula.map atomMap varMap A))
    (existsGuard : Theorem occurs' Ax' (ex h (Formula.map atomMap varMap D)))
    (proof : Derivation occurs (adjoin Ax D) allowed A) :
    Theorem occurs' Ax' (Formula.map atomMap varMap A) := by
  let D' := Formula.map atomMap varMap D
  let targetAllowed := fun y => Fresh occurs' y D'
  have translated : Derivation occurs' (adjoin Ax' D') targetAllowed
      (Formula.map atomMap varMap A) := by
    apply Derivation.map atomMap varMap ?_ ?_ freshGuard proof
    · intro p hp
      exact .logical (LogicalAxiom.map atomMap varMap freshMap hp)
    · intro p hp
      rcases hp with hp | hp
      · exact .theory (Or.inl (axiomMap p hp))
      · subst p
        exact .theory (Or.inr rfl)
  exact recover_of_exists_fresh h stable (fun _ hx => hx)
    freshConclusion existsGuard translated

/-- A convenient stronger support condition: the translated defining
condition may contain only the replacement parameter, and no translated
generalization binds that parameter. -/
theorem erase_name_with_one_parameter
    {Atom : Type u} {Var : Type v} {Atom' : Type u'} {Var' : Type v'}
    {occurs : Var → Atom → Prop} {occurs' : Var' → Atom' → Prop}
    {Ax : Formula Atom Var → Prop} {Ax' : Formula Atom' Var' → Prop}
    {allowed : Var → Prop} {D A : Formula Atom Var}
    (atomMap : Atom → Atom') (varMap : Var → Var') (h : Var')
    (freshMap : ∀ x p, Fresh occurs x p →
      Fresh occurs' (varMap x) (Formula.map atomMap varMap p))
    (axiomMap : ∀ p, Ax p → Ax' (Formula.map atomMap varMap p))
    (stable : Theorem occurs' Ax'
      (imp (Formula.map atomMap varMap D) (box (Formula.map atomMap varMap D))))
    (guardSupport : ∀ y, y ≠ h →
      Fresh occurs' y (Formula.map atomMap varMap D))
    (generalizationFresh : ∀ x, allowed x → varMap x ≠ h)
    (freshConclusion : Fresh occurs' h (Formula.map atomMap varMap A))
    (existsGuard : Theorem occurs' Ax' (ex h (Formula.map atomMap varMap D)))
    (proof : Derivation occurs (adjoin Ax D) allowed A) :
    Theorem occurs' Ax' (Formula.map atomMap varMap A) :=
  erase_stable_name atomMap varMap h freshMap axiomMap stable
    (fun x hx => guardSupport _ (generalizationFresh x hx))
    freshConclusion existsGuard proof

#print axioms erase_stable_name
#print axioms erase_name_with_one_parameter

/-! ## A concrete, capture-free atom replacement

The following instance uses typed applicative terms and truth/equality atoms.
The source signature has one additional typed constant. Its replacement is
the genuinely new variable `none`; every original variable and every binder
is mapped by `some`. Freshness and the equality-axiom map are proved below,
rather than retained as fields. This is an atom-level integration, not yet
an identification with the separate full de Bruijn comprehension syntax.

Its conclusion is in the base theory with an enlarged variable supply. The
displayed applicative fragment does not include classical logic, universal
instantiation, comprehension or Intensionality. In particular its existential
guard premise has not been discharged using the representation interface.
Transport of that full calculus, and its existential representation theorem,
remains a separate substantive obligation; the fragment certificate does not
establish the complete lambda-free reconstruction or equivalence with C.
-/

namespace Applicative

open Classicism.Meta

/-- Typed applicative syntax with no lambda constructor. -/
inductive Term (Const Var : Ty → Type) : Ty → Type where
  | var {σ} : Var σ → Term Const Var σ
  | const {σ} : Const σ → Term Const Var σ
  | app {σ ρ} : Term Const Var (σ ⇒ ρ) → Term Const Var σ → Term Const Var ρ

/-- A signature with exactly one distinguished new constant of type κ. -/
inductive NamedConst (Const : Ty → Type) (κ : Ty) : Ty → Type where
  | old {σ} : Const σ → NamedConst Const κ σ
  | name : NamedConst Const κ κ

/-- A typed variable supply with exactly one distinguished new parameter. -/
inductive ParamVar (Var : Ty → Type) (κ : Ty) : Ty → Type where
  | old {σ} : Var σ → ParamVar Var κ σ
  | parameter : ParamVar Var κ κ

abbrev Key (Var : Ty → Type) := Sigma Var

def oldKey {Var : Ty → Type} {σ : Ty} (x : Var σ) : Key Var := ⟨σ, x⟩

def newKey {Var : Ty → Type} {κ σ : Ty} : ParamVar Var κ σ → Option (Key Var)
  | .old x => some (oldKey x)
  | .parameter => none

namespace Term

variable {Const Var : Ty → Type} {κ : Ty}

def occurs {K : Type} (key : {σ : Ty} → Var σ → K) (x : K) :
    {σ : Ty} → Term Const Var σ → Prop
  | _, .var y => x = key y
  | _, .const _ => False
  | _, .app f a => occurs key x f ∨ occurs key x a

def replace : {σ : Ty} → Term (NamedConst Const κ) Var σ →
    Term Const (ParamVar Var κ) σ
  | _, .var x => .var (.old x)
  | _, .const (.old c) => .const c
  | _, .const .name => .var .parameter
  | _, .app f a => .app (replace f) (replace a)

def NoName : {σ : Ty} → Term (NamedConst Const κ) Var σ → Prop
  | _, .var _ => True
  | _, .const (.old _) => True
  | _, .const .name => False
  | _, .app f a => NoName f ∧ NoName a

theorem replace_occurs_some {σ : Ty}
    (t : Term (NamedConst Const κ) Var σ) (x : Key Var) :
    occurs newKey (some x) (replace t) → occurs oldKey x t := by
  induction t with
  | var y => exact fun h => Option.some.inj h
  | const c =>
      cases c with
      | old c => exact fun h => False.elim h
      | name =>
          intro h
          change some x = none at h
          cases h
  | app f a ihf iha =>
      intro h
      rcases h with h | h
      · exact Or.inl (ihf h)
      · exact Or.inr (iha h)

theorem replace_fresh_none {σ : Ty}
    (t : Term (NamedConst Const κ) Var σ) (ht : NoName t) :
    ¬ occurs newKey none (replace t) := by
  induction t with
  | var y =>
      intro h
      change none = some (oldKey y) at h
      cases h
  | const c =>
      cases c with
      | old c => exact fun h => h
      | name => exact False.elim ht
  | app f a ihf iha =>
      intro h
      rcases h with h | h
      · exact ihf ht.1 h
      · exact iha ht.2 h

end Term

inductive Atom (Const Var : Ty → Type) : Type where
  | truth : Term Const Var Ty.t → Atom Const Var
  | eq {σ} : Term Const Var σ → Term Const Var σ → Atom Const Var

namespace Atom

variable {Const Var : Ty → Type} {κ : Ty}

def occurs {K : Type} (key : {σ : Ty} → Var σ → K) (x : K) : Atom Const Var → Prop
  | .truth p => p.occurs key x
  | .eq a b => a.occurs key x ∨ b.occurs key x

def replace : Atom (NamedConst Const κ) Var → Atom Const (ParamVar Var κ)
  | .truth p => .truth p.replace
  | .eq a b => .eq a.replace b.replace

def NoName : Atom (NamedConst Const κ) Var → Prop
  | .truth p => p.NoName
  | .eq a b => a.NoName ∧ b.NoName

theorem replace_occurs_some (a : Atom (NamedConst Const κ) Var) (x : Key Var) :
    occurs newKey (some x) (replace a) → occurs oldKey x a := by
  cases a with
  | truth p => exact p.replace_occurs_some x
  | eq a b =>
      intro h
      rcases h with h | h
      · exact Or.inl (a.replace_occurs_some x h)
      · exact Or.inr (b.replace_occurs_some x h)

theorem replace_fresh_none (a : Atom (NamedConst Const κ) Var) (ha : NoName a) :
    ¬ occurs newKey none (replace a) := by
  cases a with
  | truth p => exact p.replace_fresh_none ha
  | eq a b =>
      intro h
      rcases h with h | h
      · exact a.replace_fresh_none ha.1 h
      · exact b.replace_fresh_none ha.2 h

end Atom

abbrev SourceFormula (Const Var : Ty → Type) (κ : Ty) :=
  Formula (Atom (NamedConst Const κ) Var) (Key Var)

abbrev TargetFormula (Const Var : Ty → Type) (κ : Ty) :=
  Formula (Atom Const (ParamVar Var κ)) (Option (Key Var))

variable {Const Var : Ty → Type} {κ : Ty}

def replaceFormula (p : SourceFormula Const Var κ) : TargetFormula Const Var κ :=
  Formula.map Atom.replace some p

def NoName : SourceFormula Const Var κ → Prop
  | .atom a => a.NoName
  | .imp p q => NoName p ∧ NoName q
  | .box p => NoName p
  | .all _ p => NoName p
  | .ex _ p => NoName p

/-- The global freshness condition now follows from the actual atom map. -/
theorem replace_fresh_some (x : Key Var) (p : SourceFormula Const Var κ)
    (hp : Fresh (Atom.occurs oldKey) x p) :
    Fresh (Atom.occurs newKey) (some x) (replaceFormula p) :=
  Formula.fresh_map Atom.replace some (fun x a => a.replace_occurs_some x) hp

/-- A conclusion in the old signature has no occurrence of the new parameter. -/
theorem replace_fresh_none (p : SourceFormula Const Var κ) (hp : NoName p) :
    Fresh (Atom.occurs newKey) none (replaceFormula p) := by
  induction p with
  | atom a => exact a.replace_fresh_none hp
  | imp p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | box p ih => exact ih hp
  | all x p ih => exact Or.inr (ih hp)
  | ex x p ih => exact Or.inr (ih hp)

/-- A concrete uniform theory fragment: typed equality and modal persistence.
It deliberately contains no comprehension, lambda, choice, or desired
conservativity theorem. Formula binders remain those of the modal calculus. -/
inductive ApplicativeAxiom (Const Var : Ty → Type) (K : Type) :
    Formula (Atom Const Var) K → Prop where
  | refl {σ} (a : Term Const Var σ) : ApplicativeAxiom Const Var K (.atom (.eq a a))
  | symm {σ} (a b : Term Const Var σ) : ApplicativeAxiom Const Var K
      (.imp (.atom (.eq a b)) (.atom (.eq b a)))
  | trans {σ} (a b c : Term Const Var σ) : ApplicativeAxiom Const Var K
      (.imp (.atom (.eq a b)) (.imp (.atom (.eq b c)) (.atom (.eq a c))))
  | app {σ ρ} (f g : Term Const Var (σ ⇒ ρ)) (a b : Term Const Var σ) :
      ApplicativeAxiom Const Var K
        (.imp (.atom (.eq f g))
          (.imp (.atom (.eq a b)) (.atom (.eq (.app f a) (.app g b)))))
  | four (p : Formula (Atom Const Var) K) : ApplicativeAxiom Const Var K
      (.imp (.box p) (.box (.box p)))

/-- Every displayed theory axiom survives the actual replacement by its
corresponding axiom instance. This is not an assumed axiom-map field. -/
theorem replace_applicative_axiom {p : SourceFormula Const Var κ}
    (hp : ApplicativeAxiom (NamedConst Const κ) Var (Key Var) p) :
    ApplicativeAxiom Const (ParamVar Var κ) (Option (Key Var)) (replaceFormula p) := by
  cases hp with
  | refl a => exact .refl a.replace
  | symm a b => exact .symm a.replace b.replace
  | trans a b c => exact .trans a.replace b.replace c.replace
  | app f g a b => exact .app f.replace g.replace a.replace b.replace
  | four p => exact .four (replaceFormula p)

/-- Concrete fresh-name erasure. The source definition is closed, and the
conclusion contains no distinguished name. Only persistence and existence
of the translated guard remain mathematical premises; syntactic freshness,
generalization safety and equality-axiom transport have been discharged. -/
theorem erase_applicative_name
    {D A : SourceFormula Const Var κ}
    (closedGuard : ∀ x, Fresh (Atom.occurs oldKey) x D)
    (oldConclusion : NoName A)
    (stable : Theorem (Atom.occurs newKey)
      (ApplicativeAxiom Const (ParamVar Var κ) (Option (Key Var)))
      (.imp (replaceFormula D) (.box (replaceFormula D))))
    (existsGuard : Theorem (Atom.occurs newKey)
      (ApplicativeAxiom Const (ParamVar Var κ) (Option (Key Var)))
      (.ex none (replaceFormula D)))
    (proof : Theorem (Atom.occurs oldKey)
      (adjoin (ApplicativeAxiom (NamedConst Const κ) Var (Key Var)) D) A) :
    Theorem (Atom.occurs newKey)
      (ApplicativeAxiom Const (ParamVar Var κ) (Option (Key Var)))
      (replaceFormula A) :=
  erase_stable_name Atom.replace some none replace_fresh_some
    (fun _ hp => replace_applicative_axiom hp) stable
    (fun x _ => replace_fresh_some x D (closedGuard x))
    (replace_fresh_none A oldConclusion) existsGuard proof

/-- In the concrete S4 fragment a boxed definition has the required
persistence automatically. Its existential witness is still required. -/
theorem erase_boxed_applicative_name
    {U A : SourceFormula Const Var κ}
    (closedGuard : ∀ x, Fresh (Atom.occurs oldKey) x (.box U))
    (oldConclusion : NoName A)
    (existsGuard : Theorem (Atom.occurs newKey)
      (ApplicativeAxiom Const (ParamVar Var κ) (Option (Key Var)))
      (.ex none (replaceFormula (.box U))))
    (proof : Theorem (Atom.occurs oldKey)
      (adjoin (ApplicativeAxiom (NamedConst Const κ) Var (Key Var)) (.box U)) A) :
    Theorem (Atom.occurs newKey)
      (ApplicativeAxiom Const (ParamVar Var κ) (Option (Key Var)))
      (replaceFormula A) :=
  erase_applicative_name closedGuard oldConclusion
    (.theory (.four (replaceFormula U))) existsGuard proof

#print axioms replace_fresh_some
#print axioms replace_fresh_none
#print axioms replace_applicative_axiom
#print axioms erase_applicative_name
#print axioms erase_boxed_applicative_name

end Applicative

end Classicism.Research.ModalStableNaming
