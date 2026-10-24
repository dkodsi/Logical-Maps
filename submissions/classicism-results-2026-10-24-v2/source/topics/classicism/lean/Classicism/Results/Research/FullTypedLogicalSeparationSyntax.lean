import Classicism.Syntax.Derivation
import Classicism.Syntax.ClosedTypes
import Classicism.Syntax.Vectorize

/-!
# The full typed logical-separation schema

Direct source: `research/2026-10-23/operator-characterizations/h-logical-observer-strengthening.txt`,
sections 1 and 3 (misc, 23 October 2026, unpaginated).

These are formulas of the existing relational object syntax. Each qualification
contains a finite list of types. Boolean and quantifier preservation are identities
of composite operations; the translated reflexivity and Leibniz clauses are retained.
Neither the definition nor a quotation of it is a proof of the H-to-C theorem.
-/

namespace Classicism.Meta.Research.FullTypedLogicalSeparation
open Term

abbrev Observer : RTy := Ty.t ⇒ RTy.t

variable {Sig : Signature} {Γ : Ctx}

def boolFull (E : Term Sig Γ Observer) : Formula Sig Γ :=
  conj (eq' (.app E top) top)
    (conj (eq' (.app E bot) bot)
      (conj
        (eq' (.lam (.app E.weaken (neg v0)))
          (.lam (neg (.app E.weaken v0))))
        (conj
          (eq' (.lam (.lam (.app E.weaken.weaken (conj v1 v0))))
            (.lam (.lam (conj (.app E.weaken.weaken v1)
              (.app E.weaken.weaken v0)))))
          (eq' (.lam (.lam (.app E.weaken.weaken (disj v1 v0))))
            (.lam (.lam (disj (.app E.weaken.weaken v1)
              (.app E.weaken.weaken v0))))))))

def quantifierFull (σ : Ty) (E : Term Sig Γ Observer) : Formula Sig Γ :=
  conj
    (eq' (.lam (.app E.weaken (.app (.all σ) v0)))
      (.lam (forall' (σ := σ) (.app E.weaken.weaken (.app v1 v0)))))
    (eq' (.lam (.app E.weaken (.app (.ex σ) v0)))
      (.lam (exists' (σ := σ) (.app E.weaken.weaken (.app v1 v0)))))

def reflexivityClause (σ : Ty) (E : Term Sig Γ Observer) : Formula Sig Γ :=
  forall' (σ := σ) (.app E.weaken (eq' v0 v0))

def leibnizClause (σ : Ty) (E : Term Sig Γ Observer) : Formula Sig Γ :=
  forall' (σ := σ) (forall' (σ := σ) (forall' (σ := σ ⇒ RTy.t)
    (imp (.app E.weaken.weaken.weaken (eq' v2 v1))
      (imp (.app E.weaken.weaken.weaken (.app v0 v2))
        (.app E.weaken.weaken.weaken (.app v0 v1))))))

def equalityClauses (σ : Ty) (E : Term Sig Γ Observer) : Formula Sig Γ :=
  conj (reflexivityClause σ E) (leibnizClause σ E)

def typeClauses : List Ty → Term Sig Γ Observer → Formula Sig Γ
  | [], _ => top
  | σ :: Δ, E => conj (quantifierFull σ E)
      (conj (equalityClauses σ E) (typeClauses Δ E))

def goodFull (Δ : List Ty) (E : Term Sig Γ Observer) : Formula Sig Γ :=
  conj (boolFull E) (typeClauses Δ E)

/-- Truth agreement after applying one observer to each complete argument tuple. -/
def agree : (ρ : RTy) → {Γ : Ctx} → Term Sig Γ Observer →
    Term Sig Γ ρ → Term Sig Γ ρ → Formula Sig Γ
  | .t, _, E, X, Y => iff (.app E X) (.app E Y)
  | .arr σ ρ, _, E, X, Y => forall' (σ := σ)
      (agree ρ E.weaken (.app X.weaken v0) (.app Y.weaken v0))

def separation (ρ : RTy) (Δ : List Ty) : Sentence Sig :=
  forall' (σ := ρ) (forall' (σ := ρ)
    (iff (eq' v1 v0) (forall' (σ := Observer)
      (imp (goodFull Δ v0) (agree ρ v0 v2 v1)))))

/-- Metalinguistic schema membership, with only closed admitted types. -/
def schema : AxiomSet Sig := fun p =>
  ∃ ρ : RTy, ∃ Δ : List Ty,
    ρ.Closed ∧ Ty.AllClosed Δ ∧ p = separation ρ Δ

theorem boolFull_rename {Θ : Ctx} (r : Ren Γ Θ) (E : Term Sig Γ Observer) :
    (boolFull E).rename r = boolFull (E.rename r) := by
  simp [boolFull, conj, disj, neg, eq', top, bot, ← Term.weaken_rename, Ren.lift]

theorem quantifierFull_rename {Θ : Ctx} (r : Ren Γ Θ) (σ : Ty)
    (E : Term Sig Γ Observer) :
    (quantifierFull σ E).rename r = quantifierFull σ (E.rename r) := by
  simp [quantifierFull, conj, eq', forall', exists', ← Term.weaken_rename, Ren.lift]

theorem equalityClauses_rename {Θ : Ctx} (r : Ren Γ Θ) (σ : Ty)
    (E : Term Sig Γ Observer) :
    (equalityClauses σ E).rename r = equalityClauses σ (E.rename r) := by
  simp [equalityClauses, reflexivityClause, leibnizClause, conj, imp, disj,
    neg, eq', forall', ← Term.weaken_rename, Ren.lift]

theorem typeClauses_rename {Θ : Ctx} (r : Ren Γ Θ) (Δ : List Ty)
    (E : Term Sig Γ Observer) :
    (typeClauses Δ E).rename r = typeClauses Δ (E.rename r) := by
  induction Δ with
  | nil => rfl
  | cons σ Δ ih =>
      simp only [typeClauses, conj, Term.rename_app, Term.rename_and,
        quantifierFull_rename, equalityClauses_rename, ih]

theorem goodFull_rename {Θ : Ctx} (r : Ren Γ Θ) (Δ : List Ty)
    (E : Term Sig Γ Observer) :
    (goodFull Δ E).rename r = goodFull Δ (E.rename r) := by
  simp only [goodFull, conj, Term.rename_app, Term.rename_and,
    boolFull_rename, typeClauses_rename]

theorem goodFull_weaken (Δ : List Ty) (E : Term Sig Γ Observer) (σ : Ty) :
    goodFull Δ (E.weaken (τ := σ)) = (goodFull Δ E).weaken :=
  (goodFull_rename Ren.shift Δ E).symm

theorem subst_weaken_lift {Θ : Ctx} {σ τ : Ty} (s : Sub Sig Γ Θ)
    (a : Term Sig Γ τ) :
    (a.weaken (τ := σ)).subst (Sub.lift s) = (a.subst s).weaken := by
  simp only [Term.weaken, Term.subst_rename, Term.rename_subst]
  rfl

theorem boolFull_subst {Θ : Ctx} (s : Sub Sig Γ Θ) (E : Term Sig Γ Observer) :
    (boolFull E).subst s = boolFull (E.subst s) := by
  simp [boolFull, conj, disj, neg, eq', top, bot, subst_weaken_lift, Sub.lift] <;>
    simp [Ren.shift]

theorem quantifierFull_subst {Θ : Ctx} (s : Sub Sig Γ Θ) (σ : Ty)
    (E : Term Sig Γ Observer) :
    (quantifierFull σ E).subst s = quantifierFull σ (E.subst s) := by
  simp [quantifierFull, conj, eq', forall', exists', subst_weaken_lift, Sub.lift] <;>
    simp [Ren.shift]

theorem equalityClauses_subst {Θ : Ctx} (s : Sub Sig Γ Θ) (σ : Ty)
    (E : Term Sig Γ Observer) :
    (equalityClauses σ E).subst s = equalityClauses σ (E.subst s) := by
  simp [equalityClauses, reflexivityClause, leibnizClause, conj, imp, disj,
    neg, eq', forall', subst_weaken_lift, Sub.lift] <;>
    simp [Ren.shift]

theorem typeClauses_subst {Θ : Ctx} (s : Sub Sig Γ Θ) (Δ : List Ty)
    (E : Term Sig Γ Observer) :
    (typeClauses Δ E).subst s = typeClauses Δ (E.subst s) := by
  induction Δ with
  | nil => rfl
  | cons σ Δ ih =>
      simp only [typeClauses, conj, Term.subst_app, Term.subst_and,
        quantifierFull_subst, equalityClauses_subst, ih]

theorem goodFull_subst {Θ : Ctx} (s : Sub Sig Γ Θ) (Δ : List Ty)
    (E : Term Sig Γ Observer) :
    (goodFull Δ E).subst s = goodFull Δ (E.subst s) := by
  simp only [goodFull, conj, Term.subst_app, Term.subst_and,
    boolFull_subst, typeClauses_subst]

theorem agree_rename (ρ : RTy) {Θ : Ctx} (r : Ren Γ Θ)
    (E : Term Sig Γ Observer) (X Y : Term Sig Γ ρ) :
    (agree ρ E X Y).rename r = agree ρ (E.rename r) (X.rename r) (Y.rename r) := by
  induction ρ using RTy.induction generalizing Γ Θ with
  | t => simp [agree, iff, imp, conj, disj, neg]
  | arr σ ρ ih =>
      simp [agree, forall', ih, ← Term.weaken_rename, Ren.lift]

theorem agree_subst (ρ : RTy) {Θ : Ctx} (s : Sub Sig Γ Θ)
    (E : Term Sig Γ Observer) (X Y : Term Sig Γ ρ) :
    (agree ρ E X Y).subst s = agree ρ (E.subst s) (X.subst s) (Y.subst s) := by
  induction ρ using RTy.induction generalizing Γ Θ with
  | t => simp [agree, iff, imp, conj, disj, neg]
  | arr σ ρ ih =>
      simp [agree, forall', ih, subst_weaken_lift, Sub.lift]

end Classicism.Meta.Research.FullTypedLogicalSeparation
