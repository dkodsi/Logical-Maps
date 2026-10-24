import Classicism.Results.Research.FullTypedLogicalSeparationHTransport
import Classicism.Results.Research.FullTypedLogicalSeparationSyntax

/-!
# Deriving observer laws from the full composite qualification in H

Direct source: `research/2026-10-23/operator-characterizations/h-logical-observer-strengthening.txt`,
sections 1--3 (misc, 23 October 2026, unpaginated).
Every conclusion here inhabits the independent Subst-free H calculus.
-/

namespace Classicism.Meta.Research.FullTypedLogicalSeparation
open Term
open Classicism.Research.FullTypedLogicalSeparationH

variable {Sig : Signature} {Ax : Axioms Sig} {Γ : Ctx}
variable {Ξ : List (Formula Sig Γ)} {E : Term Sig Γ Observer}

theorem equality_iff {p q : Formula Sig Γ}
    (h : Derives Ax Ξ (eq' p q)) : Derives Ax Ξ (iff p q) :=
  .iffI (.eqMp h.weaken₁ .hyp₀) (.eqMpr h.weaken₁ .hyp₀)

theorem typeClauses_at {Δ : List Ty} {σ : Ty} (hσ : σ ∈ Δ)
    (h : Derives Ax Ξ (typeClauses Δ E)) :
    Derives Ax Ξ (conj (quantifierFull σ E) (equalityClauses σ E)) := by
  induction Δ with
  | nil => exact False.elim (List.not_mem_nil hσ)
  | cons τ Δ ih =>
      rcases List.mem_cons.mp hσ with he | ht
      · subst τ
        exact .andI (.andE₁ h) (.andE₁ (.andE₂ h))
      · exact ih ht (.andE₂ (.andE₂ h))

theorem goodFull_bool {Δ : List Ty} (h : Derives Ax Ξ (goodFull Δ E)) :
    Derives Ax Ξ (boolFull E) := .andE₁ h

theorem goodFull_quantifier {Δ : List Ty} {σ : Ty} (hσ : σ ∈ Δ)
    (h : Derives Ax Ξ (goodFull Δ E)) : Derives Ax Ξ (quantifierFull σ E) :=
  .andE₁ (typeClauses_at hσ (.andE₂ h))

theorem goodFull_equality {Δ : List Ty} {σ : Ty} (hσ : σ ∈ Δ)
    (h : Derives Ax Ξ (goodFull Δ E)) : Derives Ax Ξ (equalityClauses σ E) :=
  .andE₂ (typeClauses_at hσ (.andE₂ h))

theorem boolFull_top_eq (h : Derives Ax Ξ (boolFull E)) :
    Derives Ax Ξ (eq' (.app E top) top) := .andE₁ h

theorem boolFull_bottom_eq (h : Derives Ax Ξ (boolFull E)) :
    Derives Ax Ξ (eq' (.app E bot) bot) := .andE₁ (.andE₂ h)

theorem boolFull_neg_eq (h : Derives Ax Ξ (boolFull E)) (p : Formula Sig Γ) :
    Derives Ax Ξ (eq' (.app E (neg p)) (neg (.app E p))) := by
  have hn := Derives.eqCongrFunβ (.andE₁ (.andE₂ (.andE₂ h))) p
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using hn

theorem boolFull_conj_eq (h : Derives Ax Ξ (boolFull E)) (p q : Formula Sig Γ) :
    Derives Ax Ξ (eq' (.app E (conj p q)) (conj (.app E p) (.app E q))) := by
  have h₁ := Derives.eqCongrFunβ (.andE₁ (.andE₂ (.andE₂ (.andE₂ h)))) p
  simp only [Term.instantiate, conj, Term.subst_lam, Term.subst_app,
    subst_weaken_lift] at h₁
  simp [Term.instantiate, Term.subst_rename, Term.subst_id] at h₁
  have h₂ := Derives.eqCongrFunβ h₁ q
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using h₂

theorem boolFull_disj_eq (h : Derives Ax Ξ (boolFull E)) (p q : Formula Sig Γ) :
    Derives Ax Ξ (eq' (.app E (disj p q)) (disj (.app E p) (.app E q))) := by
  have h₁ := Derives.eqCongrFunβ (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))) p
  simp only [Term.instantiate, disj, Term.subst_lam, Term.subst_app,
    subst_weaken_lift] at h₁
  simp [Term.instantiate, Term.subst_rename, Term.subst_id] at h₁
  have h₂ := Derives.eqCongrFunβ h₁ q
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using h₂

theorem quantifierFull_all_eq {σ : Ty} (h : Derives Ax Ξ (quantifierFull σ E))
    (F : Term Sig Γ (σ ⇒ RTy.t)) :
    Derives Ax Ξ (eq' (.app E (.app (.all σ) F))
      (forall' (.app E.weaken (.app F.weaken v0)))) := by
  have h₁ := Derives.eqCongrFunβ (.andE₁ h) F
  simp only [Term.instantiate, forall', Term.subst_lam, Term.subst_app,
    subst_weaken_lift] at h₁
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using h₁

theorem quantifierFull_ex_eq {σ : Ty} (h : Derives Ax Ξ (quantifierFull σ E))
    (F : Term Sig Γ (σ ⇒ RTy.t)) :
    Derives Ax Ξ (eq' (.app E (.app (.ex σ) F))
      (exists' (.app E.weaken (.app F.weaken v0)))) := by
  have h₁ := Derives.eqCongrFunβ (.andE₂ h) F
  simp only [Term.instantiate, exists', Term.subst_lam, Term.subst_app,
    subst_weaken_lift] at h₁
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using h₁

theorem equalityClauses_refl {σ : Ty} (h : Derives Ax Ξ (equalityClauses σ E))
    (a : Term Sig Γ σ) : Derives Ax Ξ (.app E (eq' a a)) := by
  have h₁ := Derives.allEβ (.andE₁ h) a
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using h₁

theorem equalityClauses_leibniz {σ : Ty} (h : Derives Ax Ξ (equalityClauses σ E))
    (a b : Term Sig Γ σ) (F : Term Sig Γ (σ ⇒ RTy.t)) :
    Derives Ax Ξ (imp (.app E (eq' a b))
      (imp (.app E (.app F a)) (.app E (.app F b)))) := by
  have h₁ := Derives.allEβ (.andE₂ h) a
  simp only [Term.instantiate, forall', imp, disj, neg, eq', Term.subst_lam,
    Term.subst_app, subst_weaken_lift] at h₁
  simp [Term.instantiate, Term.subst_rename, Term.subst_id] at h₁
  have h₂ := Derives.allEβ h₁ b
  simp only [Term.instantiate, forall', imp, disj, neg, eq', Term.subst_lam,
    Term.subst_app, subst_weaken_lift] at h₂
  simp [Term.instantiate, Term.subst_rename, Term.subst_id] at h₂
  have h₃ := Derives.allEβ h₂ F
  simpa [Term.instantiate, Term.subst_rename, Term.subst_id, Sub.lift, Ren.shift] using h₃

/-- All transport fields are discharged from the actual finite composite
qualification, using H equality substitution and ordinary logical rules. -/
def fullTransportLaws (Ax : Axioms Sig) (S : List Ty) : TransportLaws Ax S where
  qualification := goodFull S
  qualification_weaken E := goodFull_weaken S E _
  andLaw E p q := equality_iff (boolFull_conj_eq (goodFull_bool .hyp₀) p q)
  orLaw E p q := equality_iff (boolFull_disj_eq (goodFull_bool .hyp₀) p q)
  notLaw E p := equality_iff (boolFull_neg_eq (goodFull_bool .hyp₀) p)
  allLaw hσ E F := equality_iff
    (quantifierFull_all_eq (goodFull_quantifier hσ .hyp₀) F)
  exLaw hσ E F := equality_iff
    (quantifierFull_ex_eq (goodFull_quantifier hσ .hyp₀) F)
  refLaw hσ E a := equalityClauses_refl (goodFull_equality hσ .hyp₀) a
  leibnizLaw hσ E a b F :=
    equalityClauses_leibniz (goodFull_equality hσ .hyp₀) a b F

end Classicism.Meta.Research.FullTypedLogicalSeparation
