import StrongPossibilityConsequencesStability
import Classicism.Syntax.StrongPossibility
import Classicism.Syntax.Pure

/-!
# The exact finitary universal-identity core of Strong Possibility

Source: notes/reflection-universal-core-20261022.md §§2–7,
notes/sp-failed-disjunction-20261022.md §17 (session deductions, misc).

Unlike a schema defined by an assumed reflection certificate, this file defines
an actual inductive grammar and constructs its C derivations by induction.
Identity arguments may be arbitrary typed terms (including quantifiers inside
those terms); the Boolean matrix and its universal prefix are finite.

It then constructs the universal Boolean-identity normal form of D p and proves
the two exact schema entailments. No Max/SP consistency, semantic completeness,
model, infinitary rule, or unproved universal-reflection oracle is assumed.
-/

namespace Classicism.Meta.Research.StrongPossibilityConsequences.UniversalCore

open AxiomSet
open Classicism.Research.StrongPossibilityConsequences

variable {Sig : Signature}

def boxNeF {Γ : Ctx} (p : Formula Sig Γ) : Formula Sig Γ :=
  Term.exists' (σ := Ty.t)
    (Term.conj Term.v0 (Term.box (Term.imp (Term.dia Term.v0) p.weaken)))

def decidesF {Γ : Ctx} (p : Formula Sig Γ) : Formula Sig Γ :=
  Term.conj (Term.imp p (boxNeF p)) (Term.imp (Term.neg p) (boxNeF (Term.neg p)))

def reflectsF {Γ : Ctx} (p : Formula Sig Γ) : Formula Sig Γ :=
  Term.imp (Term.diaNe p) p

inductive Matrix (Sig : Signature) (Γ : Ctx) where
  | eq {σ : Ty} : Term Sig Γ σ → Term Sig Γ σ → Matrix Sig Γ
  | neg : Matrix Sig Γ → Matrix Sig Γ
  | conj : Matrix Sig Γ → Matrix Sig Γ → Matrix Sig Γ
  | disj : Matrix Sig Γ → Matrix Sig Γ → Matrix Sig Γ
  | imp : Matrix Sig Γ → Matrix Sig Γ → Matrix Sig Γ
  | iff : Matrix Sig Γ → Matrix Sig Γ → Matrix Sig Γ

def Matrix.formula {Γ : Ctx} : Matrix Sig Γ → Formula Sig Γ
  | .eq x y => Term.eq' x y
  | .neg p => Term.neg p.formula
  | .conj p q => Term.conj p.formula q.formula
  | .disj p q => Term.disj p.formula q.formula
  | .imp p q => Term.imp p.formula q.formula
  | .iff p q => Term.iff p.formula q.formula

inductive Universal (Sig : Signature) : Ctx → Type where
  | matrix {Γ : Ctx} : Matrix Sig Γ → Universal Sig Γ
  | all {Γ : Ctx} {σ : Ty} : Universal Sig (σ :: Γ) → Universal Sig Γ

def Universal.formula : {Γ : Ctx} → Universal Sig Γ → Formula Sig Γ
  | _, .matrix m => m.formula
  | _, .all b => Term.forall' b.formula

private theorem promote {p : Sentence Sig} (h : C.TheoremMinus p) : C.Theorem p :=
  Derivable.mono (fun _ ha => ha.elim) h

/-- The finite Boolean-matrix induction constructs the actual C derivation. -/
theorem Matrix.decides {Γ : Ctx} : ∀ m : Matrix Sig Γ,
    Derivable C.axioms [] (decidesF m.formula)
  | .eq (σ := σ) x y => Derivable.allE₂β (Derivable.ofTheorem
      (promote (C.TheoremMinus.ofPure (decidesNe_eq.derivable σ)))) x y
  | .neg p => Derivable.impE (Derivable.allEβ (Derivable.ofTheorem
      (promote (C.TheoremMinus.ofPure decidesNe_neg.derivable))) p.formula) p.decides
  | .conj p q => Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem
        (promote (C.TheoremMinus.ofPure decidesNe_and.derivable))) p.formula q.formula)
      p.decides) q.decides
  | .disj p q => Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem
        (promote (C.TheoremMinus.ofPure decidesNe_or.derivable))) p.formula q.formula)
      p.decides) q.decides
  | .imp p q => Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem
        (promote (C.TheoremMinus.ofPure decidesNe_imp.derivable))) p.formula q.formula)
      p.decides) q.decides
  | .iff p q => Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem
        (promote (C.TheoremMinus.ofPure decidesNe_iff.derivable))) p.formula q.formula)
      p.decides) q.decides

private theorem conv_neg {Γ : Ctx} {p q : Formula Sig Γ} (h : p ≡ q) :
    Term.neg p ≡ Term.neg q := Conv.app_congr (Conv.refl _) h

private theorem conv_imp {Γ : Ctx} {p p' q q' : Formula Sig Γ}
    (hp : p ≡ p') (hq : q ≡ q') : Term.imp p q ≡ Term.imp p' q' :=
  Conv.app_congr (Conv.app_congr (Conv.refl _) (conv_neg hp)) hq

private theorem conv_all {Γ : Ctx} {σ : Ty} {p q : Formula Sig (σ :: Γ)}
    (h : p ≡ q) : Term.forall' p ≡ Term.forall' q :=
  Conv.app_congr (Conv.refl _) (Conv.lam_congr h)

private theorem conv_diaNe {Γ : Ctx} {p q : Formula Sig Γ} (h : p ≡ q) :
    Term.diaNe p ≡ Term.diaNe q := by
  apply conv_neg
  apply Conv.app_congr (Conv.refl _)
  apply Conv.lam_congr
  apply Conv.app_congr (Conv.refl _)
  apply Conv.app_congr
  · apply Conv.app_congr (Conv.refl _)
    exact conv_imp (Conv.refl _) (conv_neg (Conv.rename Ren.shift h))
  · exact Conv.refl _

private theorem conv_reflects {Γ : Ctx} {p q : Formula Sig Γ} (h : p ≡ q) :
    reflectsF p ≡ reflectsF q := conv_imp (conv_diaNe h) h

private theorem instantiate_lift_shift {Γ : Ctx} {σ τ : Ty}
    (b : Term Sig (σ :: Γ) τ) :
    (b.rename (Ren.lift Ren.shift)).instantiate Term.v0 = b := by
  show (b.rename (Ren.lift Ren.shift)).subst (Sub.cons Term.v0 Sub.id) = b
  have hs : Sub.compRen (Sub.cons (Term.v0 : Term Sig (σ :: Γ) σ) Sub.id)
      (Ren.lift Ren.shift) = Sub.id := by
    funext υ v
    cases v <;> rfl
  rw [Term.subst_rename, hs, Term.subst_id]

private theorem app_lam_weaken_var {Γ : Ctx} {σ : Ty}
    (b : Formula Sig (σ :: Γ)) :
    Term.app (Term.lam (b.rename (Ren.lift Ren.shift))) Term.v0 ≡ b := by
  have h := Conv.beta (b.rename (Ren.lift Ren.shift)) Term.v0
  rwa [instantiate_lift_shift] at h

/-- Every universal prefix over a finite Boolean matrix of typed identities
reflects D in C. Generalized Barcan is not assumed. -/
theorem Universal.reflects : ∀ {Γ : Ctx} (u : Universal Sig Γ),
    Derivable C.axioms [] (reflectsF u.formula)
  | _, .matrix m => Derivable.impE (Derivable.allEβ (Derivable.ofTheorem
      (promote (C.TheoremMinus.ofPure diaNe_reflect.derivable))) m.formula) m.decides
  | _, .all (σ := σ) b => by
    let body := Term.app (Term.lam (b.formula.rename (Ren.lift Ren.shift))) Term.v0
    have hb : body ≡ b.formula := app_lam_weaken_var b.formula
    have hstep : Derivable C.axioms []
        (Term.imp (Term.forall' (reflectsF body)) (reflectsF (Term.forall' body))) := by
      have raw := Derivable.allEβ (Δ := []) (Derivable.ofTheorem
        (promote (C.TheoremMinus.ofPure (diaNe_forall_reflect.derivable σ))))
        (Term.lam b.formula)
      apply Derivable.conv raw
      apply Conv.of_nf 0 _ _
      simp only [Term.nf_zero, reflectsF, body, Term.diaNe, Term.instantiate,
        Term.close, Term.weaken, Term.neg, Term.exists', Term.forall', Term.conj,
        Term.box, Term.imp, Term.dia, Term.rename_app, Term.rename_lam,
        Term.rename_rename, Term.rename_not, Term.rename_ex, Term.rename_and,
        Term.rename_or, Term.rename_all, Term.rename_eq, Term.rename_var,
        Term.subst_app, Term.subst_lam, Term.subst_not, Term.subst_ex,
        Term.subst_and, Term.subst_or, Term.subst_all, Term.subst_eq,
        Term.subst_var, Sub.lift, Sub.cons, Ren.lift_zero, Ren.lift_succ,
        Ren.shift, Ren.comp]
      simp only [← Ren.lift_comp]
      rfl
    have hbody : Derivable C.axioms [] (Term.forall' (reflectsF body)) :=
      Derivable.allI (Derivable.conv b.reflects (conv_reflects hb.symm))
    exact Derivable.conv (Derivable.impE hstep hbody) (conv_reflects (conv_all hb))

/-- A particular member of the grammar: D's fixed-point/disequality form. -/
def fixedCore (p : Sentence Sig) : Universal Sig [] :=
  .all (.matrix (.imp (.eq Term.v0 (Term.dia Term.v0))
    (.imp (.neg (.eq Term.v0 Term.bot))
      (.neg (.eq (Term.conj Term.v0 p.weaken) Term.bot)))))

theorem fixedCore_equiv (p : Sentence Sig) :
    C.Theorem (Term.iff (Term.diaNe p) (fixedCore p).formula) :=
  promote (Derivable.allEβ (C.TheoremMinus.ofPure diaNe_fixed_iff.derivable) p)

theorem fixedCore_closed {p : Sentence Sig} (hc : p.closedTypes = true) :
    (fixedCore p).formula.closedTypes = true := by
  simp [fixedCore, Universal.formula, Matrix.formula,
    Term.weaken, Term.closedTypes_rename, hc]

def universalMaxConsistent (Sig : Signature) : AxiomSet Sig := fun a =>
  a.closedTypes = true ∧ ∃ u : Universal Sig [],
    a = u.formula ∧ Consistent (maximalist ∪ single a)

private theorem diaNe_closed {Γ : Ctx} (p : Formula Sig Γ) :
    (Term.diaNe p).closedTypes = p.closedTypes := by
  simp [Term.diaNe, Term.weaken, Term.closedTypes_rename]

/-- SP yields each independently Max-consistent sentence in the defined
universal-identity grammar. -/
theorem sp_entails_universal_core : strongPossibility Sig ⟹ universalMaxConsistent Sig := by
  rintro a ⟨hc, u, rfl, hcon⟩
  have hd : Theorem (C.axioms ∪ strongPossibility Sig) (Term.diaNe u.formula) :=
    Theorem.ax ⟨by rw [diaNe_closed]; exact hc, _, hcon, rfl⟩
  exact Theorem.mp (Theorem.ofC u.reflects) hd

/-- Conversely the universal-identity core supplies every original SP axiom.
The Max-consistency of the normal form is derived from that of p. -/
theorem universal_core_entails_sp : universalMaxConsistent Sig ⟹ strongPossibility Sig := by
  rintro a ⟨hc, p, hcon, rfl⟩
  have hpc : p.closedTypes = true := by rwa [diaNe_closed] at hc
  have hintro : C.Theorem (Term.imp p (Term.diaNe p)) :=
    promote (Derivable.allEβ (C.TheoremMinus.ofPure diaNe_intro.derivable) p)
  have himp : C.Theorem (Term.imp p (fixedCore p).formula) :=
    Derivable.impI (Derivable.iffE₁ (Derivable.weaken₁ (fixedCore_equiv p))
      (Derivable.impE (Derivable.weaken₁ hintro) Derivable.hyp₀))
  have hcons : Consistent (maximalist ∪ single (fixedCore p).formula) := by
    apply Consistent.of_entails (Ax₁ := maximalist ∪ single p) ?_ hcon
    intro b hb
    rcases hb with hb | hb
    · exact Theorem.ax (Or.inl hb)
    · change b = (fixedCore p).formula at hb
      subst b
      exact Theorem.mp (Theorem.ofC himp) (Theorem.ax (Or.inr rfl))
  have hu : Theorem (C.axioms ∪ universalMaxConsistent Sig) (fixedCore p).formula :=
    Theorem.ax ⟨fixedCore_closed hpc, fixedCore p, rfl, hcons⟩
  exact Derivable.iffE₂ (Theorem.ofC (fixedCore_equiv p)) hu

theorem sp_consistent_iff_universal_core :
    Consistent (strongPossibility Sig) ↔ Consistent (universalMaxConsistent Sig) :=
  ⟨Consistent.of_entails sp_entails_universal_core,
    Consistent.of_entails universal_core_entails_sp⟩

#print axioms Matrix.decides
#print axioms Universal.reflects
#print axioms fixedCore_equiv
#print axioms fixedCore_closed
#print axioms sp_entails_universal_core
#print axioms universal_core_entails_sp
#print axioms sp_consistent_iff_universal_core

end Classicism.Meta.Research.StrongPossibilityConsequences.UniversalCore
