import Classicism.Results.Research.ModalConcreteToCModal
import Classicism.Results.Research.ModalComprehensionConcreteCalculus

/-!
# Actual proof translation from the lambda-free calculus into C

Original research, misc, 23 October 2026. Strong comprehension is derived
using a finite lambda witness in the TARGET language. The source language
has no lambda, conversion, or equality-under-abstraction rule. The final
base theorem translates every constructor of its actual derivation relation
into existing `C.Derivable`; it has no interface-preservation hypotheses.
The converse translation and a full classical-language equivalence remain
separate obligations.
-/

namespace Classicism.Research.ModalConcreteToC
open Classicism.Meta
open ModalComprehensionRepresentation (diagram)

abbrev SourceBody := ModalComprehensionConcreteSyntax.Body
abbrev SourceProof := ModalComprehensionConcreteSyntax.Derives
abbrev SourceAxioms := ModalComprehensionConcreteSyntax.Axioms

variable {Const : Ty → Type}

theorem c_iff_conv {Γ} {p p' q q' : Formula (signature Const) Γ}
    (hp : Conv p p') (hq : Conv q q') : Conv (Term.iff p q) (Term.iff p' q') :=
  Conv.app_congr (Conv.app_congr (Conv.refl _) 
    (Conv.app_congr (Conv.app_congr (Conv.refl _) 
      (Conv.app_congr (Conv.refl _) hp)) hq))
    (Conv.app_congr (Conv.app_congr (Conv.refl _)
      (Conv.app_congr (Conv.refl _) hq)) hp)

theorem coextC_conv (ρ : RTy) : ∀ {Γ} {a a' b b' : Term (signature Const) Γ ρ},
    Conv a a' → Conv b b' → Conv (coextC ρ a b) (coextC ρ a' b') := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ a a' b b' ha hb
      exact c_iff_conv ha hb
  | arr σ ρ ih =>
      intro Γ a a' b b' ha hb
      exact Conv.app_congr (Conv.refl _) (Conv.lam_congr (ih
        (Conv.app_congr (Conv.rename Ren.shift ha) (Conv.refl _))
        (Conv.app_congr (Conv.rename Ren.shift hb) (Conv.refl _))))

theorem coextC_refl (ρ : RTy) : ∀ {Γ} (a : Term (signature Const) Γ ρ),
    C.Derivable [] (coextC ρ a a) := by
  induction ρ using RTy.induction with
  | t => intro Γ a; exact Classicism.Meta.Derivable.iffI Classicism.Meta.Derivable.hyp₀ Classicism.Meta.Derivable.hyp₀
  | arr σ ρ ih => intro Γ a; exact Classicism.Meta.Derivable.allI (ih _)

theorem c_beta_fresh {Γ σ} {ρ : RTy} (p : Term (signature Const) (σ :: Γ) ρ) :
    Conv (.app (Term.lam p).weaken (.var .zero)) p := by
  have h : Conv (.app (Term.lam p).weaken (.var .zero))
      ((p.rename (Ren.lift (Ren.shift (σ := σ)))).instantiate (.var .zero)) :=
    Conv.beta _ _
  rw [c_fresh_inst] at h
  exact h

/-- The admitted finite body, represented by a target C lambda term. -/
def bodyWitness : {Γ : Ctx} → {ρ : RTy} → SourceBody Const Γ ρ →
    Term (signature Const) Γ ρ
  | _, _, .atom p => toC p
  | _, _, .bind A => .lam (bodyWitness A)

theorem bodyWitness_rename {Γ Θ} {ρ : RTy}
    (r : SourceRen Γ Θ) (A : SourceBody Const Γ ρ) :
    bodyWitness (A.rename r) = (bodyWitness A).rename (toCRen r) := by
  induction A generalizing Θ with
  | atom p => exact toC_rename r p
  | bind A ih =>
      simp only [ModalComprehensionConcreteSyntax.Body.rename, bodyWitness,
        Term.rename_lam, ih, toCRen_lift]

/-- The finite body diagram is exactly coextension with its lambda witness,
up to the target calculus's explicit beta conversions. -/
theorem diagram_to_coext {Γ} {ρ : RTy} (A : SourceBody Const Γ ρ)
    (H : SourceTerm Const Γ ρ) :
    Conv (toC (diagram A H)) (coextC ρ (toC H) (bodyWitness A)) := by
  induction A with
  | atom p => exact Conv.refl _
  | @bind Γ σ ρ A ih =>
      change Conv (Term.forall' (toC (diagram A
        (ModalComprehensionConcreteSyntax.Term.app H.wk (.var .zero)))))
        (Term.forall' (coextC ρ (.app (toC H).weaken (.var .zero))
          (.app (Term.lam (bodyWitness A)).weaken (.var .zero))))
      apply Conv.app_congr (Conv.refl _)
      apply Conv.lam_congr
      have hi := ih (ModalComprehensionConcreteSyntax.Term.app H.wk (.var .zero))
      simp only [toC, toC_wk, toCVar] at hi
      exact Conv.trans hi (coextC_conv ρ (Conv.refl _)
        (Conv.symm (c_beta_fresh (bodyWitness A))))

theorem code_to_coext {Γ} {ρ : RTy} (A : SourceBody Const Γ ρ) :
    Conv (toC (ModalComprehensionConcreteSyntax.Body.code A))
      (Term.box (coextC ρ (.var .zero) (bodyWitness A).weaken)) := by
  apply Conv.trans (toC_box _)
  have hd := diagram_to_coext
    (A.rename ModalComprehensionConcreteSyntax.Ren.shift)
    (ModalComprehensionConcreteSyntax.Term.var .zero)
  rw [bodyWitness_rename, toCRen_shift] at hd
  exact Conv.app_congr (Conv.app_congr (Conv.refl _) hd) (Conv.refl _)

/-- The exact translated strong-comprehension instance is a C theorem. -/
theorem c_comprehension {Γ} {ρ : RTy} (A : SourceBody Const Γ ρ) :
    C.Derivable [] (toC (.ex (ModalComprehensionConcreteSyntax.Body.code A))) := by
  let W := bodyWitness A
  have hx : C.Derivable [] (Term.exists'
      (Term.box (coextC ρ (.var .zero) W.weaken))) := by
    apply Classicism.Meta.Derivable.exIβ W
    have hr := c_nec (coextC_refl ρ W)
    simpa only [Term.instantiate, Term.box, Term.eq', Term.subst_app,
      Term.subst_eq, coextC_subst, Term.subst_var, Sub.cons_zero,
      Term.subst_rename, Sub.compRen_cons_shift, Term.subst_id,
      Term.top, Term.disj, Term.neg, Term.forall', Term.subst_or,
      Term.subst_not, Term.subst_all, Term.subst_lam, Sub.lift_zero] using hr
  exact Classicism.Meta.Derivable.conv hx (Conv.symm
    (Conv.app_congr (Conv.refl _) (Conv.lam_congr (code_to_coext A))))

theorem toC_hyps_wk {Γ σ} (Δ : List (SourceTerm Const Γ Ty.t)) :
    (Δ.map (fun p => p.wk (σ := σ))).map toC = Hyps.weaken (Δ.map toC) := by
  simp only [Hyps.weaken, List.map_map]
  congr 1
  funext p
  exact toC_wk p

/-- Every actual source proof is translated. The only parameter for extra
global axioms concerns those extra axiom instances, not arbitrary proofs. -/
theorem derives_toC {Ax : SourceAxioms Const}
    (axioms : ∀ Γ p, Ax Γ p → C.Derivable [] (toC p))
    {Γ Δ p} (h : SourceProof Const Ax Γ Δ p) :
    C.Derivable (Δ.map toC) (toC p) := by
  induction h with
  | hyp h => exact Classicism.Meta.Derivable.hyp (List.mem_map.mpr ⟨_, h, rfl⟩)
  | ax h => exact Classicism.Meta.Derivable.weaken (axioms _ _ h) (List.nil_subset _)
  | weaken sub _ ih => exact Classicism.Meta.Derivable.weaken ih (List.map_subset_of_subset _ sub)
  | impI _ ih => exact Classicism.Meta.Derivable.impI ih
  | impE _ _ ih₁ ih₂ => exact Classicism.Meta.Derivable.impE ih₁ ih₂
  | iffI _ _ ih₁ ih₂ => exact Classicism.Meta.Derivable.andI ih₁ ih₂
  | iffE₁ _ _ ih₁ ih₂ => exact Classicism.Meta.Derivable.iffE₁ ih₁ ih₂
  | iffE₂ _ _ ih₁ ih₂ => exact Classicism.Meta.Derivable.iffE₂ ih₁ ih₂
  | topI => exact Classicism.Meta.Derivable.top
  | eqRefl a => exact Classicism.Meta.Derivable.refl (toC a)
  | eqSymm _ ih => exact Classicism.Meta.Derivable.eqSymm ih
  | eqTrans _ _ ih₁ ih₂ => exact Classicism.Meta.Derivable.eqTrans ih₁ ih₂
  | @eqApp Γ Δ σ ρ f g a b _ _ ih₁ ih₂ =>
      exact Classicism.Meta.Derivable.eqTrans (Classicism.Meta.Derivable.eqCongrFun ih₁ (toC a)) (Classicism.Meta.Derivable.eqCongr (toC g) ih₂)
  | eqRight a _ ih => exact Classicism.Meta.Derivable.eqCongr (.app (.eq _) (toC a)) ih
  | eqTruth _ _ ih₁ ih₂ => exact Classicism.Meta.Derivable.eqMp ih₁ ih₂
  | eqSubst P a b _ _ ihEq ihP =>
      rw [toC_inst] at ihP ⊢
      exact Classicism.Meta.Derivable.llβ (toC P) ihEq ihP
  | @allI Γ Δ σ P _ ih =>
      apply Classicism.Meta.Derivable.allI
      simpa only [toC_hyps_wk] using ih
  | allE a _ ih =>
      rw [toC_inst]
      exact Classicism.Meta.Derivable.allEβ ih (toC a)
  | exI a _ ih =>
      rw [toC_inst] at ih
      exact Classicism.Meta.Derivable.exIβ (toC a) ih
  | @exE Γ Δ σ P q _ _ ihEx ihQ =>
      have hq : C.Derivable (toC P :: Hyps.weaken (Δ.map toC)) (toC q).weaken := by
        simpa only [List.map_cons, toC_hyps_wk, toC_wk] using ihQ
      apply Classicism.Meta.Derivable.exE ihEx
      have hp : C.Derivable
          (.app (Term.lam (toC P)).weaken (.var .zero) :: Hyps.weaken (Δ.map toC))
          (toC P) := Classicism.Meta.Derivable.conv Classicism.Meta.Derivable.hyp₀ (c_beta_fresh (toC P))
      exact Classicism.Meta.Derivable.impE (Classicism.Meta.Derivable.weaken₁ (Classicism.Meta.Derivable.impI hq)) hp
  | nec _ ih => exact Classicism.Meta.Derivable.conv (c_nec ih) (Conv.symm (toC_box _))
  | K _ _ ih₁ ih₂ =>
      exact Classicism.Meta.Derivable.conv (c_K (Classicism.Meta.Derivable.conv ih₁ (toC_box _))
        (Classicism.Meta.Derivable.conv ih₂ (toC_box _))) (Conv.symm (toC_box _))
  | intensionality ρ a b _ ih =>
      have hh := Classicism.Meta.Derivable.conv ih (toC_box _)
      rw [toC_coext] at hh
      exact c_intensionality ρ (toC a) (toC b) hh
  | comprehension A => exact Classicism.Meta.Derivable.weaken (c_comprehension A) (List.nil_subset _)

/-- Unconditional one-way proof translation for the entire stipulated
lambda-free positive K/Nec/I/SC calculus. No lambda is assumed in its source. -/
theorem base_derives_toC {Γ Δ p}
    (h : SourceProof Const (ModalComprehensionConcreteSyntax.noAdditionalAxioms Const)
      Γ Δ p) : C.Derivable (Δ.map toC) (toC p) :=
  derives_toC (fun _ _ h => h.elim) h

#print axioms c_comprehension
#print axioms derives_toC
#print axioms base_derives_toC

end Classicism.Research.ModalConcreteToC
