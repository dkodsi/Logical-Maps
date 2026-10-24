import Classicism.Results.Research.ModalNamedCDefinitions

/-!
# Actual proof transport from the named reconstruction into C

Original research, misc, 23 October 2026. Direct source:
`lambda-free-classicism-reconstruction-proof.txt`, sections 3, 5, 7 and 8.

The interpretation j+ has already been defined term by term, and its global
name definitions have actual C proofs. This module supplies its concrete
substitution algebra and a finite-lambda witness for every SC instance,
then transports every constructor of the ACTUAL native Derives relation.
The final named_derives_toC theorem has no axiom-preservation hypothesis.
Optional local premises remain local; necessitation is used only on the
translated empty-local-premise proof of the source Nec constructor.
-/

namespace Classicism.Research.ModalNamedToC
open Classicism.Meta
open ModalConcreteToC (signature SourceSub SourceRen SourceProof SourceAxioms
  fromCVar fromCVar_toCVar toCVar toCVar_fromCVar toCRen toCRen_lift toCRen_shift
  coextC coextC_subst coextC_refl c_beta_fresh c_nec c_K c_intensionality)
open ModalFiniteNameSupport (NamedConst NamedAxioms)
open ModalReconstructionNames (Name closedBody)
open ModalComprehensionRepresentation (diagram)

variable {Const : Ty → Type}

/-- Assigned name values are closed, so substitution cannot alter them. -/
theorem constantValue_subst {Γ Θ σ} (s : Sub (signature Const) Γ Θ)
    (c : NamedConst Const Name σ) :
    (constantValue (Γ := Γ) c).subst s = constantValue (Γ := Θ) c := by
  rw [constantValue_join, constantValue_join]
  exact RelationalLambdaDecoding.decodeBasis_subst s _

def jPlusSub {Γ Δ} (s : SourceSub (NamedConst Const Name) Γ Δ) : Sub (signature Const) Γ Δ :=
  fun _ v => jPlus (s (fromCVar v))

theorem jPlusSub_lift {Γ Δ σ} (s : SourceSub (NamedConst Const Name) Γ Δ) :
    jPlusSub (ModalComprehensionConcreteSyntax.Sub.lift (σ := σ) s) =
      Sub.lift (jPlusSub s) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v => exact jPlus_wk (s (fromCVar v))

theorem jPlus_subst {Γ Δ σ} (s : SourceSub (NamedConst Const Name) Γ Δ) (a : NamedTerm (Const := Const) Γ σ) :
    jPlus (a.subst s) = (jPlus a).subst (jPlusSub s) := by
  induction a generalizing Δ with
  | var v =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, jPlus,
        Term.subst_var, jPlusSub, fromCVar_toCVar]
  | const c => exact (constantValue_subst (jPlusSub s) c).symm
  | app f a ihf iha =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, jPlus,
        Term.subst_app, ihf, iha]
  | top => rfl
  | imp p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, jPlus,
        Term.imp, Term.disj, Term.neg, Term.subst_app, Term.subst_or,
        Term.subst_not, ihp, ihq]
  | iff p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, jPlus,
        Term.iff, Term.conj, Term.imp, Term.disj, Term.neg, Term.subst_app,
        Term.subst_and, Term.subst_or, Term.subst_not, ihp, ihq]
  | eq a b iha ihb =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, jPlus,
        Term.eq', Term.subst_app, Term.subst_eq, iha, ihb]
  | boxOp => rfl
  | all p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, jPlus,
        Term.forall', Term.subst_app, Term.subst_all, Term.subst_lam,
        ih, jPlusSub_lift]
  | ex p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, jPlus,
        Term.exists', Term.subst_app, Term.subst_ex, Term.subst_lam,
        ih, jPlusSub_lift]

theorem jPlusSub_cons_id {Γ σ} (a : NamedTerm (Const := Const) Γ σ) :
    jPlusSub (ModalComprehensionConcreteSyntax.Sub.cons a
      ModalComprehensionConcreteSyntax.Sub.id) = Sub.cons (jPlus a) Sub.id := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v =>
      simp only [jPlusSub, fromCVar, ModalComprehensionConcreteSyntax.Sub.cons,
        ModalComprehensionConcreteSyntax.Sub.id, jPlus, toCVar_fromCVar,
        Sub.cons_succ, Sub.id]

theorem jPlus_inst {Γ σ τ} (p : NamedTerm (Const := Const) (σ :: Γ) τ)
    (a : NamedTerm (Const := Const) Γ σ) : jPlus (p.inst a) = (jPlus p).instantiate (jPlus a) := by
  rw [ModalComprehensionConcreteSyntax.Term.inst, jPlus_subst, jPlusSub_cons_id]
theorem jPlus_coext (ρ : RTy) : ∀ {Γ} (p q : NamedTerm (Const := Const) Γ ρ),
    jPlus (ModalComprehensionConcreteSyntax.Term.coext ρ p q) =
      coextC ρ (jPlus p) (jPlus q) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [ModalComprehensionConcreteSyntax.Term.coext, jPlus, coextC,
        ih, jPlus_wk, toCVar]

theorem jBodyWitness_rename {Γ Θ} {ρ : RTy}
    (r : SourceRen Γ Θ) (A : NamedBody (Const := Const) Γ ρ) :
    jBodyWitness (A.rename r) = (jBodyWitness A).rename (toCRen r) := by
  induction A generalizing Θ with
  | atom p => exact jPlus_rename r p
  | bind A ih =>
      change Term.lam (jBodyWitness (ModalComprehensionConcreteSyntax.Body.rename
        (ModalComprehensionConcreteSyntax.Ren.lift r) A)) =
        Term.lam ((jBodyWitness A).rename (Ren.lift (toCRen r)))
      rw [ih, toCRen_lift]

/-- The matrix of the ACTUAL finite-body comprehension instance. -/
theorem jPlus_code_coext {Γ} {ρ : RTy} (A : NamedBody (Const := Const) Γ ρ) :
    Conv (jPlus (ModalComprehensionConcreteSyntax.Body.code A))
      (Term.box (coextC ρ (.var .zero) (jBodyWitness A).weaken)) := by
  apply Conv.trans (jPlus_box _)
  have hd := jPlus_diagram
    (A.rename ModalComprehensionConcreteSyntax.Ren.shift)
    (ModalComprehensionConcreteSyntax.Term.var .zero)
  rw [jBodyWitness_rename, toCRen_shift] at hd
  exact Conv.app_congr (Conv.app_congr (Conv.refl _) hd) (Conv.refl _)

/-- A finite target lambda term is a witness; no source witness or object
choice function is postulated. -/
theorem c_named_comprehension {Γ} {ρ : RTy} (A : NamedBody (Const := Const) Γ ρ) :
    C.Derivable [] (jPlus (.ex (ModalComprehensionConcreteSyntax.Body.code A))) := by
  let W := jBodyWitness A
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
    (Conv.app_congr (Conv.refl _) (Conv.lam_congr (jPlus_code_coext A))))

theorem jPlus_hyps_wk {Γ σ} (Δ : List (NamedTerm (Const := Const) Γ Ty.t)) :
    (Δ.map (fun p => p.wk (σ := σ))).map jPlus = Hyps.weaken (Δ.map jPlus) := by
  simp only [Hyps.weaken, List.map_map]
  congr 1
  funext p
  exact jPlus_wk p

/-- Full induction on actual source derivations. The intermediate axiom
argument concerns individual global instances, never arbitrary proofs. -/
theorem derives_jPlus {Ax : SourceAxioms (NamedConst Const Name)}
    (axioms : ∀ Γ p, Ax Γ p → C.Derivable [] (jPlus p))
    {Γ Δ p} (h : SourceProof (NamedConst Const Name) Ax Γ Δ p) :
    C.Derivable (Δ.map jPlus) (jPlus p) := by
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
  | eqRefl a => exact Classicism.Meta.Derivable.refl (jPlus a)
  | eqSymm _ ih => exact Classicism.Meta.Derivable.eqSymm ih
  | eqTrans _ _ ih₁ ih₂ => exact Classicism.Meta.Derivable.eqTrans ih₁ ih₂
  | @eqApp Γ Δ σ ρ f g a b _ _ ih₁ ih₂ =>
      exact Classicism.Meta.Derivable.eqTrans (Classicism.Meta.Derivable.eqCongrFun ih₁ (jPlus a)) (Classicism.Meta.Derivable.eqCongr (jPlus g) ih₂)
  | eqRight a _ ih => exact Classicism.Meta.Derivable.eqCongr (.app (.eq _) (jPlus a)) ih
  | eqTruth _ _ ih₁ ih₂ => exact Classicism.Meta.Derivable.eqMp ih₁ ih₂
  | eqSubst P a b _ _ ihEq ihP =>
      rw [jPlus_inst] at ihP ⊢
      exact Classicism.Meta.Derivable.llβ (jPlus P) ihEq ihP
  | @allI Γ Δ σ P _ ih =>
      apply Classicism.Meta.Derivable.allI
      simpa only [jPlus_hyps_wk] using ih
  | allE a _ ih =>
      rw [jPlus_inst]
      exact Classicism.Meta.Derivable.allEβ ih (jPlus a)
  | exI a _ ih =>
      rw [jPlus_inst] at ih
      exact Classicism.Meta.Derivable.exIβ (jPlus a) ih
  | @exE Γ Δ σ P q _ _ ihEx ihQ =>
      have hq : C.Derivable (jPlus P :: Hyps.weaken (Δ.map jPlus)) (jPlus q).weaken := by
        simpa only [List.map_cons, jPlus_hyps_wk, jPlus_wk] using ihQ
      apply Classicism.Meta.Derivable.exE ihEx
      have hp : C.Derivable
          (.app (Term.lam (jPlus P)).weaken (.var .zero) :: Hyps.weaken (Δ.map jPlus))
          (jPlus P) := Classicism.Meta.Derivable.conv Classicism.Meta.Derivable.hyp₀ (c_beta_fresh (jPlus P))
      exact Classicism.Meta.Derivable.impE (Classicism.Meta.Derivable.weaken₁ (Classicism.Meta.Derivable.impI hq)) hp
  | nec _ ih => exact Classicism.Meta.Derivable.conv (c_nec ih) (Conv.symm (jPlus_box _))
  | K _ _ ih₁ ih₂ =>
      exact Classicism.Meta.Derivable.conv (c_K (Classicism.Meta.Derivable.conv ih₁ (jPlus_box _))
        (Classicism.Meta.Derivable.conv ih₂ (jPlus_box _))) (Conv.symm (jPlus_box _))
  | intensionality ρ a b _ ih =>
      have hh := Classicism.Meta.Derivable.conv ih (jPlus_box _)
      rw [jPlus_coext] at hh
      exact c_intensionality ρ (jPlus a) (jPlus b) hh
  | comprehension A => exact Classicism.Meta.Derivable.weaken (c_named_comprehension A) (List.nil_subset _)

/-- Every derivation in the full named extension has an actual C derivation
under its explicit interpretation. All global axiom obligations are discharged. -/
theorem named_derives_toC {Γ Δ p}
    (h : SourceProof (NamedConst Const Name) (NamedAxioms (closedBody Const)) Γ Δ p) :
    C.Derivable (Δ.map jPlus) (jPlus p) :=
  derives_jPlus (fun _ _ h => named_axioms_toC h) h

#print axioms constantValue_subst
#print axioms jPlus_subst
#print axioms jPlus_inst
#print axioms jPlus_coext
#print axioms c_named_comprehension
#print axioms derives_jPlus
#print axioms named_derives_toC

end Classicism.Research.ModalNamedToC
