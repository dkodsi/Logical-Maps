import Classicism.Results.Research.RelationalCompiledContexts
import Classicism.Results.Research.ModalLogicalOperatorLaws

/-!
# Transport of the actual C proof constructors to named lambda-free syntax

Original research, misc, 23 October 2026. All propositional, quantified,
equality and contextual Subst rules below are derived in the concrete
lambda-free calculus with the displayed conservative definitions. No
object rule is replaced by a Lean implication between shallow propositions.

The final theorem is temporarily parameterized only by the explicit delta
identities, whose independent construction is a separate module. This
source does not assert that finite-name erasure or round trips are complete.
-/

namespace Classicism.Research.RelationalCProofTransport
open Classicism.Meta (Ty RTy Ctx Signature)
open ModalComprehensionConcreteSyntax (Derives Term Formula neg conjunction disjunction)
open ModalLogicalOperators (Constants ExpandedNamedAxiom containsClassical)
open RelationalCompiledContexts (translate TargetTerm)

variable {Sig : Signature}

abbrev Proof (Γ : Ctx) (Δ : List (Formula (Constants Sig) Γ))
    (p : Formula (Constants Sig) Γ) :=
  Derives (Constants Sig) (ExpandedNamedAxiom Sig) Γ Δ p

theorem containsBasis : RelationalCompiledContexts.ContainsBasis (ExpandedNamedAxiom Sig) :=
  fun _ _ h => .basis h

theorem fresh_application_inst {Γ σ}
    (F : TargetTerm Sig Γ (σ ⇒ RTy.t)) (a : TargetTerm Sig Γ σ) :
    (Term.app F.wk (.var .zero)).inst a = .app F a := by
  change Term.app (F.wk.inst a) a = Term.app F a
  rw [Term.inst_wk]

theorem ex_identity {Γ σ} {P Q : Formula (Constants Sig) (σ :: Γ)}
    (h : Proof (σ :: Γ) [] (.eq P Q)) :
    Proof Γ [] (.eq (.ex P) (.ex Q)) := by
  apply ModalClassicalRules.equivalence_identity
  · apply Derives.exE Derives.hyp₀
    have hq : Proof (σ :: Γ) [P, (Term.ex P).wk] Q :=
      .eqTruth h.lift .hyp₀
    have hu : Proof (σ :: Γ) [P, (Term.ex P).wk]
        (.ex (Q.rename (ModalComprehensionConcreteSyntax.Ren.lift
          (ModalComprehensionConcreteSyntax.Ren.shift (σ := σ))))) := by
      apply Derives.exI (.var .zero)
      rw [Derives.instantiate_at_fresh]
      exact hq
    exact hu
  · apply Derives.exE Derives.hyp₀
    have hp : Proof (σ :: Γ) [Q, (Term.ex Q).wk] P :=
      .eqTruth (Derives.eqSymm h).lift .hyp₀
    have hu : Proof (σ :: Γ) [Q, (Term.ex Q).wk]
        (.ex (P.rename (ModalComprehensionConcreteSyntax.Ren.lift
          (ModalComprehensionConcreteSyntax.Ren.shift (σ := σ))))) := by
      apply Derives.exI (.var .zero)
      rw [Derives.instantiate_at_fresh]
      exact hp
    exact hu

/-- Explicit syntax bridges let subsequent proof induction infer original
C arguments before unfolding the compiled logical constants. -/
theorem tr_and {Γ Δ} (p q : Classicism.Meta.Formula Sig Γ) :
    Proof Γ Δ (.eq (translate (.conj p q)) (conjunction (translate p) (translate q))) := by
  simpa only [Classicism.Meta.Term.conj, translate, RelationalLambdaCompilation.compile,
    RelationalBracketInterpretation.embed, ModalLogicalOperators.named,
    ModalLogicalOperators.LogicalOperator.atom] using
    (ModalLogicalOperators.named_and (Δ := Δ) (translate p) (translate q))

theorem tr_or {Γ Δ} (p q : Classicism.Meta.Formula Sig Γ) :
    Proof Γ Δ (.eq (translate (.disj p q)) (disjunction (translate p) (translate q))) := by
  simpa only [Classicism.Meta.Term.disj, translate, RelationalLambdaCompilation.compile,
    RelationalBracketInterpretation.embed, ModalLogicalOperators.named,
    ModalLogicalOperators.LogicalOperator.atom] using
    (ModalLogicalOperators.named_or (Δ := Δ) (translate p) (translate q))

theorem tr_not {Γ Δ} (p : Classicism.Meta.Formula Sig Γ) :
    Proof Γ Δ (.eq (translate (.neg p)) (neg (translate p))) := by
  simpa only [Classicism.Meta.Term.neg, translate, RelationalLambdaCompilation.compile,
    RelationalBracketInterpretation.embed, ModalLogicalOperators.named,
    ModalLogicalOperators.LogicalOperator.atom] using
    (ModalLogicalOperators.named_not (Δ := Δ) (translate p))

theorem tr_eq {Γ Δ σ} (a b : Classicism.Meta.Term Sig Γ σ) :
    Proof Γ Δ (.eq (translate (.eq' a b)) (.eq (translate a) (translate b))) := by
  simpa only [Classicism.Meta.Term.eq', translate, RelationalLambdaCompilation.compile,
    RelationalBracketInterpretation.embed, ModalLogicalOperators.named,
    ModalLogicalOperators.LogicalOperator.atom] using
    (ModalLogicalOperators.named_eq (Δ := Δ) (translate a) (translate b))

theorem tr_all {Γ Δ σ} (F : Classicism.Meta.Term Sig Γ (σ ⇒ RTy.t)) :
    Proof Γ Δ (.eq (translate (.app (.all σ) F))
      (.all (.app (translate F).wk (.var .zero)))) := by
  simpa only [translate, RelationalLambdaCompilation.compile,
    RelationalBracketInterpretation.embed, ModalLogicalOperators.named,
    ModalLogicalOperators.LogicalOperator.atom] using
    (ModalLogicalOperators.named_all (Δ := Δ) (translate F))

theorem tr_ex {Γ Δ σ} (F : Classicism.Meta.Term Sig Γ (σ ⇒ RTy.t)) :
    Proof Γ Δ (.eq (translate (.app (.ex σ) F))
      (.ex (.app (translate F).wk (.var .zero)))) := by
  simpa only [translate, RelationalLambdaCompilation.compile,
    RelationalBracketInterpretation.embed, ModalLogicalOperators.named,
    ModalLogicalOperators.LogicalOperator.atom] using
    (ModalLogicalOperators.named_ex (Δ := Δ) (translate F))

theorem forall_lam_identity {Γ σ} (b : Classicism.Meta.Formula Sig (σ :: Γ)) :
    Proof Γ [] (.eq (translate (Classicism.Meta.Term.forall' b)) (.all (translate b))) := by
  apply Derives.eqTrans (tr_all (.lam b))
  apply ModalClassicalRules.all_identity
  exact ModalLogicalOperators.lift_basis
    (RelationalBracketInterpretation.bracket_fresh_beta_derives
      (RelationalLambdaCompilation.compile b))

theorem exists_lam_identity {Γ σ} (b : Classicism.Meta.Formula Sig (σ :: Γ)) :
    Proof Γ [] (.eq (translate (Classicism.Meta.Term.exists' b)) (.ex (translate b))) := by
  apply Derives.eqTrans (tr_ex (.lam b))
  apply ex_identity
  exact ModalLogicalOperators.lift_basis
    (RelationalBracketInterpretation.bracket_fresh_beta_derives
      (RelationalLambdaCompilation.compile b))

theorem translated_hyps_weaken {Γ σ} (Δ : List (Classicism.Meta.Formula Sig Γ)) :
    (Classicism.Meta.Hyps.weaken (σ := σ) Δ).map translate =
      (Δ.map translate).map (fun p => p.wk (σ := σ)) := by
  simp only [Classicism.Meta.Hyps.weaken, List.map_map]
  congr 1
  funext p
  exact RelationalCompiledContexts.translate_weaken p

theorem existence_e_translate {Γ} :
    Proof Γ [] (translate ((Classicism.Meta.existence_e (Sig := Sig)).close (Γ := Γ))) := by
  have he : Proof (Sig := Sig) Γ [] (Term.ex (Term.eq
      (Term.var (.zero : ModalComprehensionConcreteSyntax.Var (Ty.e :: Γ) Ty.e))
      (Term.var .zero))) := .ax (.classical .exists_e)
  have heq : Proof (Sig := Sig) Γ [] (.eq
      (.ex (translate (Classicism.Meta.Term.eq'
        (Classicism.Meta.Term.var (.zero : Classicism.Meta.Var (Ty.e :: Γ) Ty.e))
        (.var .zero))))
      (Term.ex (σ := Ty.e) (.eq (.var .zero) (.var .zero)))) := by
    apply ex_identity
    simpa only [translate, RelationalLambdaCompilation.compile,
      RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar] using
      (tr_eq (Sig := Sig) (Γ := Ty.e :: Γ) (Δ := [])
        (.var (.zero : Classicism.Meta.Var (Ty.e :: Γ) Ty.e)) (.var .zero))
  exact Derives.eqTruth (Derives.eqSymm (Derives.eqTrans
    (exists_lam_identity _) heq)) he

/-- Proof induction over the existing C derivation relation, including its
logical-axiom restriction in both recursive premises of Subst. The supplied
delta equations concern only term syntax; no proof-transport premise occurs. -/
theorem derivable_translate_of_delta
    (delta : ∀ {Γ σ} {a b : Classicism.Meta.Term Sig Γ σ},
      a.unfoldR = some b → Proof Γ [] (.eq (translate a) (translate b)))
    {Ax : Classicism.Meta.AxiomSet Sig} {Γ Δ p}
    (h : Classicism.Meta.Derivable Ax (Γ := Γ) Δ p)
    (logicalOnly : ∀ a, Ax a → Classicism.Meta.Logical a) :
    Proof Γ (Δ.map translate) (translate p) := by
  revert logicalOnly
  induction h with
  | hyp hm =>
      intro _
      exact .hyp (List.mem_map.mpr ⟨_, hm, rfl⟩)
  | ax ha =>
      intro hl
      have he := hl _ ha
      cases he
      exact existence_e_translate.lift
  | andI _ _ ih₁ ih₂ =>
      intro hl
      exact .eqTruth (Derives.eqSymm (tr_and _ _))
        (ModalClassicalRules.conjunctionI (ih₁ hl) (ih₂ hl))
  | andE₁ _ ih =>
      intro hl
      exact ModalClassicalRules.conjunctionE₁ containsClassical
        (.eqTruth (tr_and _ _) (ih hl))
  | andE₂ _ ih =>
      intro hl
      exact ModalClassicalRules.conjunctionE₂ containsClassical
        (.eqTruth (tr_and _ _) (ih hl))
  | orI₁ _ ih =>
      intro hl
      exact .eqTruth (Derives.eqSymm (tr_or _ _))
        (ModalClassicalRules.disjunctionI₁ (ih hl))
  | orI₂ _ ih =>
      intro hl
      exact .eqTruth (Derives.eqSymm (tr_or _ _))
        (ModalClassicalRules.disjunctionI₂ (ih hl))
  | orE _ _ _ ih ih₁ ih₂ =>
      intro hl
      exact ModalClassicalRules.disjunctionE containsClassical
        (.eqTruth (tr_or _ _) (ih hl)) (ih₁ hl) (ih₂ hl)
  | notI _ _ ih₁ ih₂ =>
      intro hl
      exact .eqTruth (Derives.eqSymm (tr_not _))
        (ModalClassicalRules.negI (ih₁ hl)
          (.eqTruth (tr_not _) (ih₂ hl)))
  | notE _ _ ih₁ ih₂ =>
      intro hl
      exact ModalClassicalRules.negE _ (ih₁ hl)
        (.eqTruth (tr_not _) (ih₂ hl))
  | em p =>
      intro _
      have hn := tr_not (Δ := []) p
      have ho := tr_or (Δ := []) p (Classicism.Meta.Term.neg p)
      have hd : Proof _ [] (disjunction (translate p) (translate (Classicism.Meta.Term.neg p))) := by
        apply Derives.impI
        exact .eqTruth (Derives.eqSymm hn).lift .hyp₀
      exact (Derives.eqTruth (.eqSymm ho) hd).lift
  | allE _ a ih =>
      intro hl
      have hu := Derives.eqTruth (tr_all _) (ih hl)
      have ha := Derives.allE (translate a) hu
      simpa only [fresh_application_inst, translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed] using ha
  | allI _ ih =>
      intro hl
      apply Derives.eqTruth (Derives.eqSymm (forall_lam_identity _)).lift
      apply Derives.allI
      simpa only [translated_hyps_weaken] using ih hl
  | exI a _ ih =>
      intro hl
      apply Derives.eqTruth (Derives.eqSymm (tr_ex _))
      apply Derives.exI (translate a)
      simpa only [fresh_application_inst, translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed] using ih hl
  | @exE A Γ Δ σ F r _ _ ih ih' =>
      intro hl
      apply Derives.exE (Derives.eqTruth (tr_ex _) (ih hl))
      simpa only [List.map_cons, translated_hyps_weaken,
        RelationalCompiledContexts.translate_weaken, translate,
        RelationalLambdaCompilation.compile,
        RelationalLambdaCompilation.compile_weaken,
        RelationalBracketInterpretation.embed,
        RelationalBracketInterpretation.embed_wk,
        RelationalBracketInterpretation.embedVar] using ih' hl
  | refl a =>
      intro _
      exact .eqTruth (Derives.eqSymm (tr_eq _ _)) (.eqRefl _)
  | ll F _ _ ih₁ ih₂ =>
      intro hl
      have he := Derives.eqTruth (tr_eq _ _) (ih₁ hl)
      have hf := ih₂ hl
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed] at hf ⊢
      exact .eqTruth (.eqApp (.eqRefl (translate F)) he) hf
  | conv _ hc ih =>
      intro hl
      exact .eqTruth (RelationalCompiledContexts.conversion_identity containsBasis delta hc).lift (ih hl)
  | subst H _ _ _ ih₁ ih₂ ih =>
      intro hl
      exact RelationalCompiledContexts.contextual_subst containsBasis H
        (ih₁ (fun _ ha => ha.2)) (ih₂ (fun _ ha => ha.2)) (ih hl)

#print axioms ex_identity
#print axioms forall_lam_identity
#print axioms exists_lam_identity
#print axioms existence_e_translate
#print axioms derivable_translate_of_delta

end Classicism.Research.RelationalCProofTransport
