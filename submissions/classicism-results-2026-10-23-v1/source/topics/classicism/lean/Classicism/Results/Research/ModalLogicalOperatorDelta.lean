import Classicism.Results.Research.RelationalCProofTransport

/-!
# Every raw relational delta generator has a lambda-free identity proof

Original research, misc, 23 October 2026. The application-level laws of the
independent logical definitions are connected here to the ACTUAL
`Classicism.Meta.Term.unfoldR`. Propositional abbreviations in those raw
unfoldings are compared by classical object proofs, not treated as syntax
identities. Theorem zeta closes the fresh-argument equations; no optional
premise enters a necessitation step.

The final derivation theorem discharges the explicit delta obligation of
RelationalCProofTransport. It is a translation into the named extension;
finite-name erasure and the old-language round trip are separate results.
-/

namespace Classicism.Research.ModalLogicalOperators
open Classicism.Meta (Ty RTy Signature)
open ModalComprehensionConcreteSyntax
open RelationalCompiledContexts (translate TargetTerm)
open RelationalCProofTransport (Proof forall_lam_identity)

variable {Sig : Signature}

/-- The classical definition `¬¬p → q` has the same intension as `p → q`.
Both directions are discharged before Intensionality is invoked. -/
theorem disjunction_neg_identity {Γ} (p q : Formula (Constants Sig) Γ) :
    Proof Γ [] (.eq (disjunction (neg p) q) (.imp p q)) := by
  apply ModalClassicalRules.equivalence_identity
  · apply Derives.impI
    apply Derives.impE Derives.hyp₁
    exact Derives.impI (Derives.impE Derives.hyp₀ Derives.hyp₁)
  · apply Derives.impI
    exact Derives.impE Derives.hyp₁
      (ModalClassicalRules.dne containsClassical p Derives.hyp₀)

theorem conjunction_iff_identity {Γ} (p q : Formula (Constants Sig) Γ) :
    Proof Γ [] (.eq (conjunction (.imp p q) (.imp q p)) (.iff p q)) := by
  apply ModalClassicalRules.equivalence_identity
  · exact Derives.iffI
      (ModalClassicalRules.conjunctionE₁ containsClassical Derives.hyp₀)
      (ModalClassicalRules.conjunctionE₂ containsClassical Derives.hyp₀)
  · exact ModalClassicalRules.conjunctionI
      (Derives.impI (Derives.iffE₁ Derives.hyp₁ Derives.hyp₀))
      (Derives.impI (Derives.iffE₂ Derives.hyp₁ Derives.hyp₀))

theorem tr_imp_identity {Γ} (p q : Classicism.Meta.Formula Sig Γ) :
    Proof Γ [] (.eq (translate (Classicism.Meta.Term.imp p q))
      (.imp (translate p) (translate q))) := by
  simpa only [Classicism.Meta.Term.imp, Classicism.Meta.Term.iff, Classicism.Meta.Term.conj,
    Classicism.Meta.Term.disj, Classicism.Meta.Term.neg, Classicism.Meta.Term.top,
    Classicism.Meta.Term.box, Classicism.Meta.Term.eq', translate,
    RelationalLambdaCompilation.compile, RelationalBracketInterpretation.embed,
    named, LogicalOperator.atom] using Derives.eqTrans
    (Derives.eqApp
      (Derives.eqApp (Derives.eqRefl (named .or)) (named_not (translate p)))
      (Derives.eqRefl (translate q)))
    (Derives.eqTrans (named_or (neg (translate p)) (translate q))
      (disjunction_neg_identity (translate p) (translate q)))

theorem tr_iff_identity {Γ} (p q : Classicism.Meta.Formula Sig Γ) :
    Proof Γ [] (.eq (translate (Classicism.Meta.Term.iff p q))
      (.iff (translate p) (translate q))) := by
  simpa only [Classicism.Meta.Term.imp, Classicism.Meta.Term.iff, Classicism.Meta.Term.conj,
    Classicism.Meta.Term.disj, Classicism.Meta.Term.neg, Classicism.Meta.Term.top,
    Classicism.Meta.Term.box, Classicism.Meta.Term.eq', translate,
    RelationalLambdaCompilation.compile, RelationalBracketInterpretation.embed,
    named, LogicalOperator.atom] using Derives.eqTrans
    (Derives.eqApp
      (Derives.eqApp (Derives.eqRefl (named .and)) (tr_imp_identity p q))
      (tr_imp_identity q p))
    (Derives.eqTrans
      (named_and (.imp (translate p) (translate q)) (.imp (translate q) (translate p)))
      (conjunction_iff_identity (translate p) (translate q)))

theorem tr_top_identity {Γ} :
    Proof (Sig := Sig) Γ [] (.eq (translate Classicism.Meta.Term.top) .top) := by
  let X : Formula (Constants Sig) Γ :=
    translate (Classicism.Meta.Term.forall' (Classicism.Meta.Term.var .zero))
  have hem : Proof Γ [] (.eq (disjunction X (neg X)) .top) :=
    ModalClassicalRules.equivalence_identity Derives.topI
      (ModalClassicalRules.excludedMiddle X)
  simpa only [Classicism.Meta.Term.imp, Classicism.Meta.Term.iff, Classicism.Meta.Term.conj,
    Classicism.Meta.Term.disj, Classicism.Meta.Term.neg, Classicism.Meta.Term.top,
    Classicism.Meta.Term.box, Classicism.Meta.Term.eq', translate,
    RelationalLambdaCompilation.compile, RelationalBracketInterpretation.embed,
    named, LogicalOperator.atom, X] using Derives.eqTrans
    (Derives.eqApp (Derives.eqRefl (.app (named .or) X)) (named_not X))
    (Derives.eqTrans (named_or X (neg X)) hem)

theorem tr_box_identity {Γ} (p : Classicism.Meta.Formula Sig Γ) :
    Proof Γ [] (.eq (translate (Classicism.Meta.Term.box p))
      (.eq (translate p) .top)) := by
  simpa only [Classicism.Meta.Term.imp, Classicism.Meta.Term.iff, Classicism.Meta.Term.conj,
    Classicism.Meta.Term.disj, Classicism.Meta.Term.neg, Classicism.Meta.Term.top,
    Classicism.Meta.Term.box, Classicism.Meta.Term.eq', translate,
    RelationalLambdaCompilation.compile, RelationalBracketInterpretation.embed,
    named, LogicalOperator.atom] using Derives.eqTrans
    (Derives.eqApp (Derives.eqRefl (.app (named (.eq Ty.t)) (translate p)))
      tr_top_identity)
    (named_eq (translate p) .top)

/-- Fresh-argument beta in the expanded definition package. -/
theorem translated_lam_fresh {Γ σ} {ρ : RTy}
    (M : Classicism.Meta.Term Sig (σ :: Γ) ρ) :
    Proof (σ :: Γ) []
      (.eq (.app (translate (.lam M)).wk (.var .zero)) (translate M)) :=
  lift_basis (RelationalBracketInterpretation.bracket_fresh_beta_derives
    (RelationalLambdaCompilation.compile M))

/-- Only a theorem about the fresh argument can be closed to an identity
with a compiled abstraction. No local-premise variant is asserted. -/
theorem eq_translated_lam {Γ σ} {ρ : RTy}
    {F : TargetTerm Sig Γ (σ ⇒ ρ)}
    {M : Classicism.Meta.Term Sig (σ :: Γ) ρ}
    (h : Proof (σ :: Γ) [] (.eq (.app F.wk (.var .zero)) (translate M))) :
    Proof Γ [] (.eq F (translate (.lam M))) := by
  apply (calculus (Constants Sig) (ExpandedNamedAxiom Sig)).theorem_zeta
  exact Derives.eqTrans h (Derives.eqSymm (translated_lam_fresh M))

theorem delta_constR {Γ} (ρ : RTy)
    {M : Classicism.Meta.Term Sig Γ (RTy.t ⇒ ρ)}
    (h : Classicism.Meta.Term.unfoldConst ρ = some M) :
    Proof Γ [] (.eq (named (.constR ρ)) (translate M)) := by
  cases ρ with
  | t =>
      simp only [Classicism.Meta.Term.unfoldConst, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using
        (named_constR_t (Sig := Sig) (Γ := Ty.t :: Γ) (Δ := []) (.var .zero))
  | arr σ ρ =>
      simp only [Classicism.Meta.Term.unfoldConst, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using
        (named_constR_step (Sig := Sig) (Γ := σ :: Ty.t :: Γ) (Δ := []) (σ := σ) ρ (.var (.succ .zero)) (.var .zero))

theorem delta_negR {Γ} (ρ : RTy)
    {M : Classicism.Meta.Term Sig Γ (ρ ⇒ ρ)}
    (h : Classicism.Meta.Term.unfoldNeg ρ = some M) :
    Proof Γ [] (.eq (named (.negR ρ)) (translate M)) := by
  cases ρ with
  | t =>
      simp only [Classicism.Meta.Term.unfoldNeg, Option.some.injEq] at h
      subst M
      apply (calculus (Constants Sig) (ExpandedNamedAxiom Sig)).theorem_zeta
      change Proof (Ty.t :: Γ) [] _
      have hn := named_unary_t (Sig := Sig) (Γ := Ty.t :: Γ) (Δ := []) .neg (.var .zero)
      have hm := named_not (Sig := Sig) (Γ := Ty.t :: Γ) (Δ := []) (.var .zero)
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] at hn hm
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using (Derives.eqTrans hn (Derives.eqSymm hm))
  | arr σ ρ =>
      simp only [Classicism.Meta.Term.unfoldNeg, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using
        (named_unary_step (Sig := Sig) (Γ := σ :: (σ ⇒ ρ) :: Γ) (Δ := []) (σ := σ) .neg ρ (.var (.succ .zero)) (.var .zero))

theorem delta_andR {Γ} (ρ : RTy)
    {M : Classicism.Meta.Term Sig Γ (ρ ⇒ ρ ⇒ ρ)}
    (h : Classicism.Meta.Term.unfoldAnd ρ = some M) :
    Proof Γ [] (.eq (named (.andR ρ)) (translate M)) := by
  cases ρ with
  | t =>
      simp only [Classicism.Meta.Term.unfoldAnd, Option.some.injEq] at h
      subst M
      apply (calculus (Constants Sig) (ExpandedNamedAxiom Sig)).theorem_zeta
      apply (calculus (Constants Sig) (ExpandedNamedAxiom Sig)).theorem_zeta
      change Proof (Ty.t :: Ty.t :: Γ) [] _
      have hn := named_binary_t (Sig := Sig) (Γ := Ty.t :: Ty.t :: Γ) (Δ := []) .and (.var (.succ .zero)) (.var .zero)
      have hm := named_and (Sig := Sig) (Γ := Ty.t :: Ty.t :: Γ) (Δ := []) (.var (.succ .zero)) (.var .zero)
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] at hn hm
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using (Derives.eqTrans hn (Derives.eqSymm hm))
  | arr σ ρ =>
      simp only [Classicism.Meta.Term.unfoldAnd, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      apply eq_translated_lam
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using
        (named_binary_step (Sig := Sig) (Γ := σ :: (σ ⇒ ρ) :: (σ ⇒ ρ) :: Γ) (Δ := []) (σ := σ) .and ρ (.var (.succ (.succ .zero))) (.var (.succ .zero)) (.var .zero))

theorem delta_orR {Γ} (ρ : RTy)
    {M : Classicism.Meta.Term Sig Γ (ρ ⇒ ρ ⇒ ρ)}
    (h : Classicism.Meta.Term.unfoldOr ρ = some M) :
    Proof Γ [] (.eq (named (.orR ρ)) (translate M)) := by
  cases ρ with
  | t =>
      simp only [Classicism.Meta.Term.unfoldOr, Option.some.injEq] at h
      subst M
      apply (calculus (Constants Sig) (ExpandedNamedAxiom Sig)).theorem_zeta
      apply (calculus (Constants Sig) (ExpandedNamedAxiom Sig)).theorem_zeta
      change Proof (Ty.t :: Ty.t :: Γ) [] _
      have hn := named_binary_t (Sig := Sig) (Γ := Ty.t :: Ty.t :: Γ) (Δ := []) .or (.var (.succ .zero)) (.var .zero)
      have hm := named_or (Sig := Sig) (Γ := Ty.t :: Ty.t :: Γ) (Δ := []) (.var (.succ .zero)) (.var .zero)
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] at hn hm
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using (Derives.eqTrans hn (Derives.eqSymm hm))
  | arr σ ρ =>
      simp only [Classicism.Meta.Term.unfoldOr, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      apply eq_translated_lam
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using
        (named_binary_step (Sig := Sig) (Γ := σ :: (σ ⇒ ρ) :: (σ ⇒ ρ) :: Γ) (Δ := []) (σ := σ) .or ρ (.var (.succ (.succ .zero))) (.var (.succ .zero)) (.var .zero))

theorem delta_coextR {Γ} (ρ : RTy)
    {M : Classicism.Meta.Term Sig Γ (ρ ⇒ ρ ⇒ RTy.t)}
    (h : Classicism.Meta.Term.unfoldCoext ρ = some M) :
    Proof Γ [] (.eq (named (.coextR ρ)) (translate M)) := by
  cases ρ with
  | t =>
      simp only [Classicism.Meta.Term.unfoldCoext, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      have hn := named_coextR (Sig := Sig) (Γ := Ty.t :: Ty.t :: Γ) (Δ := []) .t (.var (.succ .zero)) (.var .zero)
      have hm := tr_iff_identity (Sig := Sig) (Γ := Ty.t :: Ty.t :: Γ) (.var (.succ .zero)) (.var .zero)
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] at hn hm
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using (Derives.eqTrans hn (Derives.eqSymm hm))
  | arr σ ρ =>
      simp only [Classicism.Meta.Term.unfoldCoext, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      let b : Classicism.Meta.Formula Sig (σ :: (σ ⇒ ρ) :: (σ ⇒ ρ) :: Γ) :=
        .app (.app (.coextR ρ)
          (.app Classicism.Meta.Term.v2 Classicism.Meta.Term.v0))
          (.app Classicism.Meta.Term.v1 Classicism.Meta.Term.v0)
      have hn := named_coextR_step (Sig := Sig) (Γ := (σ ⇒ ρ) :: (σ ⇒ ρ) :: Γ) (σ := σ) ρ (.var (.succ .zero)) (.var .zero)
      have hm := forall_lam_identity b
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion, b] at hn hm
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion, b] using (Derives.eqTrans hn (Derives.eqSymm hm))

theorem delta_boxR {Γ} (ρ : RTy)
    {M : Classicism.Meta.Term Sig Γ (ρ ⇒ ρ)}
    (h : Classicism.Meta.Term.unfoldBox ρ = some M) :
    Proof Γ [] (.eq (named (.boxR ρ)) (translate M)) := by
  cases ρ with
  | t =>
      simp only [Classicism.Meta.Term.unfoldBox, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      have hn := named_unary_t (Sig := Sig) (Γ := Ty.t :: Γ) (Δ := []) .boxEq (.var .zero)
      have hm := tr_box_identity (Sig := Sig) (Γ := Ty.t :: Γ) (.var .zero)
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] at hn hm
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using (Derives.eqTrans hn (Derives.eqSymm hm))
  | arr σ ρ =>
      simp only [Classicism.Meta.Term.unfoldBox, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using
        (named_unary_step (Sig := Sig) (Γ := σ :: (σ ⇒ ρ) :: Γ) (Δ := []) (σ := σ) .boxEq ρ (.var (.succ .zero)) (.var .zero))

theorem delta_inclR {Γ} (ρ : RTy)
    {M : Classicism.Meta.Term Sig Γ (ρ ⇒ ρ ⇒ RTy.t)}
    (h : Classicism.Meta.Term.unfoldIncl ρ = some M) :
    Proof Γ [] (.eq (named (.inclR ρ)) (translate M)) := by
  cases ρ with
  | t =>
      simp only [Classicism.Meta.Term.unfoldIncl, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      have hn := named_inclR (Sig := Sig) (Γ := Ty.t :: Ty.t :: Γ) (Δ := []) .t (.var (.succ .zero)) (.var .zero)
      have hm := tr_imp_identity (Sig := Sig) (Γ := Ty.t :: Ty.t :: Γ) (.var (.succ .zero)) (.var .zero)
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] at hn hm
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion] using (Derives.eqTrans hn (Derives.eqSymm hm))
  | arr σ ρ =>
      simp only [Classicism.Meta.Term.unfoldIncl, Option.some.injEq] at h
      subst M
      apply eq_translated_lam
      apply eq_translated_lam
      let b : Classicism.Meta.Formula Sig (σ :: (σ ⇒ ρ) :: (σ ⇒ ρ) :: Γ) :=
        .app (.app (.inclR ρ)
          (.app Classicism.Meta.Term.v2 Classicism.Meta.Term.v0))
          (.app Classicism.Meta.Term.v1 Classicism.Meta.Term.v0)
      have hn := named_inclR_step (Sig := Sig) (Γ := (σ ⇒ ρ) :: (σ ⇒ ρ) :: Γ) (σ := σ) ρ (.var (.succ .zero)) (.var .zero)
      have hm := forall_lam_identity b
      simp only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion, b] at hn hm
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar,
        named, LogicalOperator.atom, Classicism.Meta.Term.v0, Classicism.Meta.Term.v1,
        Classicism.Meta.Term.v2, Term.wk, Term.rename, Ren.shift, Unary.operator,
        Binary.operator, Unary.apply, Binary.apply, language, Term.coext, inclusion, b] using (Derives.eqTrans hn (Derives.eqSymm hm))

/-- Every actual delta generator is covered, with no residual delta
assumption or function-extensionality axiom. -/
theorem delta_identity {Γ σ} {a b : Classicism.Meta.Term Sig Γ σ}
    (h : a.unfoldR = some b) : Proof Γ [] (.eq (translate a) (translate b)) := by
  cases a with
  | var v => cases h
  | const c => cases h
  | app f a => cases h
  | lam p => cases h
  | and => cases h
  | or => cases h
  | not => cases h
  | all σ => cases h
  | ex σ => cases h
  | eq σ => cases h
  | constR ρ =>
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, named, LogicalOperator.atom] using
        (delta_constR (Sig := Sig) (Γ := Γ) ρ h)
  | negR ρ =>
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, named, LogicalOperator.atom] using
        (delta_negR (Sig := Sig) (Γ := Γ) ρ h)
  | andR ρ =>
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, named, LogicalOperator.atom] using
        (delta_andR (Sig := Sig) (Γ := Γ) ρ h)
  | orR ρ =>
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, named, LogicalOperator.atom] using
        (delta_orR (Sig := Sig) (Γ := Γ) ρ h)
  | coextR ρ =>
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, named, LogicalOperator.atom] using
        (delta_coextR (Sig := Sig) (Γ := Γ) ρ h)
  | boxR ρ =>
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, named, LogicalOperator.atom] using
        (delta_boxR (Sig := Sig) (Γ := Γ) ρ h)
  | inclR ρ =>
      simpa only [translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, named, LogicalOperator.atom] using
        (delta_inclR (Sig := Sig) (Γ := Γ) ρ h)

/-- All the actual C rules translate into the explicitly named extension.
This theorem no longer assumes delta soundness. -/
theorem derivable_translate {Ax : Classicism.Meta.AxiomSet Sig} {Γ Δ p}
    (h : Classicism.Meta.Derivable Ax (Γ := Γ) Δ p)
    (logicalOnly : ∀ a, Ax a → Classicism.Meta.Logical a) :
    Proof Γ (Δ.map translate) (translate p) :=
  RelationalCProofTransport.derivable_translate_of_delta delta_identity h logicalOnly

#print axioms tr_imp_identity
#print axioms tr_iff_identity
#print axioms tr_top_identity
#print axioms delta_identity
#print axioms derivable_translate

end Classicism.Research.ModalLogicalOperators
