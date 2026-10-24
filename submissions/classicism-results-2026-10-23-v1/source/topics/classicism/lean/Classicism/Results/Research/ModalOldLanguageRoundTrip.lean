import Classicism.Results.Research.ModalLogicalOperatorDelta
import Classicism.Results.Research.ModalConcreteToCSyntax
import Classicism.Results.Research.ModalNativeCongruence
import Classicism.Results.Research.ModalSequentClosure

/-!
# Literal old-language round trip through C and bracket compilation

Original research, misc, 23 October 2026. The primitive first-class box
operator is covered before its application to an argument; its identity
is derived by theorem zeta and the proved Box/identity characterization.
This is stronger than checking only already boxed formulas.

The final theorem transports arbitrary finite local old-language premises
to the named extension. It uses implication discharge and object identity,
so no premise is made global or necessitated. Finite-name elimination is
the remaining independent step for the unconditional B/C equivalence.
-/

namespace Classicism.Research.ModalOldLanguageRoundTrip
open Classicism.Meta (Ty RTy Ctx)
open ModalComprehensionConcreteSyntax (Term Formula Derives Axioms)
open ModalConcreteToC (signature toC toCVar)
open RelationalCompiledContexts (translate)
open ModalLogicalOperators (Constants ExpandedNamedAxiom)

variable {Const : Ty → Type}

abbrev NewConst (Const : Ty → Type) := Constants (signature Const)
abbrev Proof (Γ : Ctx) (Δ : List (Formula (NewConst Const) Γ))
    (p : Formula (NewConst Const) Γ) :=
  Derives (NewConst Const) (ExpandedNamedAxiom (signature Const)) Γ Δ p

def oldConst {σ} (c : Const σ) : NewConst Const σ :=
  .original (RelationalLambdaCompilation.Atoms.nonlogical
    (Sig := signature Const) (Sigma.mk σ c))

/-- The ordinary signature inclusion, leaving all native logical syntax
and the primitive modal operation unchanged. -/
def old : {Γ : Ctx} → {σ : Ty} → Term Const Γ σ → Term (NewConst Const) Γ σ
  | _, _, .var v => .var v
  | _, _, .const c => .const (oldConst c)
  | _, _, .app f a => .app (old f) (old a)
  | _, _, .top => .top
  | _, _, .imp p q => .imp (old p) (old q)
  | _, _, .iff p q => .iff (old p) (old q)
  | _, _, .eq a b => .eq (old a) (old b)
  | _, _, .boxOp => .boxOp
  | _, _, .all p => .all (old p)
  | _, _, .ex p => .ex (old p)

theorem embed_toCVar {Γ σ} (v : ModalComprehensionConcreteSyntax.Var Γ σ) :
    RelationalBracketInterpretation.embedVar (toCVar v) = v := by
  induction v <;> simp_all only [toCVar, RelationalBracketInterpretation.embedVar]

theorem box_operator_roundtrip {Γ} :
    Proof (Const := Const) Γ [] (.eq (translate (toC (Term.boxOp (Const := Const)))) .boxOp) := by
  apply (ModalComprehensionConcreteSyntax.calculus (NewConst Const)
    (ExpandedNamedAxiom (signature Const))).theorem_zeta
  change Proof (Const := Const) (Ty.t :: Γ) []
    (.eq (.app (translate (Classicism.Meta.Term.lam
      (Classicism.Meta.Term.box (.var .zero)))).wk (.var .zero))
      (Term.box (.var .zero)))
  have hβ := ModalLogicalOperators.translated_lam_fresh
    (Sig := signature Const) (Γ := Γ)
    (Classicism.Meta.Term.box (Classicism.Meta.Term.var .zero))
  have hbox := ModalClassicalRules.theorem_equivalence_identity
    ((ModalComprehensionConcreteSyntax.calculus (NewConst Const)
      (ExpandedNamedAxiom (signature Const))).box_identity
      (Term.var (.zero : ModalComprehensionConcreteSyntax.Var (Ty.t :: Γ) Ty.t)))
  have hbox' : Proof (Const := Const) (Ty.t :: Γ) []
      (.eq (Term.box (.var .zero)) (.eq (.var .zero) .top)) := by
    simpa only [ModalComprehensionConcreteSyntax.language] using hbox
  have ht : Proof (Const := Const) (Ty.t :: Γ) []
      (.eq (translate (Classicism.Meta.Term.box (.var .zero)))
        (.eq (.var .zero) .top)) := by
    simpa only [translate, RelationalLambdaCompilation.compile,
      RelationalBracketInterpretation.embed, RelationalBracketInterpretation.embedVar] using
      (ModalLogicalOperators.tr_box_identity (Sig := signature Const)
        (Γ := Ty.t :: Γ) (.var .zero))
  exact Derives.eqTrans hβ (Derives.eqTrans ht (Derives.eqSymm hbox'))

/-- The two translations return every old term as a literal object
identity, including open terms and unsaturated primitive box. -/
theorem term_roundtrip {Γ σ} (M : Term Const Γ σ) :
    Proof Γ [] (.eq (translate (toC M)) (old M)) := by
  induction M with
  | var v =>
      simpa only [translate, toC, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, embed_toCVar, old] using
        (Derives.eqRefl (Term.var v) : Proof _ [] (.eq (.var v) (.var v)))
  | @const Γ σ c =>
      simp only [Proof, translate, toC, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed, old, oldConst, signature]
      exact Derives.eqRefl _
  | app f a ihf iha =>
      simpa only [toC, old, translate, RelationalLambdaCompilation.compile,
        RelationalBracketInterpretation.embed] using Derives.eqApp ihf iha
  | top => exact ModalLogicalOperators.tr_top_identity
  | imp p q ihp ihq =>
      exact .eqTrans (ModalLogicalOperators.tr_imp_identity (toC p) (toC q))
        (ModalNativeCongruence.imp_identity ihp ihq)
  | iff p q ihp ihq =>
      exact .eqTrans (ModalLogicalOperators.tr_iff_identity (toC p) (toC q))
        (ModalNativeCongruence.iff_identity ihp ihq)
  | eq a b iha ihb =>
      simpa only [toC, old] using Derives.eqTrans
        (RelationalCProofTransport.tr_eq (toC a) (toC b))
        (ModalNativeCongruence.equality_identity iha ihb)
  | boxOp => exact box_operator_roundtrip
  | all p ih =>
      exact .eqTrans (RelationalCProofTransport.forall_lam_identity (toC p))
        (ModalClassicalRules.all_identity ih)
  | ex p ih =>
      exact .eqTrans (RelationalCProofTransport.exists_lam_identity (toC p))
        (RelationalCProofTransport.ex_identity ih)

theorem discharge_roundtrip {Γ} (Δ : List (Formula Const Γ))
    {p q : Formula (NewConst Const) Γ} (h : Proof Γ [] (.eq p q)) :
    Proof Γ [] (.eq (ModalComprehensionConcreteSyntax.discharge
      (Δ.map (fun a => translate (toC a))) p)
      (ModalComprehensionConcreteSyntax.discharge (Δ.map old) q)) := by
  induction Δ generalizing p q with
  | nil => exact h
  | cons a Δ ih => exact ih (ModalNativeCongruence.imp_identity (term_roundtrip a) h)

/-- Actual C consequence of old formulas gives an old-formula consequence
in the explicit named extension. No generic proof-preservation assumption
or hypothesis substitution principle is needed. -/
theorem old_sequent_in_named_extension {Γ} {Δ : List (Formula Const Γ)}
    {p : Formula Const Γ}
    (h : Classicism.Meta.Derivable Classicism.Meta.Logical
      (Γ := Γ) (Δ.map toC) (toC p)) :
    Proof Γ (Δ.map old) (old p) := by
  have ht := ModalLogicalOperators.derivable_translate
    (Sig := signature Const) h (fun _ ha => ha)
  have ht' : Proof Γ (Δ.map (fun p => translate (toC p)))
      (translate (toC p)) := by
    simpa only [Proof, RelationalCProofTransport.Proof,
      List.map_map, Function.comp_def] using ht
  have hd := Derives.discharge_local _ ht'
  have he := discharge_roundtrip Δ (term_roundtrip p)
  exact Derives.reapply_local _ (Derives.eqTruth he hd)

#print axioms box_operator_roundtrip
#print axioms term_roundtrip
#print axioms old_sequent_in_named_extension

end Classicism.Research.ModalOldLanguageRoundTrip
