import Classicism.Results.Research.ModalReconstructionNames
import Classicism.Results.Research.RelationalLambdaRoundtrip
import Classicism.Syntax.Entailment

/-!
# The named reconstruction translation into C

Original research implementation, misc, 23 October 2026, by Codex (OpenAI),
prompted by Daniel Kodsi. Direct source: the typed reconstruction argument
in `research/2026-10-23/operator-characterizations/lambda-free-classicism-reconstruction-proof.txt`,
sections 3 and 8 (unpaginated).

Old constants retain their exact source identities. New relational names
are interpreted by the original logical constants or the explicit closed
lambda realizations of the five bracket combinators. The named translation
therefore agrees literally with the decoder on the compiler's applicative
image, and inherits its actual C conversion roundtrip.

This module supplies syntax, conversion and its induced C equality. Satisfaction of the
independent named definitions and transport of derivations are separate
obligations. No comprehension witness or proof-transport interface is
assumed here.
-/

namespace Classicism.Research.ModalNamedToC

open Classicism.Meta
open ModalFiniteNameSupport (NamedConst mapTerm)
open ModalReconstructionNames (Name)

variable {C : Ty → Type}

/-- Each introduced name has an explicit, closed C value. -/
def nameValue {Γ : Ctx} {ρ : RTy} (n : Name ρ) :
    Term (ModalConcreteToC.signature C) Γ ρ :=
  RelationalLambdaDecoding.decodeBasis
    (ModalReconstructionNames.join (C := C) (NamedConst.name n))

/-- Old constants are unchanged; only newly introduced names are decoded. -/
def constantValue {Γ : Ctx} : {σ : Ty} → NamedConst C Name σ →
    Term (ModalConcreteToC.signature C) Γ σ
  | σ, .old c => Term.const (Sig := ModalConcreteToC.signature C) ⟨σ, c⟩
  | _, .name n => nameValue n

theorem constantValue_join {Γ : Ctx} {σ : Ty} (c : NamedConst C Name σ) :
    constantValue (Γ := Γ) c =
      RelationalLambdaDecoding.decodeBasis (ModalReconstructionNames.join c) := by
  cases c <;> rfl

theorem constantValue_split {Γ : Ctx} {σ : Ty}
    (c : RelationalBracketAbstraction.BasisConst
      (RelationalLambdaCompilation.Atoms (ModalConcreteToC.signature C)) σ) :
    constantValue (Γ := Γ) (ModalReconstructionNames.split c) =
      RelationalLambdaDecoding.decodeBasis c := by
  rw [constantValue_join, ModalReconstructionNames.join_split]

@[simp] theorem nameValue_rename {Γ Δ : Ctx} {ρ : RTy}
    (r : Ren Γ Δ) (n : Name ρ) :
    (nameValue (C := C) (Γ := Γ) n).rename r = nameValue (Γ := Δ) n :=
  RelationalLambdaDecoding.decodeBasis_rename r _

@[simp] theorem constantValue_rename {Γ Δ : Ctx} {σ : Ty}
    (r : Ren Γ Δ) (c : NamedConst C Name σ) :
    (constantValue (Γ := Γ) c).rename r = constantValue (Γ := Δ) c := by
  cases c with
  | old c => rfl
  | name n => exact nameValue_rename r n

/-- The named extension of the concrete lambda-free translation. -/
def jPlus : {Γ : Ctx} → {σ : Ty} →
    ModalComprehensionConcreteSyntax.Term (NamedConst C Name) Γ σ →
      Term (ModalConcreteToC.signature C) Γ σ
  | _, _, .var v => .var (ModalConcreteToC.toCVar v)
  | _, _, .const c => constantValue c
  | _, _, .app f a => .app (jPlus f) (jPlus a)
  | _, _, .top => Term.top
  | _, _, .imp p q => Term.imp (jPlus p) (jPlus q)
  | _, _, .iff p q => Term.iff (jPlus p) (jPlus q)
  | _, _, .eq a b => Term.eq' (jPlus a) (jPlus b)
  | _, _, .boxOp => .lam (Term.box (.var .zero))
  | _, _, .all p => Term.forall' (jPlus p)
  | _, _, .ex p => Term.exists' (jPlus p)

theorem jPlus_rename {Γ Δ : Ctx} {σ : Ty}
    (r : ModalComprehensionConcreteSyntax.Ren Γ Δ)
    (a : ModalComprehensionConcreteSyntax.Term (NamedConst C Name) Γ σ) :
    jPlus (a.rename r) = (jPlus a).rename (ModalConcreteToC.toCRen r) := by
  induction a generalizing Δ with
  | var v =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, jPlus,
        Term.rename_var, ModalConcreteToC.toCRen, ModalConcreteToC.fromCVar_toCVar]
  | const c => exact (constantValue_rename (ModalConcreteToC.toCRen r) c).symm
  | app f a ihf iha =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, jPlus,
        Term.rename_app, ihf, iha]
  | top => rfl
  | imp p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, jPlus,
        Term.imp, Term.disj, Term.neg, Term.rename_app, Term.rename_or,
        Term.rename_not, ihp, ihq]
  | iff p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, jPlus,
        Term.iff, Term.conj, Term.imp, Term.disj, Term.neg, Term.rename_app,
        Term.rename_and, Term.rename_or, Term.rename_not, ihp, ihq]
  | eq a b iha ihb =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, jPlus,
        Term.eq', Term.rename_app, Term.rename_eq, iha, ihb]
  | boxOp => rfl
  | all p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, jPlus,
        Term.forall', Term.rename_app, Term.rename_all, Term.rename_lam,
        ih, ModalConcreteToC.toCRen_lift]
  | ex p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, jPlus,
        Term.exists', Term.rename_app, Term.rename_ex, Term.rename_lam,
        ih, ModalConcreteToC.toCRen_lift]

theorem jPlus_wk {Γ : Ctx} {σ τ : Ty}
    (a : ModalComprehensionConcreteSyntax.Term (NamedConst C Name) Γ τ) :
    jPlus (a.wk (σ := σ)) = (jPlus a).weaken (τ := σ) := by
  rw [ModalComprehensionConcreteSyntax.Term.wk, jPlus_rename,
    ModalConcreteToC.toCRen_shift]

/-- The extension restricts to the original translation on all old terms. -/
theorem jPlus_old {Γ : Ctx} {σ : Ty}
    (M : ModalComprehensionConcreteSyntax.Term C Γ σ) :
    jPlus (mapTerm (NamedConst.old (Names := Name)) M) = ModalConcreteToC.toC M := by
  induction M <;> simp_all only [mapTerm, jPlus, constantValue, ModalConcreteToC.toC]
  case const c => rfl

theorem toCVar_embedVar {Γ : Ctx} {σ : Ty} (v : Var Γ σ) :
    ModalConcreteToC.toCVar (RelationalBracketInterpretation.embedVar v) = v := by
  induction v <;>
    simp_all only [RelationalBracketInterpretation.embedVar, ModalConcreteToC.toCVar]

/-- On the explicitly split compiler signature, j+ is exactly the decoder. -/
theorem jPlus_split_embed {Γ : Ctx} {σ : Ty}
    (raw : RelationalBracketAbstraction.Term
      (RelationalLambdaCompilation.Atoms (ModalConcreteToC.signature C)) Γ σ) :
    jPlus (mapTerm ModalReconstructionNames.split
      (RelationalBracketInterpretation.embed raw)) =
      RelationalLambdaDecoding.decode raw := by
  induction raw with
  | var v =>
      simp only [RelationalBracketInterpretation.embed, mapTerm, jPlus,
        RelationalLambdaDecoding.decode, toCVar_embedVar]
  | const c =>
      simp only [RelationalBracketInterpretation.embed, mapTerm, jPlus,
        RelationalLambdaDecoding.decode, constantValue_split]
  | app f a ihf iha =>
      simp only [RelationalBracketInterpretation.embed, mapTerm, jPlus,
        RelationalLambdaDecoding.decode, ihf, iha]

/-- The compiled named term returns to its exact original C term up to
actual beta/eta conversion, at every original type and context. -/
theorem jPlus_compile {Γ : Ctx} {σ : Ty}
    (M : Term (ModalConcreteToC.signature C) Γ σ) :
    Conv (jPlus (mapTerm ModalReconstructionNames.split
      (RelationalBracketInterpretation.embed (RelationalLambdaCompilation.compile M)))) M := by
  rw [jPlus_split_embed]
  exact RelationalLambdaDecoding.decode_compile M

/-- Conversion and reflexivity give object identity in C, without any
additional assumptions about the named definitions. -/
theorem jPlus_compile_eq {Γ : Ctx} {σ : Ty}
    (M : Term (ModalConcreteToC.signature C) Γ σ)
    (Δ : List (Formula (ModalConcreteToC.signature C) Γ)) :
    Derivable Classicism.Meta.C.axioms Δ
      (Term.eq' (jPlus (mapTerm ModalReconstructionNames.split
        (RelationalBracketInterpretation.embed (RelationalLambdaCompilation.compile M)))) M) := by
  exact Derivable.conv (Derivable.refl _)
    (Conv.app_congr (Conv.refl _) (jPlus_compile M))

#print axioms constantValue_join
#print axioms constantValue_split
#print axioms nameValue_rename
#print axioms constantValue_rename
#print axioms jPlus_rename
#print axioms jPlus_wk
#print axioms jPlus_old
#print axioms toCVar_embedVar
#print axioms jPlus_split_embed
#print axioms jPlus_compile
#print axioms jPlus_compile_eq

end Classicism.Research.ModalNamedToC
