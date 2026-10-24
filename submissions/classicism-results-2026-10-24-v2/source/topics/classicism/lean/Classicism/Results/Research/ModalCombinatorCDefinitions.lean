import Classicism.Results.Research.ModalUniformCombinators
import Classicism.Results.Research.ModalConcreteToCDerivation
import Classicism.Results.Research.RelationalLambdaDecoding

/-!
# The actual C witnesses for the five modal combinator definitions

Original research implementation, misc, 23 October 2026. Saturating an
admitted relational term with `Body.ofTerm` and taking its C lambda witness
returns the original translation up to eta conversion. Thus each explicit
strong-comprehension combinator body has the corresponding closed decoded
lambda as its witness, up to conversion and actual object equality in C.

All five conclusions concern the concrete bodies and the concrete decoder.
No interpretation of a combinator law, choice of representatives, or optional
modal premise is assumed. The type restrictions are those of the existing
relational syntax; in particular, S has a relational intermediate type,
while C and W allow arbitrary argument types.

This source was prepared without running Lean. The axiom-report commands
below are requests for a later check, not a report of completed checking.
-/

namespace Classicism.Research.ModalNamedToC

open Classicism.Meta
open ModalConcreteToC (signature SourceTerm toC toCVar toC_wk bodyWitness)
open ModalComprehensionConcreteSyntax (Body)
open RelationalLambdaDecoding (decodeBasis)

variable {Const : Ty → Type}

/-- Saturation adds only eta expansions to the translated term. This is
induction on the relational output type, including every output-tail binder. -/
theorem bodyWitness_ofTerm (ρ : RTy) : ∀ {Γ : Ctx}
    (p : SourceTerm Const Γ ρ),
    Conv (bodyWitness (Body.ofTerm ρ p)) (toC p) := by
  induction ρ using RTy.induction with
  | t =>
      intro Γ p
      exact Conv.refl _
  | arr σ ρ ih =>
      intro Γ p
      change Conv
        (Term.lam (bodyWitness (Body.ofTerm ρ
          (ModalComprehensionConcreteSyntax.Term.app p.wk (.var .zero)))))
        (toC p)
      have hi : Conv
          (bodyWitness (Body.ofTerm ρ
            (ModalComprehensionConcreteSyntax.Term.app p.wk (.var .zero))))
          (Term.app (toC p).weaken (.var .zero)) := by
        simpa only [toC, toC_wk, toCVar] using
          ih (ModalComprehensionConcreteSyntax.Term.app p.wk (.var .zero))
      exact Conv.trans (Conv.lam_congr hi) (Conv.eta (toC p))

/-- Conversion gives object equality by converting reflexivity's right side. -/
theorem conv_eq {Γ : Ctx} {σ : Ty}
    {a b : Term (signature Const) Γ σ} (h : Conv a b) :
    C.Derivable [] (Term.eq' a b) :=
  Classicism.Meta.Derivable.conv (Classicism.Meta.Derivable.refl a)
    (Conv.app_congr (Conv.refl (Term.app (.eq σ) a)) h)

theorem bodyWitness_ofTerm_eq (ρ : RTy) {Γ : Ctx}
    (p : SourceTerm Const Γ ρ) :
    C.Derivable [] (Term.eq' (bodyWitness (Body.ofTerm ρ p)) (toC p)) :=
  conv_eq (bodyWitness_ofTerm ρ p)

/-- The SC witness for I converts to its actual closed lambda realization. -/
theorem combinatorWitness_I (ρ : RTy) (Γ : Ctx) :
    Conv (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.I (Const := Const) ρ Γ))
      (decodeBasis (Sig := signature Const) (.I ρ)) := by
  simpa only [ModalComprehensionConcreteSyntax.CombinatorBody.I, bodyWitness, decodeBasis, toC, toCVar] using
    (Conv.lam_congr (bodyWitness_ofTerm ρ
      (.var .zero : SourceTerm Const (ρ :: Γ) ρ)))

/-- The SC witness for K converts to its actual closed lambda realization. -/
theorem combinatorWitness_K (σ : Ty) (ρ : RTy) (Γ : Ctx) :
    Conv (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.K (Const := Const) σ ρ Γ))
      (decodeBasis (Sig := signature Const) (.K σ ρ)) := by
  simpa only [ModalComprehensionConcreteSyntax.CombinatorBody.K, bodyWitness, decodeBasis, toC, toCVar] using
    (Conv.lam_congr (Conv.lam_congr (bodyWitness_ofTerm ρ
      (.var (.succ .zero) : SourceTerm Const (σ :: ρ :: Γ) ρ))))

/-- The SC witness for S converts to its actual closed lambda realization. -/
theorem combinatorWitness_S (σ : Ty) (τ ρ : RTy) (Γ : Ctx) :
    Conv (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.S (Const := Const) σ τ ρ Γ))
      (decodeBasis (Sig := signature Const) (.S σ τ ρ)) := by
  simpa only [ModalComprehensionConcreteSyntax.CombinatorBody.S, bodyWitness, decodeBasis, toC, toCVar] using
    (Conv.lam_congr (Conv.lam_congr (Conv.lam_congr (bodyWitness_ofTerm ρ
      (.app (.app (.var (.succ (.succ .zero))) (.var .zero))
        (.app (.var (.succ .zero)) (.var .zero)) :
        SourceTerm Const (σ :: (σ ⇒ τ) :: (σ ⇒ τ ⇒ ρ) :: Γ) ρ)))))

/-- The SC witness for C converts to its actual closed lambda realization. -/
theorem combinatorWitness_C (σ τ : Ty) (ρ : RTy) (Γ : Ctx) :
    Conv (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.C (Const := Const) σ τ ρ Γ))
      (decodeBasis (Sig := signature Const) (.C σ τ ρ)) := by
  simpa only [ModalComprehensionConcreteSyntax.CombinatorBody.C, bodyWitness, decodeBasis, toC, toCVar] using
    (Conv.lam_congr (Conv.lam_congr (Conv.lam_congr (bodyWitness_ofTerm ρ
      (.app (.app (.var (.succ (.succ .zero))) (.var .zero))
        (.var (.succ .zero)) :
        SourceTerm Const (σ :: τ :: (σ ⇒ τ ⇒ ρ) :: Γ) ρ)))))

/-- The SC witness for W converts to its actual closed lambda realization. -/
theorem combinatorWitness_W (σ : Ty) (ρ : RTy) (Γ : Ctx) :
    Conv (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.W (Const := Const) σ ρ Γ))
      (decodeBasis (Sig := signature Const) (.W σ ρ)) := by
  simpa only [ModalComprehensionConcreteSyntax.CombinatorBody.W, bodyWitness, decodeBasis, toC, toCVar] using
    (Conv.lam_congr (Conv.lam_congr (bodyWitness_ofTerm ρ
      (.app (.app (.var (.succ .zero)) (.var .zero)) (.var .zero) :
        SourceTerm Const (σ :: (σ ⇒ σ ⇒ ρ) :: Γ) ρ))))

theorem combinatorWitness_I_eq (ρ : RTy) (Γ : Ctx) :
    C.Derivable [] (Term.eq'
      (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.I (Const := Const) ρ Γ))
      (decodeBasis (Sig := signature Const) (.I ρ))) :=
  conv_eq (combinatorWitness_I ρ Γ)

theorem combinatorWitness_K_eq (σ : Ty) (ρ : RTy) (Γ : Ctx) :
    C.Derivable [] (Term.eq'
      (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.K (Const := Const) σ ρ Γ))
      (decodeBasis (Sig := signature Const) (.K σ ρ))) :=
  conv_eq (combinatorWitness_K σ ρ Γ)

theorem combinatorWitness_S_eq (σ : Ty) (τ ρ : RTy) (Γ : Ctx) :
    C.Derivable [] (Term.eq'
      (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.S (Const := Const) σ τ ρ Γ))
      (decodeBasis (Sig := signature Const) (.S σ τ ρ))) :=
  conv_eq (combinatorWitness_S σ τ ρ Γ)

theorem combinatorWitness_C_eq (σ τ : Ty) (ρ : RTy) (Γ : Ctx) :
    C.Derivable [] (Term.eq'
      (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.C (Const := Const) σ τ ρ Γ))
      (decodeBasis (Sig := signature Const) (.C σ τ ρ))) :=
  conv_eq (combinatorWitness_C σ τ ρ Γ)

theorem combinatorWitness_W_eq (σ : Ty) (ρ : RTy) (Γ : Ctx) :
    C.Derivable [] (Term.eq'
      (bodyWitness (ModalComprehensionConcreteSyntax.CombinatorBody.W (Const := Const) σ ρ Γ))
      (decodeBasis (Sig := signature Const) (.W σ ρ))) :=
  conv_eq (combinatorWitness_W σ ρ Γ)

#print axioms bodyWitness_ofTerm
#print axioms conv_eq
#print axioms bodyWitness_ofTerm_eq
#print axioms combinatorWitness_I
#print axioms combinatorWitness_K
#print axioms combinatorWitness_S
#print axioms combinatorWitness_C
#print axioms combinatorWitness_W
#print axioms combinatorWitness_I_eq
#print axioms combinatorWitness_K_eq
#print axioms combinatorWitness_S_eq
#print axioms combinatorWitness_C_eq
#print axioms combinatorWitness_W_eq

end Classicism.Research.ModalNamedToC
