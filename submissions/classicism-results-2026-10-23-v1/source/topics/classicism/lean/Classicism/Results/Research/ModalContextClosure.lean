import Classicism.Results.Research.ModalConcreteNamingConservativity
import Classicism.Results.Research.ModalTheoremReplacement

/-!
# Capturing every parameter before conservative naming

Original research, misc, 23 October 2026. A finite open body can be made
closed by binding its whole variable context. Applying a closed representative
to those parameters then represents the original open body. This avoids
assuming that separately chosen pointwise witnesses form a function.

The result is an object derivation in the concrete lambda-free calculus.
Its only hypothesis is the closed representative's defining formula, kept
local. Boxed universal elimination is derived from UI, K and theorem-only
Nec; no Barcan assumption or choice principle occurs.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionRepresentation
  (diagram UniformRepresents)
open Classicism.Research.ModalFreshConstantSyntax
  (closedAt closedAt_wk closedAt_nil base_derives_rename)

variable {Const : Ty → Type}

/-- Contexts are innermost first. The outermost parameter is therefore the
first argument of the closed representative. -/
def capturedType : Ctx → RTy → RTy
  | [], ρ => ρ
  | σ :: Γ, ρ => capturedType Γ (σ ⇒ ρ)

def captureBody : (Γ : Ctx) → {ρ : RTy} → Body Const Γ ρ →
    Body Const [] (capturedType Γ ρ)
  | [], _, A => A
  | _ :: Γ, _, A => captureBody Γ (.bind A)

/-- Reapply a closed representative to the original variables. There is
still no lambda constructor in these terms. -/
def specializeClosed : (Γ : Ctx) → (ρ : RTy) →
    Term Const [] (capturedType Γ ρ) → Term Const Γ ρ
  | [], _, H => H
  | σ :: Γ, ρ, H => .app (specializeClosed Γ (σ ⇒ ρ) H).wk (.var .zero)

namespace Derives

/-- Open a necessarily universal formula at a genuinely fresh parameter.
All old local hypotheses are weakened along with the derivation. -/
theorem boxed_all_fresh {Γ Δ σ} {P : Formula Const (σ :: Γ)}
    (h : Derives Const (noAdditionalAxioms Const) Γ Δ
      (Term.box (.all P))) :
    Derives Const (noAdditionalAxioms Const) (σ :: Γ)
      (Δ.map (fun p => p.wk)) P.box := by
  have hr := base_derives_rename h (Ren.shift (σ := σ))
  have h' : Derives Const (noAdditionalAxioms Const) (σ :: Γ)
      (Δ.map (fun p => p.wk))
      (Term.box (.all (P.rename (Ren.lift Ren.shift)))) := hr
  simpa only [instantiate_at_fresh] using boxed_allE (.var .zero) h'

end Derives

/-- One closed, uniform representative suffices for all parameter values.
The definition stays a local premise throughout this derivation. -/
theorem captured_representation : ∀ (Γ : Ctx) {ρ : RTy}
    (A : Body Const Γ ρ) (H : Term Const [] (capturedType Γ ρ)),
    Derives Const (noAdditionalAxioms Const) Γ
      [closedAt (UniformRepresents (captureBody Γ A) H) Γ]
      (UniformRepresents A (specializeClosed Γ ρ H)) := by
  intro Γ
  induction Γ with
  | nil =>
      intro ρ A H
      change Derives Const (noAdditionalAxioms Const) []
        [closedAt (UniformRepresents A H) []] (UniformRepresents A H)
      rw [closedAt_nil (UniformRepresents A H)]
      exact Derives.hyp₀
  | cons σ Γ ih =>
      intro ρ A H
      have h := ih (.bind A) H
      change Derives Const (noAdditionalAxioms Const) Γ
        [closedAt (UniformRepresents (captureBody Γ (.bind A)) H) Γ]
        (Term.box (.all (diagram A
          (.app (specializeClosed Γ (σ ⇒ ρ) H).wk (.var .zero))))) at h
      have hf := Derives.boxed_all_fresh h
      simp only [List.map_cons, List.map_nil] at hf
      rw [closedAt_wk
        (UniformRepresents (captureBody Γ (.bind A)) H) Γ σ] at hf
      change Derives Const (noAdditionalAxioms Const) (σ :: Γ)
        [closedAt (UniformRepresents (captureBody Γ (.bind A)) H) (σ :: Γ)]
        (Term.box (diagram A
          (.app (specializeClosed Γ (σ ⇒ ρ) H).wk (.var .zero))))
      exact hf

/-- The resulting implication is a theorem in the open parameter context;
in particular, the representative's defining premise has not been
necessitated as if it were a theorem. -/
theorem captured_representation_imp (Γ : Ctx) {ρ : RTy}
    (A : Body Const Γ ρ) (H : Term Const [] (capturedType Γ ρ)) :
    Derives Const (noAdditionalAxioms Const) Γ []
      (.imp (closedAt (UniformRepresents (captureBody Γ A) H) Γ)
        (UniformRepresents A (specializeClosed Γ ρ H))) :=
  .impI (captured_representation Γ A H)

#print axioms Derives.boxed_allE
#print axioms Derives.boxed_all_fresh
#print axioms captured_representation
#print axioms captured_representation_imp

end Classicism.Research.ModalComprehensionConcreteSyntax
