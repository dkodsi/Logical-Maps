import Classicism.Results.Research.ModalContextClosure
import Classicism.Results.Research.ModalFiniteDefinitions

/-!
# Closing and reopening a local sequent

Original research, misc, 23 October 2026. Discharge the local premises in
their given order, then universally bind the whole free-variable context.
The exact converse uses genuinely fresh UI and reapplies those premises.
No premise is necessitated, and no modal, Barcan, or choice rule is used.

Discharge and closing work over any stipulated global axiom family. The
reopening theorem here uses the concrete unextended calculus, whose
capture-avoiding renaming theorem has already been proved. In particular,
the main equivalence has no assumed proof-preservation interface.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open Classicism.Research.ModalFreshConstantSyntax (base_derives_rename)

variable {Const : Ty → Type}

/-- The head premise is discharged FIRST. Thus `q :: Δ` becomes
`discharge Δ (q → p)`, with no permutation of hypotheses. -/
def discharge {Γ : Ctx} : List (Formula Const Γ) → Formula Const Γ → Formula Const Γ
  | [], p => p
  | q :: Δ, p => discharge Δ (.imp q p)

/-- Contexts are innermost first, so the head variable is bound first. -/
def closeContext : (Γ : Ctx) → Formula Const Γ → Formula Const []
  | [], p => p
  | _ :: Γ, p => closeContext Γ (.all p)

def closeSequent {Γ : Ctx} (Δ : List (Formula Const Γ)) (p : Formula Const Γ) :
    Formula Const [] :=
  closeContext Γ (discharge Δ p)

namespace Derives

/-- Pure implication introduction discharges exactly the displayed list. -/
theorem discharge_local {Ax : Axioms Const} {Γ}
    (Δ : List (Formula Const Γ)) {p : Formula Const Γ} :
    Derives Const Ax Γ Δ p → Derives Const Ax Γ [] (discharge Δ p) := by
  induction Δ generalizing p with
  | nil => intro h; exact h
  | cons q Δ ih =>
      intro h
      exact ih (Derives.impI h)

/-- Reapplying the displayed premises reverses discharge exactly. -/
theorem reapply_local {Ax : Axioms Const} {Γ}
    (Δ : List (Formula Const Γ)) {p : Formula Const Γ} :
    Derives Const Ax Γ [] (discharge Δ p) → Derives Const Ax Γ Δ p := by
  induction Δ generalizing p with
  | nil => intro h; exact h
  | cons q Δ ih =>
      intro h
      have hp : Derives Const Ax Γ Δ (.imp q p) := ih h
      exact .impE (.weaken (fun _ h => List.mem_cons_of_mem _ h) hp) .hyp₀

/-- Once all local premises are discharged, every free variable can be
generalized using the actual eigenvariable rule. -/
theorem close_theorem {Ax : Axioms Const} : ∀ (Γ : Ctx) {p : Formula Const Γ},
    Derives Const Ax Γ [] p → Derives Const Ax [] [] (closeContext Γ p) := by
  intro Γ
  induction Γ with
  | nil => intro p h; exact h
  | cons σ Γ ih =>
      intro p h
      exact ih (Derives.allI h)

/-- Fresh universal instantiation after capture-avoiding renaming. -/
theorem all_fresh {Γ Δ σ} {P : Formula Const (σ :: Γ)}
    (h : Derives Const (noAdditionalAxioms Const) Γ Δ (.all P)) :
    Derives Const (noAdditionalAxioms Const) (σ :: Γ)
      (Δ.map (fun p => p.wk)) P := by
  have hr := base_derives_rename h (Ren.shift (σ := σ))
  have h' : Derives Const (noAdditionalAxioms Const) (σ :: Γ)
      (Δ.map (fun p => p.wk)) (.all (P.rename (Ren.lift Ren.shift))) := hr
  simpa only [instantiate_at_fresh] using Derives.allE (.var .zero) h'

/-- Universal closure is reopened at the original fresh variables, not by
choosing arbitrary closed inhabitants of their types. -/
theorem reopen_theorem : ∀ (Γ : Ctx) {p : Formula Const Γ},
    Derives Const (noAdditionalAxioms Const) [] [] (closeContext Γ p) →
      Derives Const (noAdditionalAxioms Const) Γ [] p := by
  intro Γ
  induction Γ with
  | nil => intro p h; exact h
  | cons σ Γ ih =>
      intro p h
      have hu : Derives Const (noAdditionalAxioms Const) Γ [] (.all p) := ih h
      simpa only [List.map_nil] using all_fresh hu

theorem close_sequent {Ax : Axioms Const} {Γ Δ p}
    (h : Derives Const Ax Γ Δ p) :
    Derives Const Ax [] [] (closeSequent Δ p) :=
  close_theorem Γ (discharge_local Δ h)

theorem reopen_sequent {Γ Δ p}
    (h : Derives Const (noAdditionalAxioms Const) [] [] (closeSequent Δ p)) :
    Derives Const (noAdditionalAxioms Const) Γ Δ p :=
  reapply_local Δ (reopen_theorem Γ h)

/-- An open local consequence is equivalent to the theoremhood of its
single closed sentence. Both implications are actual proof constructions. -/
theorem sequent_iff_closed {Γ Δ p} :
    Derives Const (noAdditionalAxioms Const) Γ Δ p ↔
      Derives Const (noAdditionalAxioms Const) [] [] (closeSequent Δ p) :=
  ⟨close_sequent, reopen_sequent⟩

end Derives

#print axioms Derives.discharge_local
#print axioms Derives.reapply_local
#print axioms Derives.all_fresh
#print axioms Derives.reopen_theorem
#print axioms Derives.sequent_iff_closed

end Classicism.Research.ModalComprehensionConcreteSyntax
