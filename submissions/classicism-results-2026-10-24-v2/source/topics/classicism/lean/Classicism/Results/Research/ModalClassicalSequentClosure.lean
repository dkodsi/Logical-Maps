import Classicism.Results.Research.ModalSequentClosure
import Classicism.Results.Research.ModalFiniteClassicalDefinitions

/-!
# Classical open sequents and finite representative definitions

Original research, misc, 23 October 2026. Source:
`research/2026-10-23/operator-characterizations/finite-name-erasure-proof.txt`,
sections 7–8; and `lambda-free-classicism-reconstruction-proof.txt`, section 1.

The two displayed classical axiom forms are preserved by concrete constant
interpretation and capture-avoiding substitution. The existing induction on
actual derivations therefore gives renaming and substitution with no assumed
proof-preservation interface. Fresh UI reopens the universally closed sequent;
its optional premises are then reapplied, never necessitated.

Finally the finite DefinitionTower embedding commutes with discharge and
universal closure. This extends the existing closed-boundary classical
conservativity theorem to arbitrary free-variable contexts and local premises.
It does not establish a whole-C translation or finite support for an arbitrary
infinite family of names. No source in the imported frozen batch is changed.
-/

namespace Classicism.Research.ModalFreshConstantSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax

variable {C D : Ty → Type}

/-- Each translated classical axiom is an actual target axiom instance.
In particular the bound variable in the existence axiom remains bound. -/
theorem classical_axiom_translate {Γ Θ} (cs : ConstImage C D Θ)
    (vs : Sub D Γ Θ) {p : Formula C Γ}
    (h : ClassicalAxioms C Γ p) :
    Derives D (ClassicalAxioms D) Θ [] (translate cs vs p) := by
  cases h with
  | dne p =>
      change Derives D (ClassicalAxioms D) Θ []
        (.imp (neg (neg (translate cs vs p))) (translate cs vs p))
      exact .ax (.dne _)
  | exists_e =>
      change Derives D (ClassicalAxioms D) Θ []
        (.ex (.eq (.var (.zero : Var (Ty.e :: Θ) Ty.e)) (.var .zero)))
      exact .ax .exists_e

/-- Concrete proof transport for exactly the stated classical base.
The existing derivation induction handles SC, I, binders and theorem-only Nec;
the additional axiom-instance obligation is discharged above. -/
theorem classical_derives_translate {Γ Δ p}
    (proof : Derives C (ClassicalAxioms C) Γ Δ p)
    {Θ} (cs : ConstImage C D Θ) (vs : Sub D Γ Θ) :
    Derives D (ClassicalAxioms D) Θ
      (Δ.map (translate cs vs)) (translate cs vs p) := by
  apply derives_translate (Ax := ClassicalAxioms C) (Ay := ClassicalAxioms D)
    ?_ proof cs vs
  intro Γ Θ cs vs p h
  exact classical_axiom_translate cs vs h

/-- Fixing constants in simultaneous translation gives the existing literal,
capture-avoiding term substitution. -/
theorem translate_as_subst {Γ Θ σ} (s : Sub C Γ Θ) (t : Term C Γ σ) :
    translate (fun c => Term.const c) s t = t.subst s := by
  induction t generalizing Θ <;>
    simp_all only [translate, Term.subst, Term.wk, Term.rename]

theorem classical_derives_subst {Γ Δ p}
    (proof : Derives C (ClassicalAxioms C) Γ Δ p)
    {Θ} (s : Sub C Γ Θ) :
    Derives C (ClassicalAxioms C) Θ
      (Δ.map (fun q => q.subst s)) (p.subst s) := by
  have hf : (translate (fun c => Term.const c) s :
      Term C Γ Ty.t → Term C Θ Ty.t) = (fun q => q.subst s) := by
    funext q
    exact translate_as_subst s q
  have h := classical_derives_translate proof (fun c => .const c) s
  rw [hf] at h
  exact h

theorem classical_derives_rename {Γ Δ p}
    (proof : Derives C (ClassicalAxioms C) Γ Δ p)
    {Θ} (r : Ren Γ Θ) :
    Derives C (ClassicalAxioms C) Θ
      (Δ.map (fun q => q.rename r)) (p.rename r) := by
  have hf : (translate (fun c => Term.const c) (fun v => Term.var (r v)) :
      Term C Γ Ty.t → Term C Θ Ty.t) = (fun q => q.rename r) := by
    funext q
    exact translate_as_rename r q
  have h := classical_derives_translate proof (fun c => .const c) (fun v => .var (r v))
  rw [hf] at h
  exact h

end Classicism.Research.ModalFreshConstantSyntax

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open Classicism.Research.ModalFreshConstantSyntax (classical_derives_rename)

variable {Const : Ty → Type}

namespace Derives

/-- Rename the entire sequent into a context with a genuinely fresh variable,
then instantiate at that variable. No closed inhabitant is selected. -/
theorem classical_all_fresh {Γ Δ σ} {P : Formula Const (σ :: Γ)}
    (h : Derives Const (ClassicalAxioms Const) Γ Δ (.all P)) :
    Derives Const (ClassicalAxioms Const) (σ :: Γ)
      (Δ.map (fun p => p.wk)) P := by
  have hr := classical_derives_rename h (Ren.shift (σ := σ))
  have h' : Derives Const (ClassicalAxioms Const) (σ :: Γ)
      (Δ.map (fun p => p.wk)) (.all (P.rename (Ren.lift Ren.shift))) := hr
  simpa only [instantiate_at_fresh] using Derives.allE (.var .zero) h'

theorem classical_reopen_theorem : ∀ (Γ : Ctx) {p : Formula Const Γ},
    Derives Const (ClassicalAxioms Const) [] [] (closeContext Γ p) →
      Derives Const (ClassicalAxioms Const) Γ [] p := by
  intro Γ
  induction Γ with
  | nil => intro p h; exact h
  | cons σ Γ ih =>
      intro p h
      have hu : Derives Const (ClassicalAxioms Const) Γ [] (.all p) := ih h
      simpa only [List.map_nil] using classical_all_fresh hu

theorem classical_reopen_sequent {Γ Δ p}
    (h : Derives Const (ClassicalAxioms Const) [] [] (closeSequent Δ p)) :
    Derives Const (ClassicalAxioms Const) Γ Δ p :=
  reapply_local Δ (classical_reopen_theorem Γ h)

/-- Both directions construct actual proofs in precisely ClassicalAxioms. -/
theorem classical_sequent_iff_closed {Γ Δ p} :
    Derives Const (ClassicalAxioms Const) Γ Δ p ↔
      Derives Const (ClassicalAxioms Const) [] [] (closeSequent Δ p) :=
  ⟨close_sequent, classical_reopen_sequent⟩

end Derives
end Classicism.Research.ModalComprehensionConcreteSyntax

namespace Classicism.Research.ModalFreshConstantSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax

variable {C D : Ty → Type}

namespace DefinitionTower

theorem embed_imp {T : ClosedTheory C} {D U}
    (tower : DefinitionTower C T D U) : ∀ {Γ} (p q : Formula C Γ),
    tower.embed (.imp p q) = .imp (tower.embed p) (tower.embed q) := by
  induction tower with
  | nil => intro Γ p q; rfl
  | snoc previous A ih =>
      intro Γ p q
      simp only [embed, ih, embedOld]

theorem embed_all {T : ClosedTheory C} {D U}
    (tower : DefinitionTower C T D U) : ∀ {Γ σ} (p : Formula C (σ :: Γ)),
    tower.embed (.all p) = .all (tower.embed p) := by
  induction tower with
  | nil => intro Γ σ p; rfl
  | snoc previous A ih =>
      intro Γ σ p
      simp only [embed, ih, embedOld]

theorem embed_discharge {T : ClosedTheory C} {D U}
    (tower : DefinitionTower C T D U) {Γ} (Δ : List (Formula C Γ))
    (p : Formula C Γ) :
    tower.embed (discharge Δ p) = discharge (Δ.map tower.embed) (tower.embed p) := by
  induction Δ generalizing p with
  | nil => rfl
  | cons q Δ ih =>
      simpa only [discharge, List.map_cons, embed_imp] using ih (.imp q p)

theorem embed_closeContext {T : ClosedTheory C} {D U}
    (tower : DefinitionTower C T D U) : ∀ (Γ : Ctx) (p : Formula C Γ),
    tower.embed (closeContext Γ p) = closeContext Γ (tower.embed p) := by
  intro Γ
  induction Γ with
  | nil => intro p; rfl
  | cons σ Γ ih =>
      intro p
      simpa only [closeContext, embed_all] using ih (.all p)

theorem embed_closeSequent {T : ClosedTheory C} {D U}
    (tower : DefinitionTower C T D U) {Γ} (Δ : List (Formula C Γ))
    (p : Formula C Γ) :
    tower.embed (closeSequent Δ p) =
      closeSequent (Δ.map tower.embed) (tower.embed p) := by
  simp only [closeSequent, embed_closeContext, embed_discharge]

end DefinitionTower

/-- Finite dependent representative definitions are conservative for OLD
open local sequents. Earlier definitions remain global throughout tower
erasure; the optional premises are discharged and then reapplied locally. -/
theorem finite_classical_representation_names_conservative_open {D U}
    (tower : DefinitionTower C (ClosedClassicalTheory C) D U)
    {Γ} {Δ : List (Formula C Γ)} {P : Formula C Γ}
    (proof : Derives D (theoryAx U) Γ (Δ.map tower.embed) (tower.embed P)) :
    Derives C (ClassicalAxioms C) Γ Δ P := by
  have closed : Derives D (theoryAx U) [] [] (tower.embed (closeSequent Δ P)) := by
    simpa only [DefinitionTower.embed_closeSequent] using Derives.close_sequent proof
  have erased : Derives C (ClassicalAxioms C) [] [] (closeSequent Δ P) :=
    finite_classical_representation_names_conservative tower (Δ := [])
      (by simpa only [List.map_nil] using closed)
  exact Derives.classical_reopen_sequent erased

#print axioms classical_axiom_translate
#print axioms classical_derives_translate
#print axioms classical_derives_subst
#print axioms classical_derives_rename
#print axioms Derives.classical_sequent_iff_closed
#print axioms DefinitionTower.embed_closeSequent
#print axioms finite_classical_representation_names_conservative_open

end Classicism.Research.ModalFreshConstantSyntax
