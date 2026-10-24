import Classicism.Results.Research.ModalNamedToCSyntax
import Classicism.Results.Research.ModalCombinatorCDefinitions
import Classicism.Results.Research.ModalLogicalCDefinitions
import Classicism.Results.Research.ModalReconstructionNameAdapter
import Classicism.Results.Research.ModalConcreteToCClassical

/-!
# The explicit named reconstruction definitions hold under j+

Original research, misc, Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. Direct source: lambda-free-classicism-reconstruction-proof.txt,
sections 3, 5, 7 and 8, and logical-operator-reconstruction-proof.txt
(local research sources, unpaginated).

Every new name is assigned a particular actual C term. The five combinator
names denote closed typed lambda terms; the thirteen logical families denote
their original C constructors. Independent proofs identify these values with
the lambda witnesses of the exact old-language SC bodies. This module then
proves their actual closed defining sentences in C. The existence or
preservation of those definitions is not an assumed interface.

All abstraction congruences and necessitations used below are applied to
theorems with empty local hypotheses. No optional premise is lifted through
a binder. Compiler acceptance and axiom reports remain for the serialized
verification runner; source preparation alone is not certification.
-/

namespace Classicism.Research.ModalNamedToC
open Classicism.Meta (Ty RTy Ctx Conv)
open ModalConcreteToC (signature toC bodyWitness coextC coextC_conv
  coextC_refl coextC_subst c_beta_fresh c_nec c_defined_dne)
open ModalReconstructionNames (Name closedBody)
open ModalFiniteNameSupport (NamedConst mapBody nameDefinition NamedAxioms)
open ModalComprehensionRepresentation (diagram UniformRepresents)

variable {Const : Ty → Type}

abbrev NamedTerm := ModalComprehensionConcreteSyntax.Term (NamedConst Const Name)
abbrev NamedBody := ModalComprehensionConcreteSyntax.Body (NamedConst Const Name)

/-- The finite target lambda witness for a body in the explicit named
language. This is a structural definition using the actual j+ on formulas. -/
def jBodyWitness : {Γ : Ctx} → {ρ : RTy} → NamedBody (Const := Const) Γ ρ →
    Classicism.Meta.Term (signature Const) Γ ρ
  | _, _, .atom p => jPlus p
  | _, _, .bind A => .lam (jBodyWitness A)

theorem jBodyWitness_old {Γ} {ρ : RTy}
    (A : ModalComprehensionConcreteSyntax.Body Const Γ ρ) :
    jBodyWitness (mapBody NamedConst.old A) = bodyWitness A := by
  induction A with
  | atom p => exact jPlus_old p
  | bind A ih =>
      change Classicism.Meta.Term.lam (jBodyWitness (mapBody NamedConst.old A)) =
        .lam (bodyWitness A)
      rw [ih]

theorem jBodyWitness_name {Γ} {ρ : RTy} (n : Name ρ) :
    jBodyWitness (n.body (C := NamedConst Const Name) Γ) =
      bodyWitness (n.body (C := Const) Γ) := by
  rw [← ModalReconstructionNames.Name.body_map n
    (NamedConst.old : ModalFiniteNameSupport.ConstMap Const (NamedConst Const Name))]
  exact jBodyWitness_old _

/-- Each assigned value is the actual C object supplied by its independent
finite body, up to a C theorem of identity. -/
theorem name_body_identity {ρ : RTy} (n : Name ρ) (Γ : Ctx) :
    Classicism.Meta.C.Derivable [] (Classicism.Meta.Term.eq'
      (bodyWitness (n.body (C := Const) Γ)) (nameValue n)) := by
  cases n with
  | I ρ => exact combinatorWitness_I_eq ρ Γ
  | K σ ρ => exact combinatorWitness_K_eq σ ρ Γ
  | S σ τ ρ => exact combinatorWitness_S_eq σ τ ρ Γ
  | C σ τ ρ => exact combinatorWitness_C_eq σ τ ρ Γ
  | W σ ρ => exact combinatorWitness_W_eq σ ρ Γ
  | logical o =>
      simpa only [ModalReconstructionNames.Name.body, nameValue,
        ModalReconstructionNames.join, RelationalLambdaDecoding.decodeBasis] using
        (logicalWitness_eq (Const := Const) o Γ)

/-- Translation of the primitive box is the same explicit beta contraction
as in the old-language interpreter. -/
theorem jPlus_box {Γ} (p : NamedTerm (Const := Const) Γ Ty.t) :
    Conv (jPlus p.box) (Classicism.Meta.Term.box (jPlus p)) :=
  Conv.beta (Classicism.Meta.Term.box (.var .zero)) (jPlus p)

/-- The translated finite diagram is coextension with its target lambda
witness. This proof is on the actual finite body, not an abstract rule. -/
theorem jPlus_diagram {Γ} {ρ : RTy} (A : NamedBody (Const := Const) Γ ρ)
    (H : NamedTerm (Const := Const) Γ ρ) :
    Conv (jPlus (diagram A H)) (coextC ρ (jPlus H) (jBodyWitness A)) := by
  induction A with
  | atom p => exact Conv.refl _
  | @bind Γ σ ρ A ih =>
      change Conv (Classicism.Meta.Term.forall' (jPlus (diagram A
        (ModalComprehensionConcreteSyntax.Term.app H.wk (.var .zero)))))
        (Classicism.Meta.Term.forall' (coextC ρ
          (.app (jPlus H).weaken (.var .zero))
          (.app (Classicism.Meta.Term.lam (jBodyWitness A)).weaken (.var .zero))))
      apply Conv.app_congr (Conv.refl _)
      apply Conv.lam_congr
      have hi := ih (ModalComprehensionConcreteSyntax.Term.app H.wk (.var .zero))
      simp only [jPlus, jPlus_wk, ModalConcreteToC.toCVar] at hi
      exact Conv.trans hi (coextC_conv ρ (Conv.refl _)
        (Conv.symm (c_beta_fresh (jBodyWitness A))))

/-- Ordinary Leibniz substitution turns a theorem of identity into
coextension. It does not assume local pointwise extensionality. -/
theorem coextC_of_identity {Γ} {ρ : RTy}
    {a b : Classicism.Meta.Term (signature Const) Γ ρ}
    (h : Classicism.Meta.C.Derivable [] (Classicism.Meta.Term.eq' a b)) :
    Classicism.Meta.C.Derivable [] (coextC ρ a b) := by
  have he := Classicism.Meta.Derivable.eqCongrβ
    (coextC ρ a.weaken (.var .zero)) h
  have he' : Classicism.Meta.C.Derivable [] (Classicism.Meta.Term.eq'
      (coextC ρ a a) (coextC ρ a b)) := by
    simpa only [Classicism.Meta.Term.instantiate, coextC_subst,
      Classicism.Meta.Term.subst_var, Classicism.Meta.Sub.cons_zero,
      Classicism.Meta.Term.subst_rename, Classicism.Meta.Sub.compRen_cons_shift,
      Classicism.Meta.Term.subst_id, Classicism.Meta.Term.weaken] using he
  exact Classicism.Meta.Derivable.eqMp he' (coextC_refl ρ a)

/-- Every open contextual instance of a new name's uniform definition is
a C theorem under the explicit decoder assignment. -/
theorem name_uniform_definition {Γ} {ρ : RTy} (n : Name ρ) :
    Classicism.Meta.C.Derivable [] (jPlus
      (UniformRepresents (n.body (C := NamedConst Const Name) Γ)
        (.const (.name n)))) := by
  have hi : Classicism.Meta.C.Derivable [] (Classicism.Meta.Term.eq'
      (jBodyWitness (n.body (C := NamedConst Const Name) Γ)) (nameValue n)) := by
    rw [jBodyWitness_name]
    exact name_body_identity n Γ
  have hd := c_nec (coextC_of_identity (Classicism.Meta.Derivable.eqSymm hi))
  have hc := jPlus_diagram (n.body (C := NamedConst Const Name) Γ)
    (ModalComprehensionConcreteSyntax.Term.const (.name n))
  have ht : Conv (jPlus (UniformRepresents
      (n.body (C := NamedConst Const Name) Γ) (.const (.name n))))
      (Classicism.Meta.Term.box (coextC ρ (nameValue n)
        (jBodyWitness (n.body (C := NamedConst Const Name) Γ)))) :=
    Conv.trans (jPlus_box _) (Conv.app_congr
      (Conv.app_congr (Conv.refl _) hc) (Conv.refl _))
  exact Classicism.Meta.Derivable.conv hd (Conv.symm ht)

/-- This is exactly the closed-definition family used by finite-name
erasure, weakened to any surrounding variable context. -/
theorem nameDefinition_toC {ρ : RTy} (n : Name ρ) (Γ : Ctx) :
    Classicism.Meta.C.Derivable [] (jPlus
      (ModalFreshConstantSyntax.closedAt (nameDefinition (closedBody Const) n) Γ)) := by
  rw [ModalReconstructionNames.nameDefinition_at]
  exact name_uniform_definition n

/-- Both kinds of actual named-extension axiom have actual C proofs.
No premise asserts preservation of an arbitrary derivation. -/
theorem named_axioms_toC {Γ p}
    (h : NamedAxioms (closedBody Const) Γ p) :
    Classicism.Meta.C.Derivable [] (jPlus p) := by
  cases h with
  | classical h =>
      cases h with
      | dne p => exact c_defined_dne (jPlus p)
      | exists_e =>
          change Classicism.Meta.C.Derivable []
            (Classicism.Meta.existence_e (Sig := signature Const)).close
          exact Classicism.Meta.Derivable.ax rfl
  | definition n => exact nameDefinition_toC n Γ

#print axioms name_body_identity
#print axioms jPlus_diagram
#print axioms coextC_of_identity
#print axioms name_uniform_definition
#print axioms nameDefinition_toC
#print axioms named_axioms_toC

end Classicism.Research.ModalNamedToC
