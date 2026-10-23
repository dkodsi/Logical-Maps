import Classicism.Results.Research.SectionsRetractionsPersistenceCertificates

/-!
# Tuple existence used by the relational masks

This small supporting certificate spells out C's ordinary Existence axiom and
the finite-tuple induction used in `Classicism.Results.Lists`. It keeps this
family independent of the full record audit. Direct mathematical source:
Classicism, §1.1 (nonempty types); local mask proof in
`research/2026-10-22/notes/choice-uniformization.md`, §11 (unpaginated).
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def ExistenceTailCons (τ σ : Type) [Ty τ] [Ty σ] : Prop :=
  ∃ (x : σ) (y : τ), x = x ∧ y = y

theorem mask_existence_e : Existence e := existence_e
theorem mask_existence_rel {τ : Type} [Rel τ] : Existence τ := existence_rel
theorem mask_existence_nil : True := trivial
theorem mask_existence_cons {τ σ : Type} [Ty τ] [Ty σ] :
    Existence τ → Existence σ → ExistenceTailCons τ σ :=
  fun ht hs => hs.elim fun x hx => ht.elim fun y hy => ⟨x, y, hx, hy⟩

end Classicism.Research.Splitting

#classicism_schema Classicism.Research.Splitting.ExistenceTailCons
#classicism_derive Classicism.Research.Splitting.mask_existence_nil
#classicism_certify Classicism.Research.Splitting.mask_existence_e
  Classicism.Research.Splitting.mask_existence_rel
  Classicism.Research.Splitting.mask_existence_cons
#classicism_entails Classicism.Research.Splitting.mask_existence_e
  Classicism.Research.Splitting.mask_existence_rel

namespace Classicism.Meta.Research.Splitting
open AxiomSet Classicism.Research.Splitting

theorem mask_single_existence : empty ⟹ P.Existence.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  cases σ with
  | e => exact mask_existence_e.entails _ rfl
  | rel ρ => exact mask_existence_rel.entails _ ⟨ρ, hσ, rfl⟩
  | var i => exact hσ.elim

theorem mask_list_existence : empty ⟹ P.Existence.listSchema := by
  rintro a ⟨σs, hσs, rfl⟩
  induction σs with
  | nil => exact Theorem.ofCMinus mask_existence_nil.derivable
  | cons σ τs ih =>
    cases τs with
    | nil =>
      exact (mask_single_existence _ ⟨σ, hσs.head, rfl⟩).cast
        (P.Existence.listQuoted_single σ).symm
    | cons τ τs =>
      exact (Theorem.ofC (mask_existence_cons.listRule (τ :: τs) σ hσs.head)).mp₂
        (ih hσs.tail) (mask_single_existence _ ⟨σ, hσs.head, rfl⟩)

end Classicism.Meta.Research.Splitting

#print axioms Classicism.Meta.Research.Splitting.mask_list_existence
