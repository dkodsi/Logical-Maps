import Classicism.Results.Research.ModalFiniteNameSupport

/-!
# Actual proof transport along a fixed typed constant map

Original research, misc, 23 October 2026. Unlike arbitrary constant
interpretation, a fixed syntactic map can preserve named definitions.
Only individual global axiom instances require a map; preservation of
whole proofs is proved by induction on the actual derivation constructors.
Optional premises stay local, including in the empty-context Nec case.
-/

namespace Classicism.Research.ModalFiniteNameSupport
open Classicism.Meta
open ModalComprehensionConcreteSyntax

variable {C D : Ty → Type}

theorem classical_map {Γ p} (f : ConstMap C D) (h : ClassicalAxioms C Γ p) :
    ClassicalAxioms D Γ (mapTerm f p) := by
  cases h with
  | dne p => exact .dne (mapTerm f p)
  | exists_e => exact .exists_e

theorem derives_map (f : ConstMap C D) {Ax : Axioms C} {Ay : Axioms D}
    (axiomMap : ∀ Γ p, Ax Γ p → Derives D Ay Γ [] (mapTerm f p))
    {Γ Δ p} (proof : Derives C Ax Γ Δ p) :
    Derives D Ay Γ (Δ.map (mapTerm f)) (mapTerm f p) := by
  induction proof with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | ax h => exact (axiomMap _ _ h).lift
  | weaken h _ ih =>
      apply Derives.weaken ?_ ih
      intro q hq
      rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
      exact List.mem_map_of_mem (h r hr)
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | iffI _ _ ih₁ ih₂ => exact .iffI ih₁ ih₂
  | iffE₁ _ _ ih₁ ih₂ => exact .iffE₁ ih₁ ih₂
  | iffE₂ _ _ ih₁ ih₂ => exact .iffE₂ ih₁ ih₂
  | topI => exact .topI
  | eqRefl a => exact .eqRefl (mapTerm f a)
  | eqSymm _ ih => exact .eqSymm ih
  | eqTrans _ _ ih₁ ih₂ => exact .eqTrans ih₁ ih₂
  | eqApp _ _ ih₁ ih₂ => exact .eqApp ih₁ ih₂
  | eqRight a _ ih => exact .eqRight (mapTerm f a) ih
  | eqTruth _ _ ih₁ ih₂ => exact .eqTruth ih₁ ih₂
  | eqSubst P a b _ _ ihEq ihP =>
      rw [mapTerm_inst] at ihP ⊢
      exact .eqSubst (mapTerm f P) (mapTerm f a) (mapTerm f b) ihEq ihP
  | allI _ ih =>
      apply Derives.allI
      simpa only [List.map_map, Function.comp_def, mapTerm_wk] using ih
  | allE a _ ih =>
      rw [mapTerm_inst]
      exact .allE (mapTerm f a) ih
  | exI a _ ih =>
      apply Derives.exI (mapTerm f a)
      simpa only [mapTerm_inst] using ih
  | exE _ _ ihEx ihQ =>
      apply Derives.exE ihEx
      simpa only [List.map_cons, List.map_map, Function.comp_def, mapTerm_wk] using ihQ
  | nec _ ih => exact .nec ih
  | K _ _ ih₁ ih₂ => exact .K ih₁ ih₂
  | intensionality ρ a b _ ih =>
      apply Derives.intensionality ρ (mapTerm f a) (mapTerm f b)
      simpa only [Term.box, mapTerm, mapTerm_coext] using ih
  | comprehension A =>
      change Derives D Ay _ _ (.ex (mapTerm f (Body.code A)))
      rw [mapTerm_body_code]
      exact .comprehension (mapBody f A)

#print axioms classical_map
#print axioms derives_map

end Classicism.Research.ModalFiniteNameSupport
