import Classicism.Results.Research.FiniteTypePropagationCertificates

/-!
# Finite base types propagate through the whole admitted type grammar

Direct source: research/2026-10-22/proof-refinements/finite-type-propagation.md,
§§1–4, unpaginated original research (misc). This is metatheory assembling
translated C derivations. It does not identify a uniform type-finiteness
derivation with a recursive model interpretation.
-/
namespace Classicism.Meta.Research.FiniteTypePropagation
open AxiomSet Classicism.Research.FiniteTypePropagation

def FiniteBases : AxiomSet Signature.pure :=
  single (FiniteDomain.quoted .e) ∪ single (FiniteDomain.quoted .t)

section induction
variable {Ax : AxiomSet Signature.pure}
mutual
  private theorem finite_type
      (he : Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted .e))
      (ht : Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted .t))
      (step : ∀ (σ : Ty) (ρ : RTy), σ.Closed → ρ.Closed →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted σ) →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel ρ)) →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel (σ ⇒ ρ)))) :
      ∀ (σ : Ty), σ.Closed →
      Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted σ)
    | .e, _ => he
    | .rel ρ, hρ => finite_relation he ht step ρ hρ
    | .var _, h => h.elim
  private theorem finite_relation
      (he : Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted .e))
      (ht : Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted .t))
      (step : ∀ (σ : Ty) (ρ : RTy), σ.Closed → ρ.Closed →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted σ) →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel ρ)) →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel (σ ⇒ ρ)))) :
      ∀ (ρ : RTy), ρ.Closed →
      Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel ρ))
    | .t, _ => ht
    | .arr σ ρ, h => step σ ρ h.1 h.2
        (finite_type he ht step σ h.1) (finite_relation he ht step ρ h.2)
end
end induction

theorem functionality_finite_bases_imply_all_finite :
    (Classicism.P.Functionality.schema ∪ FiniteBases) ⟹ FiniteDomain.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  apply finite_type
    (Theorem.ax (Or.inr (Or.inl rfl)))
    (Theorem.ax (Or.inr (Or.inr rfl)))
    (fun τ ρ hτ hρ hτfin hρfin =>
      (((Theorem.ofC (finite_arrow_of_functionality.rule τ ρ)).mp
        (Theorem.ax (Or.inl ⟨τ, ρ, hτ, hρ, rfl⟩))).mp hτfin).mp hρfin)
    σ hσ

theorem barcan_finite_bases_imply_all_finite :
    (Classicism.P.Barcan.schema ∪ FiniteBases) ⟹ FiniteDomain.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  apply finite_type
    (Theorem.ax (Or.inr (Or.inl rfl)))
    (Theorem.ax (Or.inr (Or.inr rfl)))
    (fun τ ρ hτ _ hτfin hρfin =>
      (((Theorem.ofC (finite_arrow_of_barcan.rule τ ρ)).mp
        (Theorem.ax (Or.inl ⟨τ, hτ, rfl⟩))).mp hτfin).mp hρfin)
    σ hσ

theorem all_finite_implies_finite_bases : FiniteDomain.schema ⟹ FiniteBases := by
  intro a h
  rcases h with h | h
  · exact Theorem.ax ⟨Ty.e, Ty.closed_e, h⟩
  · exact Theorem.ax ⟨Ty.t, RTy.closed_t, h⟩

theorem c5_finite_bases_imply_all_finite :
    (Classicism.P.NecNecessityOfDistinctnessT.schema ∪ FiniteBases) ⟹
      FiniteDomain.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  apply finite_type
    (Theorem.ax (Or.inr (Or.inl rfl)))
    (Theorem.ax (Or.inr (Or.inr rfl)))
    (fun τ ρ _ _ hτfin hρfin =>
      (((Theorem.ofC (finite_arrow_of_c5.rule τ ρ)).mp
        (Theorem.ax (Or.inl rfl))).mp hτfin).mp hρfin)
    σ hσ

theorem relational_finite_implies_all_finite :
    FiniteRelDomain.schema ⟹ FiniteDomain.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  cases σ with
  | e =>
    exact (Theorem.ofC (finite_base_of_finite_predicates.rule .e)).mp
      (Theorem.ax ⟨Ty.e ⇒ RTy.t, ⟨Ty.closed_e, RTy.closed_t⟩, rfl⟩)
  | rel ρ =>
    exact (Theorem.ofC (finite_domain_of_rel.rule ρ)).mp
      (Theorem.ax ⟨ρ, hσ, rfl⟩)
  | var i => exact hσ.elim

theorem c5_finite_bases_imply_necessary_all_finite :
    (Classicism.P.NecNecessityOfDistinctnessT.schema ∪ FiniteBases) ⟹
      NecessaryFiniteDomain.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  exact ((Theorem.ofC (finite_domain_necessary_c5.rule σ)).mp
    (Theorem.ax (Or.inl rfl))).mp
    (c5_finite_bases_imply_all_finite _ ⟨σ, hσ, rfl⟩)

theorem necessary_all_finite_implies_all_finite :
    NecessaryFiniteDomain.schema ⟹ FiniteDomain.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  exact (Theorem.ofC (finite_domain_of_necessary.rule σ)).mp
    (Theorem.ax ⟨σ, hσ, rfl⟩)

theorem all_finite_implies_relational_finite :
    FiniteDomain.schema ⟹ FiniteRelDomain.schema := by
  rintro a ⟨ρ, hρ, rfl⟩
  exact (Theorem.ofC (finite_rel_domain.rule ρ)).mp
    (Theorem.ax ⟨Ty.rel ρ, hρ, rfl⟩)

theorem all_and_relational_finiteness_equivalent :
    (FiniteDomain.schema ⟹ FiniteRelDomain.schema) ∧
    (FiniteRelDomain.schema ⟹ FiniteDomain.schema) :=
  ⟨all_finite_implies_relational_finite, relational_finite_implies_all_finite⟩

end Classicism.Meta.Research.FiniteTypePropagation

#print axioms Classicism.Meta.Research.FiniteTypePropagation.functionality_finite_bases_imply_all_finite
#print axioms Classicism.Meta.Research.FiniteTypePropagation.barcan_finite_bases_imply_all_finite
#print axioms Classicism.Meta.Research.FiniteTypePropagation.c5_finite_bases_imply_all_finite
#print axioms Classicism.Meta.Research.FiniteTypePropagation.c5_finite_bases_imply_necessary_all_finite
#print axioms Classicism.Meta.Research.FiniteTypePropagation.all_and_relational_finiteness_equivalent
