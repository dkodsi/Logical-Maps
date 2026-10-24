import Classicism.Results.Research.FiniteTypeDescentCertificates
import Classicism.Syntax.Inhabited

/-!
# Exact finite-base requirements for each closed type

Direct source: research/2026-10-22/proof-refinements/finite-type-propagation.md,
§§5–6, unpaginated original research (misc). The two directions below build
actual C derivations. The necessary base premises are computed from the finite
type tree; Functionality is explicit in the sufficient direction only.
-/
namespace Classicism.Meta.Research.FiniteTypeDescent
open AxiomSet Classicism.Research.FiniteTypePropagation
open Classicism.Research.FiniteTypeDescent

private theorem closed_existence (σ : Ty) (hc : σ.Closed) :
    C.Theorem (Classicism.P.Existence.quoted σ) := by
  change C.Theorem (Term.exists' (σ := σ) (Term.eq' Term.v0 Term.v0))
  apply Derivable.of_forall_weaken C.axioms.existence_e σ hc
  apply Derivable.allI
  exact Derivable.exIβ (Term.var .zero) (Derivable.refl (Term.var .zero))

private theorem collapse_output {Ax : AxiomSet Signature.pure} (σ : Ty) :
    ∀ (ρ : RTy), ρ.Closed →
      Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel (σ ⇒ ρ))) →
      Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel (σ ⇒ .t)))
  | .t, _, hf => hf
  | .arr τ ρ, hc, hf =>
    collapse_output σ ρ hc.2
      (((Theorem.ofC (finite_delete_output_argument.rule σ τ ρ)).mp
        (Theorem.ofC (closed_existence τ hc.1))).mp hf)

private theorem input_finite {Ax : AxiomSet Signature.pure}
    (σ : Ty) (ρ : RTy) (hc : ρ.Closed)
    (hf : Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel (σ ⇒ ρ)))) :
    Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted σ) :=
  (Theorem.ofC (finite_input_of_predicate.rule σ)).mp (collapse_output σ ρ hc hf)

private theorem output_finite {Ax : AxiomSet Signature.pure}
    (σ : Ty) (ρ : RTy) (hc : σ.Closed)
    (hf : Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel (σ ⇒ ρ)))) :
    Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel ρ)) :=
  ((Theorem.ofC (finite_output_of_arrow.rule σ ρ)).mp
    (Theorem.ofC (closed_existence σ hc))).mp hf

theorem finite_arrow_implies_finite_input (σ : Ty) (ρ : RTy) (hc : ρ.Closed) :
    single (FiniteDomain.quoted (.rel (σ ⇒ ρ))) ⟹ single (FiniteDomain.quoted σ) := by
  rintro a rfl
  exact input_finite σ ρ hc (Theorem.ax rfl)

theorem finite_arrow_implies_finite_output (σ : Ty) (ρ : RTy) (hc : σ.Closed) :
    single (FiniteDomain.quoted (.rel (σ ⇒ ρ))) ⟹
      single (FiniteDomain.quoted (.rel ρ)) := by
  rintro a rfl
  exact output_finite σ ρ hc (Theorem.ax rfl)

mutual
  def BaseRequirements : Ty → AxiomSet Signature.pure
    | .e => single (FiniteDomain.quoted .e)
    | .rel ρ => RelBaseRequirements ρ
    | .var _ => empty
  def RelBaseRequirements : RTy → AxiomSet Signature.pure
    | .t => single (FiniteDomain.quoted .t)
    | .arr σ ρ => BaseRequirements σ ∪ RelBaseRequirements ρ
end

mutual
  private theorem requirements_of_finite {Ax : AxiomSet Signature.pure} :
      ∀ (σ : Ty), σ.Closed →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted σ) →
        ∀ a, BaseRequirements σ a → Theorem (C.axioms ∪ Ax) a
    | .e, _, hf, _, h => by cases h; exact hf
    | .rel ρ, hc, hf, a, h => rel_requirements_of_finite ρ hc hf a h
    | .var _, hc, _, _, _ => hc.elim
  private theorem rel_requirements_of_finite {Ax : AxiomSet Signature.pure} :
      ∀ (ρ : RTy), ρ.Closed →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel ρ)) →
        ∀ a, RelBaseRequirements ρ a → Theorem (C.axioms ∪ Ax) a
    | .t, _, hf, _, h => by cases h; exact hf
    | .arr σ ρ, hc, hf, a, h => by
      cases h with
      | inl h => exact requirements_of_finite σ hc.1 (input_finite σ ρ hc.2 hf) a h
      | inr h => exact rel_requirements_of_finite ρ hc.2 (output_finite σ ρ hc.1 hf) a h
end

mutual
  private theorem finite_of_requirements {Ax : AxiomSet Signature.pure}
      (hfn : ∀ (σ : Ty) (ρ : RTy), σ.Closed → ρ.Closed →
        Theorem (C.axioms ∪ Ax) (Classicism.P.Functionality.quoted σ ρ)) :
      ∀ (σ : Ty), σ.Closed →
        (∀ a, BaseRequirements σ a → Theorem (C.axioms ∪ Ax) a) →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted σ)
    | .e, _, hr => hr _ rfl
    | .rel ρ, hc, hr => rel_finite_of_requirements hfn ρ hc hr
    | .var _, hc, _ => hc.elim
  private theorem rel_finite_of_requirements {Ax : AxiomSet Signature.pure}
      (hfn : ∀ (σ : Ty) (ρ : RTy), σ.Closed → ρ.Closed →
        Theorem (C.axioms ∪ Ax) (Classicism.P.Functionality.quoted σ ρ)) :
      ∀ (ρ : RTy), ρ.Closed →
        (∀ a, RelBaseRequirements ρ a → Theorem (C.axioms ∪ Ax) a) →
        Theorem (C.axioms ∪ Ax) (FiniteDomain.quoted (.rel ρ))
    | .t, _, hr => hr _ rfl
    | .arr σ ρ, hc, hr =>
      (((Theorem.ofC (finite_arrow_of_functionality.rule σ ρ)).mp
        (hfn σ ρ hc.1 hc.2)).mp
        (finite_of_requirements hfn σ hc.1 (fun a h => hr a (Or.inl h)))).mp
        (rel_finite_of_requirements hfn ρ hc.2 (fun a h => hr a (Or.inr h)))
end

theorem finiteness_implies_base_requirements (σ : Ty) (hc : σ.Closed) :
    single (FiniteDomain.quoted σ) ⟹ BaseRequirements σ :=
  requirements_of_finite σ hc (Theorem.ax rfl)

theorem functionality_base_requirements_imply_finiteness (σ : Ty) (hc : σ.Closed) :
    (Classicism.P.Functionality.schema ∪ BaseRequirements σ) ⟹
      single (FiniteDomain.quoted σ) := by
  rintro a rfl
  exact finite_of_requirements
    (fun τ ρ hτ hρ => Theorem.ax (Or.inl ⟨τ, ρ, hτ, hρ, rfl⟩)) σ hc
    (fun a h => Theorem.ax (Or.inr h))

mutual
  def OccursE : Ty → Prop
    | .e => True
    | .rel ρ => RelOccursE ρ
    | .var _ => False
  def RelOccursE : RTy → Prop
    | .t => False
    | .arr σ ρ => OccursE σ ∨ RelOccursE ρ
end

mutual
  private def OccursT : Ty → Prop
    | .e => False
    | .rel ρ => RelOccursT ρ
    | .var _ => False
  private def RelOccursT : RTy → Prop
    | .t => True
    | .arr σ ρ => OccursT σ ∨ RelOccursT ρ
end

mutual
  private theorem requirements_iff (a : Sentence Signature.pure) :
      ∀ (σ : Ty), σ.Closed →
        (BaseRequirements σ a ↔
          (OccursT σ ∧ a = FiniteDomain.quoted .t) ∨
          (OccursE σ ∧ a = FiniteDomain.quoted .e))
    | .e, _ => by simp [BaseRequirements, OccursT, OccursE, AxiomSet.single]
    | .rel ρ, hc => rel_requirements_iff a ρ hc
    | .var _, hc => hc.elim
  private theorem rel_requirements_iff (a : Sentence Signature.pure) :
      ∀ (ρ : RTy), ρ.Closed →
        (RelBaseRequirements ρ a ↔
          (RelOccursT ρ ∧ a = FiniteDomain.quoted .t) ∨
          (RelOccursE ρ ∧ a = FiniteDomain.quoted .e))
    | .t, _ => by simp [RelBaseRequirements, RelOccursT, RelOccursE, AxiomSet.single]
    | .arr σ ρ, hc => by
      change (BaseRequirements σ a ∨ RelBaseRequirements ρ a) ↔
        ((OccursT σ ∨ RelOccursT ρ) ∧ a = FiniteDomain.quoted .t) ∨
        ((OccursE σ ∨ RelOccursE ρ) ∧ a = FiniteDomain.quoted .e)
      rw [requirements_iff a σ hc.1, rel_requirements_iff a ρ hc.2]
      constructor
      · rintro ((⟨hT, ha⟩ | ⟨hE, ha⟩) | (⟨hT, ha⟩ | ⟨hE, ha⟩))
        · exact Or.inl ⟨Or.inl hT, ha⟩
        · exact Or.inr ⟨Or.inl hE, ha⟩
        · exact Or.inl ⟨Or.inr hT, ha⟩
        · exact Or.inr ⟨Or.inr hE, ha⟩
      · rintro (⟨(hT | hT), ha⟩ | ⟨(hE | hE), ha⟩)
        · exact Or.inl (Or.inl ⟨hT, ha⟩)
        · exact Or.inr (Or.inl ⟨hT, ha⟩)
        · exact Or.inl (Or.inr ⟨hE, ha⟩)
        · exact Or.inr (Or.inr ⟨hE, ha⟩)
end

private theorem relational_type_has_t : ∀ (ρ : RTy), RelOccursT ρ
  | .t => True.intro
  | .arr _ ρ => Or.inr (relational_type_has_t ρ)

theorem relational_base_requirements_iff (ρ : RTy) (hc : ρ.Closed)
    (a : Sentence Signature.pure) :
    RelBaseRequirements ρ a ↔
      a = FiniteDomain.quoted .t ∨ (RelOccursE ρ ∧ a = FiniteDomain.quoted .e) := by
  constructor
  · intro h
    exact ((rel_requirements_iff a ρ hc).mp h).elim
      (fun h => Or.inl h.2) Or.inr
  · intro h
    exact (rel_requirements_iff a ρ hc).mpr
      (h.elim (fun ht => Or.inl ⟨relational_type_has_t ρ, ht⟩) Or.inr)

theorem relational_requirements_without_e (ρ : RTy) (hc : ρ.Closed)
    (he : ¬ RelOccursE ρ) :
    RelBaseRequirements ρ = single (FiniteDomain.quoted .t) := by
  funext a
  apply propext
  constructor
  · intro h
    exact ((relational_base_requirements_iff ρ hc a).mp h).elim
      (fun h => h) (fun h => (he h.1).elim)
  · intro h
    exact (relational_base_requirements_iff ρ hc a).mpr (Or.inl h)

theorem relational_requirements_with_e (ρ : RTy) (hc : ρ.Closed)
    (he : RelOccursE ρ) :
    RelBaseRequirements ρ =
      single (FiniteDomain.quoted .e) ∪ single (FiniteDomain.quoted .t) := by
  funext a
  apply propext
  constructor
  · intro h
    exact ((relational_base_requirements_iff ρ hc a).mp h).elim
      Or.inr (fun h => Or.inl h.2)
  · intro h
    exact (relational_base_requirements_iff ρ hc a).mpr
      (h.elim (fun h => Or.inr ⟨he, h⟩) Or.inl)

theorem finite_e_free_type_implies_finite_t (ρ : RTy) (hc : ρ.Closed)
    (he : ¬ RelOccursE ρ) :
    single (FiniteDomain.quoted (.rel ρ)) ⟹ single (FiniteDomain.quoted .t) := by
  rw [← relational_requirements_without_e ρ hc he]
  exact finiteness_implies_base_requirements (.rel ρ) hc

theorem functionality_finite_t_implies_finite_e_free_type (ρ : RTy) (hc : ρ.Closed)
    (he : ¬ RelOccursE ρ) :
    (Classicism.P.Functionality.schema ∪ single (FiniteDomain.quoted .t)) ⟹
      single (FiniteDomain.quoted (.rel ρ)) := by
  rw [← relational_requirements_without_e ρ hc he]
  exact functionality_base_requirements_imply_finiteness (.rel ρ) hc

theorem finite_e_containing_type_implies_finite_bases (ρ : RTy) (hc : ρ.Closed)
    (he : RelOccursE ρ) :
    single (FiniteDomain.quoted (.rel ρ)) ⟹
      (single (FiniteDomain.quoted .e) ∪ single (FiniteDomain.quoted .t)) := by
  rw [← relational_requirements_with_e ρ hc he]
  exact finiteness_implies_base_requirements (.rel ρ) hc

theorem functionality_finite_bases_imply_finite_e_containing_type
    (ρ : RTy) (hc : ρ.Closed) (he : RelOccursE ρ) :
    (Classicism.P.Functionality.schema ∪
      (single (FiniteDomain.quoted .e) ∪ single (FiniteDomain.quoted .t))) ⟹
      single (FiniteDomain.quoted (.rel ρ)) := by
  rw [← relational_requirements_with_e ρ hc he]
  exact functionality_base_requirements_imply_finiteness (.rel ρ) hc

end Classicism.Meta.Research.FiniteTypeDescent

#print axioms Classicism.Meta.Research.FiniteTypeDescent.finite_arrow_implies_finite_input
#print axioms Classicism.Meta.Research.FiniteTypeDescent.finite_arrow_implies_finite_output
#print axioms Classicism.Meta.Research.FiniteTypeDescent.finiteness_implies_base_requirements
#print axioms Classicism.Meta.Research.FiniteTypeDescent.functionality_base_requirements_imply_finiteness
#print axioms Classicism.Meta.Research.FiniteTypeDescent.finite_e_free_type_implies_finite_t
#print axioms Classicism.Meta.Research.FiniteTypeDescent.functionality_finite_t_implies_finite_e_free_type
#print axioms Classicism.Meta.Research.FiniteTypeDescent.finite_e_containing_type_implies_finite_bases
#print axioms Classicism.Meta.Research.FiniteTypeDescent.functionality_finite_bases_imply_finite_e_containing_type
