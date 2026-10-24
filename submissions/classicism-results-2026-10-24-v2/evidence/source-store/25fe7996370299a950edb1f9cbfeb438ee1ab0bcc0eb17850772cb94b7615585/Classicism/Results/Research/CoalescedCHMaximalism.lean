import Classicism.Results.Research.CoalescedCHModal
import Classicism.Results.Research.CoalescedCHVocabularyCertificates

/-!
# The conditional Maximalism obstruction for structural CH

Original research, misc, Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. The two explicit consistency hypotheses concern existential
sentences asserting a real structure with CH and a real structure without CH.
Neither is replaced by consistency of bare CH, and neither is asserted here.

In particular this module does not construct an internal Henkin reduct of a
model of ZFC, prove its existence from Con(ZFC), or certify the unconditional
database incompatibility. Its modal conclusion is an actual derivability and
consistency statement about C, conditional on exactly the remaining witnesses.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Classicism.Meta.Research.CoalescedCH

open AxiomSet

noncomputable abbrev existsRealCH (σ : Ty) : Sentence Signature.pure :=
  Classicism.Research.CoalescedCH.HasRealCH.quoted σ

noncomputable abbrev existsRealNotCH (σ : Ty) : Sentence Signature.pure :=
  Classicism.Research.CoalescedCH.HasRealNotCH.quoted σ

/-- The canonical boxed-universal sentence, not merely a chosen normal form. -/
noncomputable abbrev nonContingency (σ : Ty) : Sentence Signature.pure :=
  Classicism.Research.CoalescedCH.NonContingency.quoted σ

theorem existsRealCH_pure (σ : Ty) : (existsRealCH σ).pure = true :=
  Term.pure_of_pureSig _

theorem existsRealNotCH_pure (σ : Ty) : (existsRealNotCH σ).pure = true :=
  Term.pure_of_pureSig _

theorem nonContingency_pure (σ : Ty) : (nonContingency σ).pure = true :=
  Term.pure_of_pureSig _

theorem existsRealCH_closedTypes (σ : Ty) (hσ : σ.Closed) :
    (existsRealCH σ).closedTypes = true := by
  simp [existsRealCH, Classicism.Research.CoalescedCH.HasRealCH.quoted,
    Term.closedTypes, hσ]

theorem existsRealNotCH_closedTypes (σ : Ty) (hσ : σ.Closed) :
    (existsRealNotCH σ).closedTypes = true := by
  simp [existsRealNotCH, Classicism.Research.CoalescedCH.HasRealNotCH.quoted,
    Term.closedTypes, hσ]

theorem nonContingency_closedTypes (σ : Ty) (hσ : σ.Closed) :
    (nonContingency σ).closedTypes = true := by
  simp [nonContingency, Classicism.Research.CoalescedCH.NonContingency.quoted,
    Term.closedTypes, hσ]

/-- The source sentence and the two-witness normal form are C-identical. -/
theorem normal_form_derivable (σ : Ty) :
    C.TheoremMinus (Term.eq' (nonContingency σ)
      (eitherBoxNeg (existsRealNotCH σ) (existsRealCH σ))) :=
  Classicism.Research.CoalescedCH.normal_form.derivable σ

theorem nonContingency_entails_normal (σ : Ty) :
    single (nonContingency σ) ⟹
      single (eitherBoxNeg (existsRealNotCH σ) (existsRealCH σ)) := by
  rintro a rfl
  exact Derivable.eqMp (Theorem.ofCMinus (normal_form_derivable σ)) (Theorem.ax rfl)

theorem normal_entails_nonContingency (σ : Ty) :
    single (eitherBoxNeg (existsRealNotCH σ) (existsRealCH σ)) ⟹
      single (nonContingency σ) := by
  rintro a rfl
  exact Derivable.eqMpr (Theorem.ofCMinus (normal_form_derivable σ)) (Theorem.ax rfl)

theorem possibility_inconsistent (σ : Ty) (hσ : σ.Closed)
    (hCH : Consistent (single (existsRealCH σ)))
    (hNotCH : Consistent (single (existsRealNotCH σ))) :
    ¬ Consistent (possibility (empty : AxiomSet Signature.pure) ∪
      single (nonContingency σ)) := by
  intro hc
  exact possibility_two_inconsistent (existsRealNotCH σ) (existsRealCH σ)
    (existsRealNotCH_closedTypes σ hσ) (existsRealCH_closedTypes σ hσ) hNotCH hCH
    (Consistent.of_entails
      (Entails.union (Entails.union_left _ _)
        (Entails.mono_left (subset_union_right _ _) (nonContingency_entails_normal σ))) hc)

/-- Pure Distinctness alone already suffices; no signature constants occur. -/
theorem distinctness_inconsistent (σ : Ty) (hσ : σ.Closed)
    (hCH : Consistent (single (existsRealCH σ)))
    (hNotCH : Consistent (single (existsRealNotCH σ))) :
    ¬ Consistent (distinctness (empty : AxiomSet Signature.pure) ∪
      single (nonContingency σ)) := by
  intro hc
  exact distinctness_two_inconsistent (existsRealNotCH σ) (existsRealCH σ)
    (existsRealNotCH_closedTypes σ hσ) (existsRealCH_closedTypes σ hσ) hNotCH hCH
    (Consistent.of_entails
      (Entails.union (Entails.union_left _ _)
        (Entails.mono_left (subset_union_right _ _) (nonContingency_entails_normal σ))) hc)

theorem maximalism_inconsistent (σ : Ty) (hσ : σ.Closed)
    (hCH : Consistent (single (existsRealCH σ)))
    (hNotCH : Consistent (single (existsRealNotCH σ))) :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ single (nonContingency σ)) := by
  intro hc
  exact maximalism_two_inconsistent (existsRealNotCH σ) (existsRealCH σ)
    (existsRealNotCH_closedTypes σ hσ) (existsRealCH_closedTypes σ hσ) hNotCH hCH
    (Consistent.of_entails
      (Entails.union (Entails.union_left _ _)
        (Entails.mono_left (subset_union_right _ _) (nonContingency_entails_normal σ))) hc)

/-- One type instance refutes the entire non-contingency schema. -/
theorem maximalism_schema_inconsistent (σ : Ty) (hσ : σ.Closed)
    (hCH : Consistent (single (existsRealCH σ)))
    (hNotCH : Consistent (single (existsRealNotCH σ))) :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪
      Classicism.Research.CoalescedCH.NonContingency.schema) := by
  intro hc
  apply maximalism_inconsistent σ hσ hCH hNotCH
  apply Consistent.mono (Ax₁ := maximalist (Sig := Signature.pure) ∪
    Classicism.Research.CoalescedCH.NonContingency.schema) _ hc
  intro a ha
  rcases ha with ha | rfl
  · exact Or.inl ha
  · exact Or.inr ⟨σ, hσ, rfl⟩

open CategoryTheory Intensional

/-- This is the application interface for a coalesced model: opposite witnesses
at accessible objects refute the canonical source sentence at the root. -/
theorem not_holds_nonContingency_of_accessible
    {K : Type} [SmallCategory K] (A : Premodel Signature.pure K) (hA : A.IsModel)
    (σ : Ty) {W V : K} (u : A.W₀ ⟶ W) (v : A.W₀ ⟶ V)
    (hNotCH : A.Holds u (existsRealNotCH σ) .nil)
    (hCH : A.Holds v (existsRealCH σ) .nil) :
    ¬ A.HoldsSentence (nonContingency σ) := by
  intro h
  have hn := A.entails_holds hA (nonContingency_entails_normal σ) (A.holdsAx_single h)
  exact not_holds_eitherBoxNeg_of_accessible A hA
    (existsRealNotCH σ) (existsRealCH σ) u v hNotCH hCH (hn _ rfl)

#print axioms normal_form_derivable
#print axioms maximalism_inconsistent
#print axioms maximalism_schema_inconsistent
#print axioms not_holds_nonContingency_of_accessible

end Classicism.Meta.Research.CoalescedCH
