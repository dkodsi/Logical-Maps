import StrongPossibilityConsequencesMaxDiagram
import StrongPossibilityConsequencesReflection

/-!
# Max-consistency is exactly conservativity for closed typed identities

Source: notes/max-degree.md §11, theory-space-comparison.md §9.
Direct source of this finite-support proof implementation: misc.

The converse is implemented, not assumed: from a contradiction with Max,
extract finitely many Max inequalities, discharge their conjunction Q, and
turn not Q into the closed identity (not Q)=top. Identity-conservativity would
make that identity a C theorem, contradicting the explicitly retained Con(Max).
No standard-arithmetic model or effective coding assumption is involved.
-/

namespace Classicism.Research.StrongPossibilityConsequences.Conservativity

theorem reflected_neg_box (p : Prop) : (◇ p → p) → ¬ p → □ (¬ p) := by
  intro href hp
  rw [box_not_eq]
  exact (em (p = False)).elim (fun h => h) (fun h => (hp (href h)).elim)

#classicism_check reflected_neg_box
#classicism_types reflected_neg_box
#classicism_derive reflected_neg_box

end Classicism.Research.StrongPossibilityConsequences.Conservativity

namespace Classicism.Meta.Research.StrongPossibilityConsequences.MaxConservativity

open AxiomSet
open Reflection

variable {Sig : Signature}

def IdentityConservative (Ax : AxiomSet Sig) : Prop :=
  ∀ (σ : Ty) (x y : Term Sig [] σ), (Term.eq' x y).closedTypes = true →
    Theorem (C.axioms ∪ Ax) (Term.eq' x y) → C.Theorem (Term.eq' x y)

theorem conjunction_closed : ∀ L : List (Sentence Sig),
    (∀ a ∈ L, a.closedTypes = true) → (conjunction L).closedTypes = true
  | [], _ => rfl
  | a :: L, h => by
    change (Term.conj a (conjunction L)).closedTypes = true
    simp only [Term.closedTypes_conj, h a (List.mem_cons_self),
      conjunction_closed L (fun b hb => h b (List.mem_cons_of_mem _ hb)), Bool.and_true]

theorem identity_conservative_of_max_consistent {Ax : AxiomSet Sig}
    (hcon : Consistent ((maximalist : AxiomSet Sig) ∪ Ax)) : IdentityConservative Ax := by
  intro σ x y hc hxy
  apply (MaxDiagram.identity_iff hcon (Entails.of_subset (subset_union_left _ _)) x y hc).mp
  exact Derivable.mono (fun _ ha => ha.elim Or.inl (fun h => Or.inr (Or.inr h))) hxy

/-- The nontrivial converse. The only consistency input is for original Max
itself; no Max+Ax consistency premise occurs. -/
theorem max_consistent_of_identity_conservative
    (hM : Consistent (maximalist : AxiomSet Sig)) {Ax : AxiomSet Sig}
    (hconserv : IdentityConservative Ax) : Consistent (maximalist ∪ Ax) := by
  classical
  intro hbot
  obtain ⟨L, hL, hd⟩ := FiniteChoiceBasis.finiteSupport hbot
  let K := L.filter (fun a => decide ((maximalist : AxiomSet Sig) a))
  have hK : ∀ a ∈ K, (maximalist : AxiomSet Sig) a := by
    intro a ha
    have : a ∈ L ∧ (maximalist : AxiomSet Sig) a := by simpa [K] using ha
    exact this.2
  have hKclosed : (conjunction K).closedTypes = true :=
    conjunction_closed K (fun a ha => (hK a ha).elim False.elim (fun h => h.1))
  have hQ : Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) (conjunction K) :=
    conjunction_intro K (fun a ha => Theorem.ax (hK a ha))
  have hcut : Ax ∪ single (conjunction K) ⟹ FiniteChoiceBasis.ofList L := by
    intro a ha
    change a ∈ L at ha
    by_cases hm : (maximalist : AxiomSet Sig) a
    · have hak : a ∈ K := by simp [K, ha, hm]
      exact conjunction_elim K (Theorem.ax (Or.inr rfl)) a hak
    · have hax : Ax a := (hL a ha).resolve_left hm
      exact Theorem.ax (Or.inl hax)
  have hbad : Theorem (C.axioms ∪ (Ax ∪ single (conjunction K))) Term.bot :=
    Derivable.cut hcut hd
  have hnot : Theorem (C.axioms ∪ Ax) (Term.neg (conjunction K)) :=
    Derivable.notI
      (Derivable.impE (Derivable.weaken₁ (Theorem.deductionC hbad)) Derivable.hyp₀)
      (Derivable.notI (Derivable.andE₁ Derivable.hyp₀) (Derivable.andE₂ Derivable.hyp₀))
  have hreflect := conjunction_reflects K (fun a ha => maximalist_axiom_reflects (hK a ha))
  have hbox : Theorem (C.axioms ∪ Ax) (Term.box (Term.neg (conjunction K))) :=
    Theorem.mp₂ (Theorem.ofCMinus (Derivable.allEβ
      (C.TheoremMinus.ofPure
        Classicism.Research.StrongPossibilityConsequences.Conservativity.reflected_neg_box.derivable)
      (conjunction K))) (Theorem.ofC hreflect) hnot
  have heq : C.Theorem (Term.box (Term.neg (conjunction K))) :=
    hconserv Ty.t (Term.neg (conjunction K)) Term.top (by simpa using hKclosed) hbox
  have hCnot : C.Theorem (Term.neg (conjunction K)) :=
    Derivable.eqMpr heq Derivable.top
  exact hM (Derivable.notE hQ (Theorem.ofC hCnot))

theorem identity_conservative_iff_max_consistent
    (hM : Consistent (maximalist : AxiomSet Sig)) (Ax : AxiomSet Sig) :
    IdentityConservative Ax ↔ Consistent (maximalist ∪ Ax) :=
  ⟨max_consistent_of_identity_conservative hM, identity_conservative_of_max_consistent⟩

#print axioms identity_conservative_iff_max_consistent

end Classicism.Meta.Research.StrongPossibilityConsequences.MaxConservativity
