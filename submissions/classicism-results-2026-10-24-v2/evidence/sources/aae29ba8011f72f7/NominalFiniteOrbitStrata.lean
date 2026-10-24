import Classicism.Models.NominalStabilizerCriterion
import Classicism.Models.NominalWorldExamples
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Equiv.Basic

/-!
# Finite stabilizer orbits and the atom-world Dedekind obstruction

This implements the existing finite-orbit argument of
research/2026-10-22/notes/nominal-choice-classification-20261022.md §§2,6
(original research, unpaginated; direct source misc).

A supported proposition is determined by its values on orbit representatives.
For the full permutation action on atoms, every finite support has singleton
orbits inside it and at most one orbit outside it. Thus the finite-strata
premise is discharged for the concrete atom-world model, without assuming a
general orbit decomposition theorem. The arbitrary orbit-finite-world
classification still requires that separate theorem. Ordinary metatheory;
these proof bodies require a successful compiler and axiom audit.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

/-- Restriction to finitely many stabilizer-orbit representatives is injective. -/
theorem finite_proposition_stratum_of_representatives (W : Nom A I) (S : Set A)
    (R : Set W) (hR : R.Finite)
    (hcover : ∀ w : W, ∃ r ∈ R, SupportOrbit W S r w) :
    Finite {p : propositions W // Supports A (propositions W).obj S p} := by
  letI : Finite R := hR
  let code : {p : propositions W // Supports A (propositions W).obj S p} →
      (R → Prop) := fun p r => p.val.val r.val
  apply Finite.of_injective code
  intro p q he
  apply Subtype.ext
  apply Subtype.ext
  funext w
  obtain ⟨r, hr, g, hg, hgr⟩ := hcover w
  have hp := exponential_covariance W (trivialNom A I Prop) p.property g hg r
  have hq := exponential_covariance W (trivialNom A I Prop) q.property g hg r
  change p.val.val (W.obj.act g r) = p.val.val r at hp
  change q.val.val (W.obj.act g r) = q.val.val r at hq
  rw [hgr] at hp hq
  exact hp.trans ((congrFun he ⟨r, hr⟩).trans hq.symm)

theorem Hierarchy.not_dedInfT_of_finite_stabilizer_orbits (W : Nom A I)
    (horbits : ∀ S : Set A, I.Small S →
      ∃ R : Set W, R.Finite ∧ ∀ w : W, ∃ r ∈ R, SupportOrbit W S r w) (w : W) :
    ¬Hierarchy.Holds W (Hierarchy.pureConstants W) (Γ := []) () w Hierarchy.dedInfT := by
  apply Hierarchy.not_dedInfT_of_finite_strata W _ w
  intro S hS
  obtain ⟨R, hR, hc⟩ := horbits S hS
  exact finite_proposition_stratum_of_representatives W S R hR hc

namespace Examples

/-- The support itself and one fresh atom represent all support-fixer orbits. -/
theorem finite_atom_stabilizer_orbits (Atom : Type) (S : Set (atoms Atom))
    (hS : S.Finite) :
    ∃ R : Set (finiteAtomWorlds Atom), R.Finite ∧
      ∀ w : finiteAtomWorlds Atom, ∃ r ∈ R, SupportOrbit (finiteAtomWorlds Atom) S r w := by
  classical
  by_cases hfresh : ∃ a : Atom, a ∉ S
  · obtain ⟨a, ha⟩ := hfresh
    refine ⟨S ∪ {a}, hS.union (Set.finite_singleton a), ?_⟩
    intro w
    by_cases hw : w ∈ S
    · exact ⟨w, Or.inl hw, supportOrbit_self _ S w⟩
    · refine ⟨a, Or.inr (Set.mem_singleton a), Equiv.swap a w, ?_, ?_⟩
      · intro b hb
        change Equiv.swap a w b = b
        exact Equiv.swap_apply_of_ne_of_ne
          (fun he => ha (he ▸ hb)) (fun he => hw (he ▸ hb))
      · exact Equiv.swap_apply_left a w
  · refine ⟨S, hS, ?_⟩
    intro w
    have hw : w ∈ S := Classical.byContradiction (fun hn => hfresh ⟨w, hn⟩)
    exact ⟨w, hw, supportOrbit_self _ S w⟩

theorem finite_atom_proposition_strata (Atom : Type) (S : Set (atoms Atom))
    (hS : S.Finite) :
    Finite {p : propositions (finiteAtomWorlds Atom) //
      Supports (atoms Atom) (propositions (finiteAtomWorlds Atom)).obj S p} := by
  obtain ⟨R, hR, hc⟩ := finite_atom_stabilizer_orbits Atom S hS
  exact finite_proposition_stratum_of_representatives _ S R hR hc

/-- No extra finiteness premise remains in this concrete original-sentence verdict. -/
theorem finite_atoms_not_dedInfT (Atom : Type) (w : finiteAtomWorlds Atom) :
    ¬Hierarchy.Holds (finiteAtomWorlds Atom) (Hierarchy.pureConstants _) (Γ := []) () w
      Hierarchy.dedInfT :=
  Hierarchy.not_dedInfT_of_finite_strata _ (finite_atom_proposition_strata Atom) w

theorem finite_atoms_boxed_not_dedInfT (Atom : Type) (w : finiteAtomWorlds Atom) :
    Hierarchy.Holds (finiteAtomWorlds Atom) (Hierarchy.pureConstants _) (Γ := []) () w
      (Term.box (Term.neg Hierarchy.dedInfT)) := by
  apply (Hierarchy.holds_box _ _ (Γ := []) _ () w).2
  intro v
  exact (Hierarchy.holds_not _ _ (Γ := []) () v _).2 (finite_atoms_not_dedInfT Atom v)

end Examples
end
end Classicism.Meta.Nominal
