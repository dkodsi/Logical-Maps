import Classicism.Models.NominalFiniteOrbitStrata
import Mathlib.Data.Set.Finite.Lattice

/-!
# All-type Intensional Choice for finite-support atom worlds

The atom world action has Intensional Choice for every finitely supported
witness action. One swap transports a witness at a fresh atom to each world
outside the support of the family. A finite union absorbs the supports of the
remaining finitely many witnesses. The established support-stabilizer criterion
then supplies the selector graph. No least-support or orbit-decomposition
theorem is assumed, and the atom type need not be countable or infinite.

Together with the existing atom-world obstruction, this gives boxed IC at each
original type and boxed failure of operational Dedekind infinity at type t.
It does not identify operational Dedekind infinity with Frege's Infinity axiom.

Source: nominal-choice-classification-20261022.md §§3,6–7, local research,
unpaginated, misc. The single-swap proof is a new simplification developed on
23 October 2026. Ordinary classical metatheory; compiler and axiom evidence are
recorded separately.
-/

namespace Classicism.Meta.Nominal.Examples
noncomputable section

/-- Every finitely supported witness action admits intensional selectors over
the atom world action. This includes the empty and finite atom types. -/
theorem finite_atoms_ic (Atom : Type)
    (X : Nom (atoms Atom) (finiteIdeal (atoms Atom))) :
    IC (finiteAtomWorlds Atom) X := by
  classical
  apply (ic_iff_stabilizers (finiteAtomWorlds Atom) X).2
  intro F hF
  obtain ⟨S, hS, hFS⟩ := (exponential X (propositions (finiteAtomWorlds Atom))).supported F
  have hSfin : S.Finite := hS
  by_cases hfresh : ∃ a : Atom, a ∉ S
  · obtain ⟨a₀, ha₀⟩ := hfresh
    let x : Atom → X := fun w => Classical.choose (hF w)
    have hx : ∀ w : Atom, (F.val (x w)).val w :=
      fun w => Classical.choose_spec (hF w)
    let K : Atom → Set Atom := fun w => Classical.choose (X.supported (x w))
    have hKfin : ∀ w : Atom, (K w).Finite :=
      fun w => (Classical.choose_spec (X.supported (x w))).1
    have hKsupport : ∀ w : Atom, Supports (atoms Atom) X.obj (K w) (x w) :=
      fun w => (Classical.choose_spec (X.supported (x w))).2
    let U : Set Atom := ⋃ w ∈ S, K w
    have hU : U.Finite := hSfin.biUnion (fun w _ => hKfin w)
    let T : Set Atom := (S ∪ U) ∪ (K a₀ ∪ {a₀})
    have hT : T.Finite := (hSfin.union hU).union ((hKfin a₀).union (Set.finite_singleton a₀))
    refine ⟨T, hT, supports_mono (atoms Atom) _ (fun _ ha => Or.inl (Or.inl ha)) hFS, ?_⟩
    change ∀ w : Atom, ∃ z : X, (F.val z).val w ∧
      ∀ g : Equiv.Perm Atom, Fixes (atoms Atom) T g → g w = w → X.obj.act g z = z
    intro w
    by_cases hw : w ∈ S
    · refine ⟨x w, hx w, ?_⟩
      intro k hk _
      apply hKsupport w k
      intro a ha
      apply hk a
      exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, ha⟩⟩))
    · let g : Equiv.Perm Atom := Equiv.swap a₀ w
      have hgS : Fixes (atoms Atom) S g := by
        intro a ha
        exact Equiv.swap_apply_of_ne_of_ne
          (fun he => ha₀ (he ▸ ha)) (fun he => hw (he ▸ ha))
      have hgi : (finiteAtomWorlds Atom).obj.act g⁻¹ w = a₀ := by
        change (Equiv.swap a₀ w).symm w = a₀
        rw [Equiv.symm_swap, Equiv.swap_apply_right]
      have hxg : (F.val (X.obj.act g (x a₀))).val w := by
        have he := congrArg (fun p : propositions (finiteAtomWorlds Atom) => p.val w)
          (exponential_covariance X (propositions (finiteAtomWorlds Atom)) hFS g hgS (x a₀))
        change (F.val (X.obj.act g (x a₀))).val w =
          (F.val (x a₀)).val ((finiteAtomWorlds Atom).obj.act g⁻¹ w) at he
        rw [hgi] at he
        exact Eq.mpr he (hx a₀)
      refine ⟨X.obj.act g (x a₀), hxg, ?_⟩
      intro k hk hkw
      apply supports_translate (atoms Atom) X.obj (hKsupport a₀) g k
      rintro b ⟨a, ha, rfl⟩
      change k (g a) = g a
      by_cases haa₀ : a = a₀
      · subst a
        change k (Equiv.swap a₀ w a₀) = Equiv.swap a₀ w a₀
        rw [Equiv.swap_apply_left]
        exact hkw
      · by_cases haw : a = w
        · subst a
          change k (Equiv.swap a₀ w w) = Equiv.swap a₀ w w
          rw [Equiv.swap_apply_right]
          exact hk a₀ (Or.inr (Or.inr (Set.mem_singleton a₀)))
        · have hga : g a = a := Equiv.swap_apply_of_ne_of_ne haa₀ haw
          rw [hga]
          exact hk a (Or.inr (Or.inl ha))
  · refine ⟨S, hS, hFS, ?_⟩
    intro w
    obtain ⟨x, hx⟩ := hF w
    refine ⟨x, hx, ?_⟩
    intro g hg _
    have he : g = 1 := by
      apply Equiv.ext
      intro a
      exact hg a (Classical.byContradiction (fun ha => hfresh ⟨a, ha⟩))
    rw [he]
    exact X.obj.one_act x

theorem finite_atoms_intensionalChoice_quoted (Atom : Type) (σ : Ty)
    (w : finiteAtomWorlds Atom) :
    Hierarchy.Holds (finiteAtomWorlds Atom) (Hierarchy.pureConstants _) (Γ := []) () w
      (P.IntensionalChoice.quoted σ) :=
  (Hierarchy.intensionalChoice_quoted_iff (finiteAtomWorlds Atom) σ w).2
    (finite_atoms_ic Atom (Hierarchy.dom (finiteAtomWorlds Atom) σ))

theorem finite_atoms_boxed_intensionalChoice_quoted (Atom : Type) (σ : Ty)
    (w : finiteAtomWorlds Atom) :
    Hierarchy.Holds (finiteAtomWorlds Atom) (Hierarchy.pureConstants _) (Γ := []) () w
      (P.NecIntensionalChoice.quoted σ) := by
  change Hierarchy.Holds (finiteAtomWorlds Atom) (Hierarchy.pureConstants _) (Γ := []) () w
    (Term.box (P.IntensionalChoice.quoted σ))
  exact (Hierarchy.holds_box _ _ (Γ := []) _ () w).2
    (finite_atoms_intensionalChoice_quoted Atom σ)

/-- The two original-language verdicts hold together at every atom world. -/
theorem finite_atoms_boxed_ic_and_not_dedInfT (Atom : Type) (σ : Ty)
    (w : finiteAtomWorlds Atom) :
    Hierarchy.Holds (finiteAtomWorlds Atom) (Hierarchy.pureConstants _) (Γ := []) () w
        (P.NecIntensionalChoice.quoted σ) ∧
      Hierarchy.Holds (finiteAtomWorlds Atom) (Hierarchy.pureConstants _) (Γ := []) () w
        (Term.box (Term.neg Hierarchy.dedInfT)) :=
  ⟨finite_atoms_boxed_intensionalChoice_quoted Atom σ w,
    finite_atoms_boxed_not_dedInfT Atom w⟩

end
end Classicism.Meta.Nominal.Examples
