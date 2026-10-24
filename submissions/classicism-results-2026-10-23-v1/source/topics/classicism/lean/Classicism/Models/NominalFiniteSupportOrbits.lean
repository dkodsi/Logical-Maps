import Classicism.Models.NominalFiniteOrbitStrata
import Mathlib.Data.Set.Finite.Lattice

/-!
# Orbit-finite nominal worlds have finite support-fixer orbits

The atom group is the full permutation group, the ideal is finite support,
and the hypothesis supplies finitely many representatives of GLOBAL orbits.
For every finite atom set, finitely many orbits remain under its pointwise
fixer. This discharges the finite-strata hypothesis without assuming least
supports or a classification of transitive nominal sets. The atom type may
be finite, infinite, or empty.

Proof: on a finite support K of one global representative, a transported
support has only finitely many equality patterns with the fixed finite set S.
Equal patterns extend to a permutation fixing S. The extension is proved by
finite-set induction using swaps, so no infinite-atom assumption is hidden.

Source: research/2026-10-22/notes/nominal-choice-classification-20261022.md
sections 2 and 6; original local research, unpaginated, direct source misc.
The explicit arbitrary-atom finite-pattern proof is new formalization work.
Ordinary classical metatheory; successful compilation and axiom auditing are
separate from the presence of these proof bodies.
-/

namespace Classicism.Meta.Nominal
noncomputable section

namespace FiniteSupportOrbits

/-- Extend finite injective data while fixing S pointwise. Agreement about
which coordinates equal each member of S is the exact compatibility needed.
The fixed set S need not itself be finite in this extension lemma. -/
theorem extend_finite_pattern {D Atom : Type} (S : Set Atom)
    (f g : D → Atom) (hf : Function.Injective f) (hg : Function.Injective g)
    (hpattern : ∀ a s, s ∈ S → (f a = s ↔ g a = s))
    (K : Set D) (hK : K.Finite) :
    ∃ π : Equiv.Perm Atom, (∀ s ∈ S, π s = s) ∧ ∀ a ∈ K, π (f a) = g a := by
  classical
  induction K, hK using Set.Finite.induction_on with
  | empty =>
      exact ⟨1, fun _ _ => rfl, fun _ h => h.elim⟩
  | @insert a K ha hK ih =>
      obtain ⟨π, hπS, hπK⟩ := ih
      let x := π (f a)
      let y := g a
      have hxy : ∀ s ∈ S, (x = s ↔ y = s) := by
        intro s hs
        have hx : x = s ↔ f a = s := by
          change π (f a) = s ↔ f a = s
          constructor
          · intro he
            exact π.injective (he.trans (hπS s hs).symm)
          · intro he
            rw [he, hπS s hs]
        exact hx.trans (hpattern a s hs)
      have hswapS : ∀ s ∈ S, Equiv.swap x y s = s := by
        intro s hs
        by_cases h : x = y
        · simp only [h, Equiv.swap_self, Equiv.refl_apply]
        · apply Equiv.swap_apply_of_ne_of_ne
          · intro hsx
            exact h (hsx.symm.trans (((hxy s hs).1 hsx.symm).symm))
          · intro hsy
            exact h (((hxy s hs).2 hsy.symm).trans hsy)
      refine ⟨Equiv.swap x y * π, ?_, ?_⟩
      · intro s hs
        change Equiv.swap x y (π s) = s
        rw [hπS s hs, hswapS s hs]
      · intro b hb
        change Equiv.swap x y (π (f b)) = g b
        rcases hb with rfl | hb
        · exact Equiv.swap_apply_left x y
        · rw [hπK b hb]
          apply Equiv.swap_apply_of_ne_of_ne
          · intro he
            have hba : b = a := hf (π.injective ((hπK b hb).trans he))
            exact ha (hba ▸ hb)
          · intro he
            have hba : b = a := hg he
            exact ha (hba ▸ hb)

/-- Specialize the extension lemma to two permutations whose restrictions to
a finite support have the same equality pattern with S. -/
theorem align_permutations {Atom : Type} (S K : Set Atom) (hK : K.Finite)
    (g h : Equiv.Perm Atom)
    (hpattern : ∀ a ∈ K, ∀ s ∈ S, (g a = s ↔ h a = s)) :
    ∃ π : Equiv.Perm Atom, Fixes (Examples.atoms Atom) S π ∧
      ∀ a ∈ K, π (g a) = h a := by
  classical
  letI : Finite K := hK
  obtain ⟨π, hπS, hπK⟩ := extend_finite_pattern S
    (fun a : K => g a.val) (fun a : K => h a.val)
    (g.injective.comp Subtype.val_injective) (h.injective.comp Subtype.val_injective)
    (fun a s hs => hpattern a.val a.property s hs) Set.univ (Set.toFinite _)
  exact ⟨π, hπS, fun a ha => hπK ⟨a, ha⟩ (Set.mem_univ _)⟩

/-- Equal finite support patterns put the corresponding worlds in the same
S-fixer orbit. No least-support property is used. -/
theorem supportOrbit_of_pattern {Atom : Type}
    (W : Nom (Examples.atoms Atom) (finiteIdeal (Examples.atoms Atom)))
    (r : W) (S K : Set Atom) (hK : K.Finite)
    (hr : Supports (Examples.atoms Atom) W.obj K r)
    (g h : Equiv.Perm Atom)
    (hpattern : ∀ a ∈ K, ∀ s ∈ S, (g a = s ↔ h a = s)) :
    SupportOrbit W S (W.obj.act g r) (W.obj.act h r) := by
  obtain ⟨π, hπS, hπK⟩ := align_permutations S K hK g h hpattern
  have hk : Fixes (Examples.atoms Atom) K (h⁻¹ * (π * g)) := by
    change ∀ a : Atom, a ∈ K → h.symm (π (g a)) = a
    intro a ha
    exact (congrArg h.symm (hπK a ha)).trans (h.symm_apply_apply a)
  have he := congrArg (W.obj.act h) (hr (h⁻¹ * (π * g)) hk)
  have ht : W.obj.act (π * g) r = W.obj.act h r := by
    simpa only [W.obj.mul_act, act_inv] using he
  exact ⟨π, hπS, by rw [← W.obj.mul_act, ht]⟩

/-- One global orbit splits into finitely many S-fixer orbits. -/
theorem finite_representatives_in_orbit {Atom : Type}
    (W : Nom (Examples.atoms Atom) (finiteIdeal (Examples.atoms Atom)))
    (r : W) (S : Set Atom) (hS : S.Finite) :
    ∃ T : Set W, T.Finite ∧
      ∀ w : W, Orbit W r w → ∃ t ∈ T, SupportOrbit W S t w := by
  classical
  obtain ⟨K, hK, hr⟩ := W.supported r
  letI : Finite K := hK
  letI : Finite S := hS
  let Pattern := K → S → Prop
  let code : Equiv.Perm Atom → Pattern := fun g a s => g a.val = s.val
  let Q : Set Pattern := Set.range code
  letI : Finite Q := Set.toFinite Q
  let rep : Q → Equiv.Perm Atom := fun p => Classical.choose p.property
  have hrep : ∀ p : Q, code (rep p) = p.val :=
    fun p => Classical.choose_spec p.property
  refine ⟨Set.range (fun p : Q => W.obj.act (rep p) r), Set.finite_range _, ?_⟩
  intro w hw
  obtain ⟨g, rfl⟩ := hw
  let p : Q := ⟨code g, ⟨g, rfl⟩⟩
  refine ⟨W.obj.act (rep p) r, ⟨p, rfl⟩, ?_⟩
  apply supportOrbit_of_pattern W r S K hK hr (rep p) g
  intro a ha s hs
  have he := congrFun (congrFun (hrep p) ⟨a, ha⟩) ⟨s, hs⟩
  exact Iff.of_eq he

end FiniteSupportOrbits

/-- The orbit-finite implication needed by the nominal Dedekind-infinity
classification. Its only orbit hypothesis concerns GLOBAL orbit representatives. -/
theorem finite_stabilizer_orbits_of_global_representatives {Atom : Type}
    (W : Nom (Examples.atoms Atom) (finiteIdeal (Examples.atoms Atom)))
    (R : Set W) (hR : R.Finite)
    (hcover : ∀ w : W, ∃ r ∈ R, Orbit W r w)
    (S : Set Atom) (hS : S.Finite) :
    ∃ T : Set W, T.Finite ∧ ∀ w : W, ∃ t ∈ T, SupportOrbit W S t w := by
  classical
  let T : W → Set W := fun r =>
    Classical.choose (FiniteSupportOrbits.finite_representatives_in_orbit W r S hS)
  have hT : ∀ r, (T r).Finite ∧
      ∀ w : W, Orbit W r w → ∃ t ∈ T r, SupportOrbit W S t w :=
    fun r => Classical.choose_spec
      (FiniteSupportOrbits.finite_representatives_in_orbit W r S hS)
  refine ⟨⋃ r ∈ R, T r, hR.biUnion (fun r _ => (hT r).1), ?_⟩
  intro w
  obtain ⟨r, hr, hwr⟩ := hcover w
  obtain ⟨t, ht, htw⟩ := (hT r).2 w hwr
  exact ⟨t, Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hr, ht⟩⟩, htw⟩

/-- Finitely many global world orbits imply finite proposition strata. -/
theorem finite_proposition_strata_of_global_representatives {Atom : Type}
    (W : Nom (Examples.atoms Atom) (finiteIdeal (Examples.atoms Atom)))
    (R : Set W) (hR : R.Finite)
    (hcover : ∀ w : W, ∃ r ∈ R, Orbit W r w)
    (S : Set Atom) (hS : S.Finite) :
    Finite {p : propositions W // Supports (Examples.atoms Atom) (propositions W).obj S p} := by
  obtain ⟨T, hT, hc⟩ :=
    finite_stabilizer_orbits_of_global_representatives W R hR hcover S hS
  exact finite_proposition_stratum_of_representatives W S T hT hc

/-- The existing operational sentence now has a genuine orbit-finite
obstruction for arbitrary finite-supported world actions of Sym(Atom). -/
theorem Hierarchy.not_dedInfT_of_global_representatives {Atom : Type}
    (W : Nom (Examples.atoms Atom) (finiteIdeal (Examples.atoms Atom)))
    (R : Set W) (hR : R.Finite)
    (hcover : ∀ w : W, ∃ r ∈ R, Orbit W r w) (w : W) :
    ¬Hierarchy.Holds W (Hierarchy.pureConstants W) (Γ := []) () w Hierarchy.dedInfT :=
  Hierarchy.not_dedInfT_of_finite_strata W
    (finite_proposition_strata_of_global_representatives W R hR hcover) w

end
end Classicism.Meta.Nominal
