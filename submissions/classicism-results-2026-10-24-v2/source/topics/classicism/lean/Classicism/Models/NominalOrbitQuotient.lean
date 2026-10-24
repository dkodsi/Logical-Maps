import Classicism.Models.NominalOrbitShift
import Mathlib.Data.Quot
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Range

/-!
# The orbit quotient and operational Dedekind infinity

This module removes the supplied-sequence premise from the positive half of
the nominal Dedekind classification. An infinite quotient of worlds by the
global group action supplies a sequence of pairwise distinct orbits. The
already constructed supported shift then acts on the whole proposition domain.
The finite case supplies a finite set of representatives, ready for a separate
support-fixer orbit theorem.

The construction is generic in the group and support ideal. It uses ordinary
classical metatheory and does not assert that finite global orbit count alone
implies finite support-fixer orbit count for arbitrary group actions.
`Hierarchy.dedInfT` remains operational Dedekind infinity, not the quantified
Frege Infinity axiom.

Source: research/2026-10-22/notes/nominal-choice-classification-20261022.md
§§2,6, original local research, unpaginated, direct source misc. These new
proof bodies require a successful compiler and axiom audit.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

theorem orbit_refl (W : Nom A I) (u : W) : Orbit W u u :=
  ⟨1, W.obj.one_act u⟩

theorem orbit_symm (W : Nom A I) {u v : W} (h : Orbit W u v) : Orbit W v u := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg, inv_act]⟩

theorem orbit_trans (W : Nom A I) {u v w : W}
    (huv : Orbit W u v) (hvw : Orbit W v w) : Orbit W u w := by
  obtain ⟨g, hg⟩ := huv
  obtain ⟨h, hh⟩ := hvw
  exact ⟨h * g, by rw [W.obj.mul_act, hg, hh]⟩

def orbitSetoid (W : Nom A I) : Setoid W where
  r := Orbit W
  iseqv := ⟨orbit_refl W, orbit_symm W, orbit_trans W⟩

/-- The external set of global world orbits. -/
abbrev OrbitQuotient (W : Nom A I) := Quotient (orbitSetoid W)

def orbitClass (W : Nom A I) (w : W) : OrbitQuotient W :=
  Quotient.mk (orbitSetoid W) w

theorem orbitClass_eq_iff (W : Nom A I) (u v : W) :
    orbitClass W u = orbitClass W v ↔ Orbit W u v :=
  Quotient.eq

/-- A finite global orbit quotient has finitely many representative worlds.
This includes the empty world action; no distinguished world is needed. -/
theorem finite_orbit_representatives (W : Nom A I) [Finite (OrbitQuotient W)] :
    ∃ R : Set W, R.Finite ∧ ∀ w : W, ∃ r ∈ R, Orbit W r w := by
  let rep : OrbitQuotient W → W := Quotient.out
  refine ⟨Set.range rep, Set.finite_range rep, ?_⟩
  intro w
  refine ⟨rep (orbitClass W w), ⟨orbitClass W w, rfl⟩, ?_⟩
  exact Quotient.exact (Quotient.out_eq (orbitClass W w))

/-- Choose representatives of countably many distinct global orbits. -/
def orbitSequence (W : Nom A I) [Infinite (OrbitQuotient W)] : Nat → W :=
  fun n => (Infinite.natEmbedding (OrbitQuotient W) n).out

theorem orbitSequence_separated (W : Nom A I) [Infinite (OrbitQuotient W)]
    (n m : Nat) (h : Orbit W (orbitSequence W n) (orbitSequence W m)) : n = m := by
  apply (Infinite.natEmbedding (OrbitQuotient W)).injective
  have he : Quotient.mk (orbitSetoid W) (orbitSequence W n) =
      Quotient.mk (orbitSetoid W) (orbitSequence W m) := Quotient.sound h
  change Quotient.mk (orbitSetoid W)
      ((Infinite.natEmbedding (OrbitQuotient W) n).out) =
    Quotient.mk (orbitSetoid W)
      ((Infinite.natEmbedding (OrbitQuotient W) m).out) at he
  simpa only [Quotient.out_eq] using he

theorem infinite_orbit_quotient_dedekind (W : Nom A I) [Infinite (OrbitQuotient W)] :
    ∃ f : exponential (propositions W) (propositions W),
      Function.Injective f.val ∧ ∃ r : propositions W, ∀ p, f.val p ≠ r :=
  orbit_sequence_dedekind W (orbitSequence W) (orbitSequence_separated W)

namespace Hierarchy

theorem infinite_orbit_quotient_dedInfT (W : Nom A I)
    [Infinite (OrbitQuotient W)] (w : W) :
    Holds W (pureConstants W) (Γ := []) () w dedInfT :=
  orbit_sequence_dedInfT W (orbitSequence W) (orbitSequence_separated W) w

theorem infinite_orbit_quotient_boxed_dedInfT (W : Nom A I)
    [Infinite (OrbitQuotient W)] (w : W) :
    Holds W (pureConstants W) (Γ := []) () w (Term.box dedInfT) :=
  orbit_sequence_boxed_dedInfT W (orbitSequence W) (orbitSequence_separated W) w

end Hierarchy
end
end Classicism.Meta.Nominal
