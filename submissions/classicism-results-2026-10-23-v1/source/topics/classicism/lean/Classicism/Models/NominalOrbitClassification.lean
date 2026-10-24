import Classicism.Models.NominalOrbitQuotient
import Classicism.Models.NominalFiniteSupportOrbits

/-!
# Exact operational Dedekind classification by global world orbits

For the full permutation group of an arbitrary atom type and the finite-support
ideal, the proposition domain has an admitted injective nonsurjective operation
exactly when the global world-orbit quotient is infinite. The finite direction
uses the proved finite-pattern refinement, not an assumed local orbit premise.
The actual and boxed original operational sentences are connected below.

Source: research/2026-10-22/notes/nominal-choice-classification-20261022.md §6;
the arbitrary-atom simplification is proved in
research/2026-10-23/nominal-classification-followup.md §§2–3.
Original local research, unpaginated, direct source misc. Classical semantic
metatheory; this does not identify operational infinity with Frege Infinity.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {Atom : Type}
variable (W : Nom (Examples.atoms Atom) (finiteIdeal (Examples.atoms Atom)))

theorem finite_stabilizer_orbits_of_finite_orbit_quotient
    [Finite (OrbitQuotient W)] (S : Set Atom) (hS : S.Finite) :
    ∃ R : Set W, R.Finite ∧ ∀ w : W, ∃ r ∈ R, SupportOrbit W S r w := by
  obtain ⟨R, hR, hc⟩ := finite_orbit_representatives W
  exact finite_stabilizer_orbits_of_global_representatives W R hR hc S hS

theorem finite_proposition_strata_of_finite_orbit_quotient
    [Finite (OrbitQuotient W)] (S : Set Atom) (hS : S.Finite) :
    Finite {p : propositions W //
      Supports (Examples.atoms Atom) (propositions W).obj S p} := by
  obtain ⟨R, hR, hc⟩ := finite_stabilizer_orbits_of_finite_orbit_quotient W S hS
  exact finite_proposition_stratum_of_representatives W S R hR hc

theorem no_dedekind_of_finite_orbit_quotient [Finite (OrbitQuotient W)] :
    ¬∃ f : exponential (propositions W) (propositions W),
      Function.Injective f.val ∧ ∃ r : propositions W, ∀ p, f.val p ≠ r :=
  no_dedekind_of_finite_strata (propositions W)
    (finite_proposition_strata_of_finite_orbit_quotient W)

theorem dedekind_iff_infinite_orbit_quotient :
    (∃ f : exponential (propositions W) (propositions W),
      Function.Injective f.val ∧ ∃ r : propositions W, ∀ p, f.val p ≠ r) ↔
      Infinite (OrbitQuotient W) := by
  classical
  constructor
  · intro h
    by_contra hn
    letI : Finite (OrbitQuotient W) := Finite.of_not_infinite hn
    exact no_dedekind_of_finite_orbit_quotient W h
  · intro h
    letI : Infinite (OrbitQuotient W) := h
    exact infinite_orbit_quotient_dedekind W

namespace Hierarchy

theorem dedInfT_iff_infinite_orbit_quotient (w : W) :
    Holds W (pureConstants W) (Γ := []) () w dedInfT ↔
      Infinite (OrbitQuotient W) :=
  (dedInfT_iff W w).trans (dedekind_iff_infinite_orbit_quotient W)

theorem not_dedInfT_iff_finite_orbit_quotient (w : W) :
    ¬Holds W (pureConstants W) (Γ := []) () w dedInfT ↔
      Finite (OrbitQuotient W) :=
  (dedInfT_iff_infinite_orbit_quotient W w).not.trans not_infinite_iff_finite

theorem boxed_dedInfT_iff_infinite_orbit_quotient (w : W) :
    Holds W (pureConstants W) (Γ := []) () w (Term.box dedInfT) ↔
      Infinite (OrbitQuotient W) := by
  constructor
  · intro h
    exact (dedInfT_iff_infinite_orbit_quotient W w).1
      ((holds_box W (pureConstants W) (Γ := []) dedInfT () w).1 h w)
  · intro h
    letI : Infinite (OrbitQuotient W) := h
    exact infinite_orbit_quotient_boxed_dedInfT W w

theorem boxed_not_dedInfT_iff_finite_orbit_quotient (w : W) :
    Holds W (pureConstants W) (Γ := []) () w (Term.box (Term.neg dedInfT)) ↔
      Finite (OrbitQuotient W) := by
  constructor
  · intro h
    have hn := (holds_box W (pureConstants W) (Γ := []) (Term.neg dedInfT) () w).1 h w
    exact (not_dedInfT_iff_finite_orbit_quotient W w).1
      ((holds_not W (pureConstants W) (Γ := []) () w dedInfT).1 hn)
  · intro h
    apply (holds_box W (pureConstants W) (Γ := []) (Term.neg dedInfT) () w).2
    intro v
    exact (holds_not W (pureConstants W) (Γ := []) () v dedInfT).2
      ((not_dedInfT_iff_finite_orbit_quotient W v).2 h)

end Hierarchy
end
end Classicism.Meta.Nominal
