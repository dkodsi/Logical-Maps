import Classicism.Results.Research.FiniteProfiles
import Classicism.Results.Research.WorldRepresentation

/-!
# Finite atoms, finite propositions, and raw world-profile Infinity

Direct source: research/2026-10-22/notes/world-cardinality-ucp-20261022.md,
§20.C–D (unpaginated original research, misc). Atomicity is an explicit current
premise. No completeness, BF, C5 or Choice premise is added.
-/

namespace Classicism.Research.FiniteAtomProfiles
open Classicism.Paper Classicism.P
open Classicism.Research.FregeFiniteSets
open Classicism.Research.FiniteProfiles
open Classicism.Research.WorldRepresentation

theorem atoms_separate_propositions (hat : AtomicityT) (p q : Prop)
    (h : ∀ w, Atom w → (w ≤ p ↔ w ≤ q)) : p = q := by
  apply modalized_fregean p q
  apply (atomic_coverage hat (p ↔ q)).1
  intro w hw
  apply (em (w ≤ p)).elim
  · intro hp
    have hpq : w ≤ (p ∧ q) := le_and_prop w p q hp ((h w hw).1 hp)
    exact le_trans_prop _ _ _ hpq (le_of_box_incl
      (nec% (fun (hpq : p ∧ q) => (show p ↔ q from ⟨fun _ => hpq.2, fun _ => hpq.1⟩))))
  · intro hp
    have hnq : ¬ w ≤ q := fun hq => hp ((h w hw).2 hq)
    have hn : w ≤ (¬ p ∧ ¬ q) :=
      le_and_prop w (¬ p) (¬ q) ((at_neg w p hw).2 hp) ((at_neg w q hw).2 hnq)
    exact le_trans_prop _ _ _ hn (le_of_box_incl
      (nec% (fun (hneg : ¬ p ∧ ¬ q) => (show p ↔ q from
        ⟨fun hp => (hneg.1 hp).elim, fun hq => (hneg.2 hq).elim⟩))))

theorem finite_propositions_of_finite_atoms (hat : AtomicityT)
    (hfin : Finite (Atom (τ := Prop))) : Finite (fun _ : Prop => True) :=
  finite_separated_family Atom (fun _ => True) (fun w p => w ≤ p) hfin
    (fun p q _ _ h => atoms_separate_propositions hat p q h)

theorem finite_atoms_of_finite_propositions (hfin : Finite (fun _ : Prop => True)) :
    Finite (Atom (τ := Prop)) :=
  finite_subset (fun _ => True) Atom hfin (fun _ _ => True.intro)

theorem finite_atoms_iff_propositions (hat : AtomicityT) :
    Finite (Atom (τ := Prop)) ↔ Finite (fun _ : Prop => True) :=
  ⟨finite_propositions_of_finite_atoms hat, finite_atoms_of_finite_propositions⟩

theorem raw_uwr_finite_base_iff_propositions {σ : Type} [Ty σ]
    (V : σ → Prop) (hV : RawUWR V) (hat : AtomicityT) :
    Finite (fun _ : σ => True) ↔ Finite (fun _ : Prop => True) :=
  (raw_uwr_finite_atoms_iff V hV).symm.trans (finite_atoms_iff_propositions hat)

theorem raw_uwr_infinity_base_iff_propositions {σ : Type} [Ty σ]
    (V : σ → Prop) (hV : RawUWR V) (hat : AtomicityT) :
    AxiomOfInfinity σ ↔ AxiomOfInfinity Prop :=
  ⟨fun hi ht => hi ((raw_uwr_finite_base_iff_propositions V hV hat).2 ht),
    fun ht hi => ht ((raw_uwr_finite_base_iff_propositions V hV hat).1 hi)⟩

end Classicism.Research.FiniteAtomProfiles
