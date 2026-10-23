import Classicism.Results.Research.RigidityClosureResearchUniform
import Classicism.Results.Research.RigidityClosureResearchJoins
import Classicism.Results.Research.ChoiceCompleteness
import Classicism.Results.Research.ActualityCore

/-!
# Boolean normalizers, represented joins, and the actual-world interval

Direct source: notes/rigidity-by-joins-and-boolean-closure.md §§4–6 and
notes/maximalism-modal.md §§22–23 (original research, misc, unpaginated,
22 October 2026). All equations quantify over current arguments. Completeness
is only over admitted families. Neither external subsets nor boxed universal
normalizer laws are assumed. The normalizer's range unit may be below top.
-/
namespace Classicism.Research.RigidityClosure
open Classicism.P Classicism.Paper
variable {σ : Type} [Ty σ]

def NormalizerImage (R : (σ → Prop) → (σ → Prop)) (H : (σ → Prop) → Prop) :
    (σ → Prop) → Prop := fun Y => ∃ X, H X ∧ Y = R X

def CurrentUnion (H : (σ → Prop) → Prop) : σ → Prop := fun a => ∃ X, H X ∧ X a

def WorldCut (w : Prop) (Y : σ → Prop) : σ → Prop := fun a => w ∧ Y a

theorem normalizer_coext_eq (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (X Y : σ → Prop) (hc : X ≡ Y) : R X = R Y :=
  Proofs.eq_of_weaklyRigid_coext (hr X).1 (hr Y).1 (fun a =>
    ⟨fun h => ((hr Y).2 a).mp ((hc a).mp (((hr X).2 a).mpr h)),
     fun h => ((hr X).2 a).mp ((hc a).mpr (((hr Y).2 a).mpr h))⟩)

theorem normalizer_fixes (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (Y : σ → Prop) (hy : WeaklyRigid Y) : R Y = Y :=
  Proofs.eq_of_weaklyRigid_coext (hr Y).1 hy (fun a => ((hr Y).2 a).symm)

theorem normalizer_idempotent (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (X : σ → Prop) : R (R X) = R X := normalizer_fixes R hr (R X) (hr X).1

theorem normalizer_le_of_current_inclusion (R : (σ → Prop) → (σ → Prop))
    (hr : WeakNormalizer R) (X Y : σ → Prop) (hi : X ⊆ Y) : R X ≤ R Y :=
  le_of_box_incl ((hr X).1.2 (R Y) fun a ha =>
    (hr Y).1.1 a (((hr Y).2 a).mp (hi a (((hr X).2 a).mpr ha))))

theorem normalizer_monotone (R : (σ → Prop) → (σ → Prop))
    (hr : WeakNormalizer R) (X Y : σ → Prop) (hi : X ≤ Y) : R X ≤ R Y :=
  normalizer_le_of_current_inclusion R hr X Y (incl_of_le hi)

theorem normalizer_range_unit (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (Y : σ → Prop) (hy : WeaklyRigid Y) : Y ≤ R (fun _ => True) :=
  le_of_box_incl (hy.2 (R (fun _ => True)) fun a _ =>
    (hr (fun _ => True)).1.1 a (((hr (fun _ => True)).2 a).mp trivial))

theorem normalizer_union (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (X Y : σ → Prop) : R (fun a => X a ∨ Y a) = (fun a => R X a ∨ R Y a) :=
  Proofs.eq_of_weaklyRigid_coext (hr (fun a => X a ∨ Y a)).1
    (weak_union (R X) (R Y) (hr X).1 (hr Y).1) (fun a =>
      ⟨fun h => (((hr (fun a => X a ∨ Y a)).2 a).mpr h).elim
        (fun hx => Or.inl (((hr X).2 a).mp hx)) (fun hy => Or.inr (((hr Y).2 a).mp hy)),
       fun h => ((hr (fun a => X a ∨ Y a)).2 a).mp (h.elim
        (fun hx => Or.inl (((hr X).2 a).mpr hx)) (fun hy => Or.inr (((hr Y).2 a).mpr hy)))⟩)

theorem normalizer_intersection (nd : NecessityOfDistinctness σ)
    (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R) (X Y : σ → Prop) :
    R (fun a => X a ∧ Y a) = (fun a => R X a ∧ R Y a) :=
  Proofs.eq_of_weaklyRigid_coext (hr (fun a => X a ∧ Y a)).1
    (nd_weak_meet nd (R X) (R Y) (hr X).1 (hr Y).1) (fun a =>
      ⟨fun h => ⟨((hr X).2 a).mp (((hr (fun a => X a ∧ Y a)).2 a).mpr h).1,
        ((hr Y).2 a).mp (((hr (fun a => X a ∧ Y a)).2 a).mpr h).2⟩,
       fun h => ((hr (fun a => X a ∧ Y a)).2 a).mp
        ⟨((hr X).2 a).mpr h.1, ((hr Y).2 a).mpr h.2⟩⟩)

theorem normalizer_complement (nd : NecessityOfDistinctness σ)
    (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R) (X : σ → Prop) :
    R (fun a => ¬ X a) = (fun a => R (fun _ => True) a ∧ ¬ R X a) :=
  Proofs.eq_of_weaklyRigid_coext (hr (fun a => ¬ X a)).1
    (nd_weak_difference nd (R (fun _ => True)) (R X) (hr (fun _ => True)).1 (hr X).1)
    (fun a => ⟨fun h =>
      ⟨((hr (fun _ => True)).2 a).mp trivial,
       fun hx => ((hr (fun a => ¬ X a)).2 a).mpr h (((hr X).2 a).mpr hx)⟩,
      fun h => ((hr (fun a => ¬ X a)).2 a).mp
        (fun hx => h.2 (((hr X).2 a).mp hx))⟩)

theorem normalizer_bottom (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R) :
    R (fun _ => False) = (fun _ => False) := normalizer_fixes R hr _ weak_bottom

/-- Under Actuality a represented Boolean join is a current pointwise union. -/
theorem actual_world_join_pointwise (w : Prop) (hw : ActualWorld w)
    (H : (σ → Prop) → Prop) (J : σ → Prop) (hj : LUB J H) (a : σ) :
    J a ↔ CurrentUnion H a := by
  refine ⟨?_, ?_⟩
  · intro hja
    exact (em (CurrentUnion H a)).elim id fun hn =>
      have hb : J a ≤ ¬ w :=
        (Classicism.Research.Choice.evaluation_lub H J hj a (¬ w)).1 fun X hx =>
          le_of_box_incl (modal_K _ _
            (nec% (fun (h : w → ¬ X a) (ha : X a) (hw : w) => h hw ha))
            ((le_iff_prop _ _).1 (hw.2 (¬ X a) (fun ha => hn ⟨X, hx, ha⟩))))
      False.elim (imp_of_le_prop _ _ hb hja hw.1)
  · intro ha
    exact ha.elim fun X hx => incl_of_le (((hj J).2 (le_refl_rel J)) X hx.1) a hx.2

/-- The representative of a current union is the join of the representatives. -/
theorem normalizer_current_union_lub (R : (σ → Prop) → (σ → Prop))
    (hr : WeakNormalizer R) (H : (σ → Prop) → Prop) :
    LUB (R (CurrentUnion H)) (NormalizerImage R H) := by
  intro Z
  refine ⟨?_, ?_⟩
  · intro hz
    apply le_of_box_incl
    exact (hr (CurrentUnion H)).1.2 Z fun a ha =>
      (((hr (CurrentUnion H)).2 a).mpr ha).elim fun X hx =>
        modal_K _ _
          (converse_barcan _ ((le_iff _ _).1 (hz (R X) ⟨X, hx.1, rfl⟩)) a)
          ((hr X).1.1 a (((hr X).2 a).mp hx.2))
  · intro hz Y hy
    obtain ⟨X, hx, he⟩ := hy
    rw [he]
    exact le_trans_rel _ _ _
      (normalizer_le_of_current_inclusion R hr X (CurrentUnion H) fun a ha => ⟨X, hx, ha⟩) hz

/-- Preservation of every already represented join; no extra existence premise. -/
theorem normalizer_preserves_join (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (act : Actuality) (H : (σ → Prop) → Prop) (J : σ → Prop) (hj : LUB J H) :
    LUB (R J) (NormalizerImage R H) :=
  act.elim fun w hw => (normalizer_coext_eq R hr J (CurrentUnion H)
    (fun a => actual_world_join_pointwise w hw H J hj a)).symm ▸
      normalizer_current_union_lub R hr H

/-- The kernel consists exactly of current empty relations. -/
theorem normalizer_kernel (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (X : σ → Prop) : R X = (fun _ => False) ↔ ∀ a, ¬ X a :=
  ⟨fun he a hx => Eq.mp (congrFun he a) (((hr X).2 a).mp hx),
   fun hn => Proofs.eq_of_weaklyRigid_coext (hr X).1 weak_bottom
      (fun a => ⟨fun h => hn a (((hr X).2 a).mpr h), fun h => False.elim h⟩)⟩

theorem kernel_world_interval (w : Prop) (hw : ActualWorld w) (X : σ → Prop) :
    (∀ a, ¬ X a) ↔ X ≤ (fun _ => ¬ w) :=
  ⟨fun hn => le_of_box_incl (modal_K _ _
    (nec% (fun (h : w → ∀ a : σ, ¬ X a) (a : σ) (hx : X a) (hw : w) => h hw a hx))
    ((le_iff_prop _ _).1 (hw.2 (∀ a, ¬ X a) hn))),
   fun hi a hx => incl_of_le hi a hx hw.1⟩

/-- Localization of weakly rigid fragments is an order embedding into [0,c(w)]. -/
theorem world_cut_order_iff (w : Prop) (hw : ActualWorld w)
    (Y Z : σ → Prop) (hy : WeaklyRigid Y) (hz : WeaklyRigid Z) :
    WorldCut w Y ≤ WorldCut w Z ↔ Y ≤ Z :=
  ⟨fun hi => le_of_box_incl (hy.2 Z fun a ha => hz.1 a
    (incl_of_le hi a ⟨hw.1, ha⟩).2),
   fun hi => le_of_box_incl (modal_K _ _
    (nec% (fun (h : ∀ a : σ, Y a → Z a) (a : σ) (ha : w ∧ Y a) => ⟨ha.1, h a ha.2⟩))
    ((le_iff _ _).1 hi))⟩

theorem world_cut_injective (w : Prop) (hw : ActualWorld w)
    (Y Z : σ → Prop) (hy : WeaklyRigid Y) (hz : WeaklyRigid Z)
    (he : WorldCut w Y = WorldCut w Z) : Y = Z :=
  Proofs.eq_of_weaklyRigid_coext hy hz (fun a =>
    ⟨fun ha => (Eq.mp (congrFun he a) ⟨hw.1, ha⟩).2,
     fun ha => (Eq.mpr (congrFun he a) ⟨hw.1, ha⟩).2⟩)

theorem world_cut_supported (w : Prop) (Y : σ → Prop) :
    WorldCut w Y ≤ (fun _ => w) :=
  le_of_box_incl (nec% (fun (a : σ) (h : w ∧ Y a) => h.1))

/-- Surjectivity onto the whole supported interval uses only current WRC. -/
theorem world_cut_surjective (w : Prop) (hw : ActualWorld w)
    (rc : WeakRigidComprehension (σ → Prop)) (X : σ → Prop) (hs : X ≤ (fun _ => w)) :
    ∃ Y : σ → Prop, WeaklyRigid Y ∧ WorldCut w Y = X :=
  (rc X).elim fun Y hy => ⟨Y, hy.1,
    Classicism.Research.ActualityCore.localized_eq w hw _ _
      (world_cut_supported w Y) hs
      (fun a => ⟨fun ha => (hy.2 a).mpr ha.2, fun ha => ⟨hw.1, (hy.2 a).mp ha⟩⟩)⟩

theorem rigid_world_cut_surjective (w : Prop) (hw : ActualWorld w)
    (rc : RigidComprehension (σ → Prop)) (X : σ → Prop) (hs : X ≤ (fun _ => w)) :
    ∃ Y : σ → Prop, Rigid Y ∧ WorldCut w Y = X :=
  (rc X).elim fun Y hy => ⟨Y, hy.1,
    Classicism.Research.ActualityCore.localized_eq w hw _ _
      (world_cut_supported w Y) hs
      (fun a => ⟨fun ha => (hy.2 a).mpr ha.2, fun ha => ⟨hw.1, (hy.2 a).mp ha⟩⟩)⟩

/-- The inverse is precisely the normalizer restricted to the supported interval. -/
theorem normalizer_inverse_world_cut (w : Prop) (hw : ActualWorld w)
    (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (X : σ → Prop) (hs : X ≤ (fun _ => w)) : WorldCut w (R X) = X :=
  Classicism.Research.ActualityCore.localized_eq w hw _ _ (world_cut_supported w (R X)) hs
    (fun a => ⟨fun ha => ((hr X).2 a).mpr ha.2,
      fun ha => ⟨hw.1, ((hr X).2 a).mp ha⟩⟩)

theorem normalizer_of_world_cut (w : Prop) (hw : ActualWorld w)
    (R : (σ → Prop) → (σ → Prop)) (hr : WeakNormalizer R)
    (Y : σ → Prop) (hy : WeaklyRigid Y) : R (WorldCut w Y) = Y :=
  (normalizer_coext_eq R hr (WorldCut w Y) Y
    (fun a => ⟨And.right, fun ha => ⟨hw.1, ha⟩⟩)).trans (normalizer_fixes R hr Y hy)

/-- Every admitted family of weakly rigid relations has its ambient join in the fragment. -/
theorem weak_fragment_complete (bc : BooleanCompleteness (σ → Prop))
    (H : (σ → Prop) → Prop) (hh : ∀ Y, H Y → WeaklyRigid Y) :
    ∃ J : σ → Prop, WeaklyRigid J ∧ LUB J H :=
  (BooleanCompleteness.to_lub bc H).elim fun J hj =>
    ⟨J, represented_join_preserves_weak_rigidity H J hj hh, hj⟩

theorem rigid_fragment_complete (bc : BooleanCompleteness (σ → Prop))
    (rc : RigidComprehension (σ → Prop)) (H : (σ → Prop) → Prop)
    (hh : ∀ Y, H Y → Rigid Y) : ∃ J : σ → Prop, Rigid J ∧ LUB J H :=
  (BooleanCompleteness.to_lub bc H).elim fun J hj =>
    ⟨J, (tame_iff_rigid_join_closure.1 (Proofs.rigid_comprehension_implies_tame_rigidity rc))
      H J hj hh, hj⟩

/-- Current range units are explicit and are not identified with ambient top. -/
theorem weak_fragment_unit (rc : WeakRigidComprehension (σ → Prop)) :
    ∃ U : σ → Prop, WeaklyRigid U ∧ (∀ a, U a) ∧
      ∀ Y : σ → Prop, WeaklyRigid Y → Y ≤ U :=
  (rc (fun _ => True)).elim fun U hu => ⟨U, hu.1,
    (fun a => (hu.2 a).mp trivial), fun Y hy => le_of_box_incl
      (hy.2 U fun a _ => hu.1.1 a ((hu.2 a).mp trivial))⟩

theorem rigid_fragment_unit (rc : RigidComprehension (σ → Prop)) :
    ∃ U : σ → Prop, Rigid U ∧ (∀ a, U a) ∧
      ∀ Y : σ → Prop, Rigid Y → Y ≤ U :=
  (rc (fun _ => True)).elim fun U hu => ⟨U, hu.1,
    (fun a => (hu.2 a).mp trivial), fun Y hy => le_of_box_incl
      ((weaklyRigid_of_rigid hy).2 U fun a _ =>
        (weaklyRigid_of_rigid hu.1).1 a ((hu.2 a).mp trivial))⟩

def BooleanNormalizerLaws (σ : Type) [Ty σ] : Prop :=
  ∀ R : (σ → Prop) → (σ → Prop), WeakNormalizer R →
    (∀ X, R (R X) = R X) ∧ (R (fun _ => False) = (fun _ => False)) ∧
    (∀ X Y, R (fun a => X a ∨ Y a) = (fun a => R X a ∨ R Y a)) ∧
    (∀ X Y, R (fun a => X a ∧ Y a) = (fun a => R X a ∧ R Y a)) ∧
    (∀ X, R (fun a => ¬ X a) = (fun a => R (fun _ => True) a ∧ ¬ R X a))

def NormalizerJoinPreservation (σ : Type) [Ty σ] : Prop :=
  ∀ R : (σ → Prop) → (σ → Prop), WeakNormalizer R →
    ∀ H : (σ → Prop) → Prop, ∀ J : σ → Prop,
      LUB J H → LUB (R J) (NormalizerImage R H)

def WeakFragmentInterval (σ : Type) [Ty σ] : Prop :=
  ∀ w : Prop, ActualWorld w →
    (∀ Y : σ → Prop, WeaklyRigid Y → WorldCut w Y ≤ (fun _ => w)) ∧
    (∀ Y Z : σ → Prop, WeaklyRigid Y → WeaklyRigid Z →
      (WorldCut w Y ≤ WorldCut w Z ↔ Y ≤ Z)) ∧
    (∀ X : σ → Prop, X ≤ (fun _ => w) →
      ∃ Y : σ → Prop, WeaklyRigid Y ∧ WorldCut w Y = X)

def RigidFragmentInterval (σ : Type) [Ty σ] : Prop :=
  ∀ w : Prop, ActualWorld w →
    (∀ Y : σ → Prop, Rigid Y → WorldCut w Y ≤ (fun _ => w)) ∧
    (∀ Y Z : σ → Prop, Rigid Y → Rigid Z →
      (WorldCut w Y ≤ WorldCut w Z ↔ Y ≤ Z)) ∧
    (∀ X : σ → Prop, X ≤ (fun _ => w) →
      ∃ Y : σ → Prop, Rigid Y ∧ WorldCut w Y = X)

def WeakFragmentCompleteness (σ : Type) [Ty σ] : Prop :=
  ∀ H : (σ → Prop) → Prop, (∀ Y, H Y → WeaklyRigid Y) →
    ∃ J : σ → Prop, WeaklyRigid J ∧ LUB J H

def RigidFragmentCompleteness (σ : Type) [Ty σ] : Prop :=
  ∀ H : (σ → Prop) → Prop, (∀ Y, H Y → Rigid Y) →
    ∃ J : σ → Prop, Rigid J ∧ LUB J H

theorem boolean_normalizer_laws : NecessityOfDistinctness σ → BooleanNormalizerLaws σ :=
  fun nd R hr => ⟨normalizer_idempotent R hr, normalizer_bottom R hr,
    normalizer_union R hr, normalizer_intersection nd R hr, normalizer_complement nd R hr⟩

theorem complete_normalizer_laws : Actuality → NormalizerJoinPreservation σ :=
  fun act R hr H J hj => normalizer_preserves_join R hr act H J hj

theorem weak_fragment_interval_law : WeakRigidComprehension (σ → Prop) →
    WeakFragmentInterval σ := fun rc w hw =>
  ⟨fun Y _ => world_cut_supported w Y,
    fun Y Z hy hz => world_cut_order_iff w hw Y Z hy hz,
    fun X hs => world_cut_surjective w hw rc X hs⟩

theorem rigid_fragment_interval_law : RigidComprehension (σ → Prop) →
    RigidFragmentInterval σ := fun rc w hw =>
  ⟨fun Y _ => world_cut_supported w Y,
    fun Y Z hy hz => world_cut_order_iff w hw Y Z (weaklyRigid_of_rigid hy) (weaklyRigid_of_rigid hz),
    fun X hs => rigid_world_cut_surjective w hw rc X hs⟩

theorem weak_fragment_completeness_law : BooleanCompleteness (σ → Prop) →
    WeakFragmentCompleteness σ := weak_fragment_complete

theorem rigid_fragment_completeness_law : BooleanCompleteness (σ → Prop) →
    RigidComprehension (σ → Prop) → RigidFragmentCompleteness σ := rigid_fragment_complete

/-- Rigid normalizers satisfy every weak-normalizer law, with their rigid range. -/
theorem rigid_normalizer_is_weak (R : (σ → Prop) → (σ → Prop)) (hr : RigidNormalizer R) :
    WeakNormalizer R := fun X => ⟨weaklyRigid_of_rigid (hr X).1, (hr X).2⟩

/-- Under ND these are literal ambient relative complements inside the fragment unit. -/
theorem weak_relative_complement_below (nd : NecessityOfDistinctness σ)
    (U Y : σ → Prop) (hu : WeaklyRigid U) (hy : WeaklyRigid Y) :
    WeaklyRigid (fun a => U a ∧ ¬ Y a) ∧ (fun a => U a ∧ ¬ Y a) ≤ U :=
  ⟨nd_weak_difference nd U Y hu hy,
   le_of_box_incl (nec% (fun (a : σ) (h : U a ∧ ¬ Y a) => h.1))⟩

theorem rigid_relative_complement_below (nd : NecessityOfDistinctness σ)
    (U Y : σ → Prop) (hu : Rigid U) (hy : Rigid Y) :
    Rigid (fun a => U a ∧ ¬ Y a) ∧ (fun a => U a ∧ ¬ Y a) ≤ U :=
  ⟨nd_rigid_difference nd U Y hu hy,
   le_of_box_incl (nec% (fun (a : σ) (h : U a ∧ ¬ Y a) => h.1))⟩

theorem represented_join_below_fragment_unit (H : (σ → Prop) → Prop)
    (J U : σ → Prop) (hj : LUB J H) (hh : ∀ Y, H Y → Y ≤ U) : J ≤ U :=
  (hj U).1 hh

/-- Complete interval representation, with existence of its true world and range unit. -/
def WeakFragmentAlgebra (σ : Type) [Ty σ] : Prop :=
  Actuality ∧ WeakFragmentInterval σ ∧ WeakFragmentCompleteness σ ∧
    ∃ U : σ → Prop, WeaklyRigid U ∧ (∀ a, U a) ∧
      ∀ Y : σ → Prop, WeaklyRigid Y → Y ≤ U

def RigidFragmentAlgebra (σ : Type) [Ty σ] : Prop :=
  Actuality ∧ RigidFragmentInterval σ ∧ RigidFragmentCompleteness σ ∧
    ∃ U : σ → Prop, Rigid U ∧ (∀ a, U a) ∧
      ∀ Y : σ → Prop, Rigid Y → Y ≤ U

def CompleteWeakRetraction (σ : Type) [Ty σ] : Prop :=
  UniformWeakRigidComprehension (σ → Prop) ∧
    BooleanNormalizerLaws σ ∧ NormalizerJoinPreservation σ

def CompleteRigidRetraction (σ : Type) [Ty σ] : Prop :=
  UniformRigidComprehension (σ → Prop) ∧
    BooleanNormalizerLaws σ ∧ NormalizerJoinPreservation σ

theorem weak_comprehension_actuality : WeakRigidComprehension (Prop → Prop) → Actuality :=
  fun rc => Proofs.persistent_comprehension_r_implies_actuality
    (Proofs.weak_rigid_comprehension_r_implies_persistent_comprehension_r rc)

theorem weak_comprehension_fragment_algebra : WeakRigidComprehension (Prop → Prop) →
    WeakRigidComprehension (σ → Prop) → WeakRigidComprehension ((σ → Prop) → Prop) →
    WeakFragmentAlgebra σ := fun truth low high =>
  ⟨weak_comprehension_actuality truth, weak_fragment_interval_law low,
    weak_fragment_completeness_law
      (Proofs.weak_rigid_comprehension_r_implies_boolean_completeness_r high),
    weak_fragment_unit low⟩

theorem rigid_comprehension_fragment_algebra : RigidComprehension (Prop → Prop) →
    RigidComprehension (σ → Prop) → RigidComprehension ((σ → Prop) → Prop) →
    RigidFragmentAlgebra σ := fun truth low high =>
  ⟨Proofs.rigid_comprehension_r_implies_actuality truth, rigid_fragment_interval_law low,
    rigid_fragment_completeness_law
      (Proofs.rigid_comprehension_r_implies_boolean_completeness_r high) low,
    rigid_fragment_unit low⟩

theorem nd_weak_comprehension_complete_retraction : NecessityOfDistinctness Prop →
    WeakRigidComprehension (Prop → Prop) → WeakRigidComprehension (σ → Prop) →
    WeakRigidComprehension ((σ → Prop) → (σ → Prop) → Prop) → CompleteWeakRetraction σ :=
  fun nd truth low high => ⟨nd_weak_comprehension_uniform nd low high,
    boolean_normalizer_laws (Proofs.nd_of_nd_t nd),
    complete_normalizer_laws (weak_comprehension_actuality truth)⟩

theorem nd_rigid_comprehension_complete_retraction : NecessityOfDistinctness Prop →
    RigidComprehension (Prop → Prop) → RigidComprehension (σ → Prop) →
    RigidComprehension ((σ → Prop) → (σ → Prop) → Prop) → CompleteRigidRetraction σ :=
  fun nd truth low high => ⟨nd_rigid_comprehension_uniform nd low high,
    boolean_normalizer_laws (Proofs.nd_of_nd_t nd),
    complete_normalizer_laws (Proofs.rigid_comprehension_r_implies_actuality truth)⟩

end Classicism.Research.RigidityClosure
