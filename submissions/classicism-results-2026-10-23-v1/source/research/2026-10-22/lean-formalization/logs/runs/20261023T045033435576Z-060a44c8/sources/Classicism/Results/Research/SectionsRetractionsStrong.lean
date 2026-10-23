import Classicism.Results.Research.SectionsRetractions
import Classicism.Results.Records.C5

/-!
# Necessary injections and strong retractions

Direct source: `research/2026-10-22/notes/choice-uniformization.md`,
§§7,9,11–12 (original research, `misc`, 22 October 2026; unpaginated).

The inverse is a lambda term, not an assumed graph-realization principle.
The unary-output law is intended to be vectorized, including the empty tuple.
The separate truth-value law also states the nullary case directly.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def inverseKernel {ν B : Type} [Ty ν] [Rel B]
    (f : (ν → Prop) → B) (b : B) : ν → Prop :=
  fun u => ∀ a, b = f a → a u

theorem inverseKernel_coext {ν B : Type} [Ty ν] [Rel B]
    (f : (ν → Prop) → B) : Injective f →
    (fun a => inverseKernel f (f a)) ≡ (fun a : ν → Prop => a) := by
  intro hi a u
  exact ⟨fun h => h a rfl, fun h a' he => (hi a a' he) ▸ h⟩

theorem necessary_injection_retraction {ν B : Type} [Ty ν] [Rel B]
    (f : (ν → Prop) → B) (hi : □ (Injective f)) :
    StrongLeftInverse f (inverseKernel f) :=
  (strong_left_iff_composition f (inverseKernel f)).mpr
    (intensionality _ _ (modal_K _ _ (nec% (inverseKernel_coext f)) hi))

theorem necessary_injection_iff_retraction {ν B : Type} [Ty ν] [Rel B]
    (f : (ν → Prop) → B) :
    □ (Injective f) ↔ ∃ g, StrongLeftInverse f g :=
  ⟨fun hi => ⟨inverseKernel f, necessary_injection_retraction f hi⟩,
   fun hg => hg.elim fun g h => strong_left_necessary_injective f g h⟩

def NecessaryInjectionSplitting (ν B : Type) [Ty ν] [Rel B] : Prop :=
  ∀ f : (ν → Prop) → B, □ (Injective f) → ∃ g, StrongLeftInverse f g

theorem necessary_injection_splitting {ν B : Type} [Ty ν] [Rel B] :
    NecessaryInjectionSplitting ν B :=
  fun f hi => ⟨inverseKernel f, necessary_injection_retraction f hi⟩

def inverseKernelT {B : Type} [Rel B] (f : Prop → B) (b : B) : Prop :=
  ∀ p, b = f p → p

theorem inverseKernelT_coext {B : Type} [Rel B] (f : Prop → B) :
    Injective f → (fun p => inverseKernelT f (f p)) ≡ (fun p : Prop => p) := by
  intro hi p
  exact ⟨fun h => h p rfl, fun h q he => (hi p q he) ▸ h⟩

theorem necessary_injection_retraction_t {B : Type} [Rel B]
    (f : Prop → B) (hi : □ (Injective f)) :
    StrongLeftInverse f (inverseKernelT f) :=
  (strong_left_iff_composition f (inverseKernelT f)).mpr
    (intensionality _ _ (modal_K _ _ (nec% (inverseKernelT_coext f)) hi))

theorem necessary_injection_iff_retraction_t {B : Type} [Rel B] (f : Prop → B) :
    □ (Injective f) ↔ ∃ g, StrongLeftInverse f g :=
  ⟨fun hi => ⟨inverseKernelT f, necessary_injection_retraction_t f hi⟩,
   fun hg => hg.elim fun g h => strong_left_necessary_injective f g h⟩

theorem injectivity_persists_of_nd_barcan {A B : Type} [Ty A] [Rel B]
    (nd : NecessityOfDistinctness B) (bf : Barcan A) : InjectivityPersists A B := by
  intro f hi
  apply bf (fun a => ∀ a', f a = f a' → a = a')
  intro a
  apply bf (fun a' => f a = f a' → a = a')
  intro a'
  exact (em (a = a')).elim
    (fun he => modal_K _ _
      (nec% (fun (he : a = a') (_ : f a = f a') => he))
      (necessity_of_identity _ _ he))
    (fun hn => modal_K _ _
      (nec% (fun (hne : f a ≠ f a') (he : f a = f a') => (hne he).elim))
      (nd _ _ (fun he => hn (hi a a' he))))

theorem c5_injectivity_persists {A B : Type} [Ty A] [Rel B] :
    NecNecessityOfDistinctness Prop → InjectivityPersists A B := fun c5 =>
  injectivity_persists_of_nd_barcan
    (Proofs.necessary_distinctness_necessary_t_implies_distinctness_necessary_r c5)
    (Proofs.necessary_nd_implies_bf c5)

theorem persistent_injections_strong_retractions {ν B : Type} [Ty ν] [Rel B] :
    InjectivityPersists (ν → Prop) B → StrongLeftSplitting (ν → Prop) B :=
  fun hp f hi => ⟨inverseKernel f, necessary_injection_retraction f (hp f hi)⟩

theorem c5_strong_retractions {ν B : Type} [Ty ν] [Rel B] :
    NecNecessityOfDistinctness Prop → StrongLeftSplitting (ν → Prop) B :=
  fun c5 => persistent_injections_strong_retractions (c5_injectivity_persists c5)

theorem c5_strong_retractions_t {B : Type} [Rel B] :
    NecNecessityOfDistinctness Prop → StrongLeftSplitting Prop B := fun c5 f hi =>
  ⟨inverseKernelT f, necessary_injection_retraction_t f (c5_injectivity_persists c5 f hi)⟩

/-- The low-type test needs only ordinary pointwise retractions. -/
def truthEmbedding (p q r : Prop) : Prop := p ∧ r = q

theorem truthEmbedding_injective (p : Prop) (hp : p) : Injective (truthEmbedding p) :=
  fun q q' he => ((congrFun he q).mp ⟨hp, rfl⟩).2

theorem truthEmbedding_collapse (p : Prop) (hp : p = False) :
    truthEmbedding p True = truthEmbedding p False := by
  have h : truthEmbedding False True = truthEmbedding False False :=
    funext fun r => propext ⟨fun h => h.1.elim, fun h => h.1.elim⟩
  exact Eq.mpr (congrArg (fun z => truthEmbedding z True = truthEmbedding z False) hp) h

theorem truthEmbedding_inverse_possible (p : Prop) (g : (Prop → Prop) → Prop) :
    g (truthEmbedding p True) = True → g (truthEmbedding p False) = False → ◇ p :=
  fun ht hf hp => Eq.mp
    (ht.symm.trans ((congrArg g (truthEmbedding_collapse p hp)).trans hf)) trivial

theorem truth_retractions_modal_b : LeftSplitting Prop (Prop → Prop) → ModalB := by
  intro sl p hp
  obtain ⟨g, hg⟩ := sl (truthEmbedding p) (truthEmbedding_injective p hp)
  exact modal_K _ _
    (modal_K _ _ (nec% (truthEmbedding_inverse_possible p g))
      (necessity_of_identity _ _ (hg True)))
    (necessity_of_identity _ _ (hg False))

theorem truth_retractions_nd {A : Type} [Ty A] :
    LeftSplitting Prop (Prop → Prop) → NecessityOfDistinctness A :=
  fun sl => Proofs.modal_b_implies_distinctness_necessary_r (truth_retractions_modal_b sl)

end Classicism.Research.Splitting
