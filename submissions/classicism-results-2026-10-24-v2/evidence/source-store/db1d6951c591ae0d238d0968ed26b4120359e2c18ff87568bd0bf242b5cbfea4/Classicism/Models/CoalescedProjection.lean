import Mathlib.Data.Set.Function

/-!
# Set projections for a root coalesced from two leaves

These are set-theoretic lemmas, independent of a Classicist premodel. A root
property has an arbitrary root extension and two internal leaf extensions.
The definitions below spell out persistence and the universal test-property
condition for weak inextensibility; neither projection characterization is
assumed. Leaf families contain top and bottom and admit deletion of a singleton.

Joint surjectivity of the two transport maps is needed only for cylinder lifts.
The connection between these predicates and the object-language definitions,
and the construction of a premodel providing the transports, are separate.
No object-language extensionality or choice principle is asserted here.
-/

namespace Classicism.Meta.Intensional.CoalescedProjection

universe u v w

variable {S : Type u} {A : Type v} {B : Type w}

/-- The concrete closure properties of the available extensions at one leaf. -/
structure SetFamily (A : Type v) where
  internal : Set (Set A)
  empty_mem : (∅ : Set A) ∈ internal
  univ_mem : (Set.univ : Set A) ∈ internal
  delete_singleton : ∀ E ∈ internal, ∀ a : A, E \ {a} ∈ internal

/-- A property specified by its three extensions, with a free root coordinate. -/
structure PropertyTriple (S : Type u) (A : Type v) (B : Type w) where
  root : Set S
  left : Set A
  right : Set B

def Admissible (FA : SetFamily A) (FB : SetFamily B)
    (F : PropertyTriple S A B) : Prop :=
  F.left ∈ FA.internal ∧ F.right ∈ FB.internal

def Included (F G : PropertyTriple S A B) : Prop :=
  F.root ⊆ G.root ∧ F.left ⊆ G.left ∧ F.right ⊆ G.right

/-- Every present root member belongs to the test property at all three points. -/
def ContainsTransport (piA : S → A) (piB : S → B) (E : Set S)
    (G : PropertyTriple S A B) : Prop :=
  E ⊆ G.root ∧ piA '' E ⊆ G.left ∧ piB '' E ⊆ G.right

def WeakPersistent (piA : S → A) (piB : S → B)
    (F : PropertyTriple S A B) : Prop :=
  piA '' F.root ⊆ F.left ∧ piB '' F.root ⊆ F.right

/-- Universal quantification over all available test triples, including their
arbitrary root extensions. -/
def WeakInextensible (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (F : PropertyTriple S A B) : Prop :=
  ∀ G : PropertyTriple S A B, Admissible FA FB G →
    ContainsTransport piA piB F.root G → Included F G

def WeakRigid (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (F : PropertyTriple S A B) : Prop :=
  WeakPersistent piA piB F ∧ WeakInextensible FA FB piA piB F

theorem containsTransport_iff (piA : S → A) (piB : S → B)
    (E : Set S) (G : PropertyTriple S A B) :
    ContainsTransport piA piB E G ↔
      ∀ s ∈ E, s ∈ G.root ∧ piA s ∈ G.left ∧ piB s ∈ G.right := by
  constructor
  · intro h s hs
    exact ⟨h.1 hs, h.2.1 ⟨s, hs, rfl⟩, h.2.2 ⟨s, hs, rfl⟩⟩
  · intro h
    refine ⟨fun s hs => (h s hs).1, ?_, ?_⟩
    · rintro a ⟨s, hs, rfl⟩
      exact (h s hs).2.1
    · rintro b ⟨s, hs, rfl⟩
      exact (h s hs).2.2

/-- Singleton-deletion tests exclude every leaf member missing from the image.
Joint surjectivity and admissibility of `F` are not needed for this fact. -/
theorem weakInextensible_iff_images (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (F : PropertyTriple S A B) :
    WeakInextensible FA FB piA piB F ↔
      F.left ⊆ piA '' F.root ∧ F.right ⊆ piB '' F.root := by
  classical
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra hnot
      let G : PropertyTriple S A B := ⟨Set.univ, Set.univ \ {a}, Set.univ⟩
      have hGa : Admissible FA FB G :=
        ⟨FA.delete_singleton Set.univ FA.univ_mem a, FB.univ_mem⟩
      have hGt : ContainsTransport piA piB F.root G := by
        refine ⟨fun _ _ => Set.mem_univ _, ?_, fun _ _ => Set.mem_univ _⟩
        intro a' ha'
        refine ⟨Set.mem_univ _, ?_⟩
        have hne : a' ≠ a := fun he => hnot (he ▸ ha')
        simpa only [Set.mem_singleton_iff] using hne
      have hmem := (h G hGa hGt).2.1 ha
      exact hmem.2 (by simp)
    · intro b hb
      by_contra hnot
      let G : PropertyTriple S A B := ⟨Set.univ, Set.univ, Set.univ \ {b}⟩
      have hGa : Admissible FA FB G :=
        ⟨FA.univ_mem, FB.delete_singleton Set.univ FB.univ_mem b⟩
      have hGt : ContainsTransport piA piB F.root G := by
        refine ⟨fun _ _ => Set.mem_univ _, fun _ _ => Set.mem_univ _, ?_⟩
        intro b' hb'
        refine ⟨Set.mem_univ _, ?_⟩
        have hne : b' ≠ b := fun he => hnot (he ▸ hb')
        simpa only [Set.mem_singleton_iff] using hne
      have hmem := (h G hGa hGt).2.2 hb
      exact hmem.2 (by simp)
  · rintro ⟨hA, hB⟩ G _ hG
    exact ⟨hG.1, fun _ ha => hG.2.1 (hA ha), fun _ hb => hG.2.2 (hB hb)⟩

theorem weakRigid_iff_images (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (F : PropertyTriple S A B) :
    WeakRigid FA FB piA piB F ↔
      F.left = piA '' F.root ∧ F.right = piB '' F.root := by
  constructor
  · rintro ⟨hp, hi⟩
    have h := (weakInextensible_iff_images FA FB piA piB F).mp hi
    exact ⟨Set.Subset.antisymm h.1 hp.1, Set.Subset.antisymm h.2 hp.2⟩
  · rintro ⟨hA, hB⟩
    constructor
    · change piA '' F.root ⊆ F.left ∧ piB '' F.root ⊆ F.right
      rw [hA, hB]
      exact ⟨fun _ h => h, fun _ h => h⟩
    · apply (weakInextensible_iff_images FA FB piA piB F).mpr
      rw [hA, hB]
      exact ⟨fun _ h => h, fun _ h => h⟩

def imageTriple (piA : S → A) (piB : S → B) (E : Set S) :
    PropertyTriple S A B :=
  ⟨E, piA '' E, piB '' E⟩

theorem imageTriple_weakRigid (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (E : Set S) :
    WeakRigid FA FB piA piB (imageTriple piA piB E) :=
  (weakRigid_iff_images FA FB piA piB _).mpr ⟨rfl, rfl⟩

/-- Exactly the free root sets with internal projections admit a weakly rigid
property with that root extension. -/
theorem exists_weakRigid_iff_internal_images
    (FA : SetFamily A) (FB : SetFamily B) (piA : S → A) (piB : S → B)
    (E : Set S) :
    (∃ F : PropertyTriple S A B, Admissible FA FB F ∧ F.root = E ∧
      WeakRigid FA FB piA piB F) ↔
      piA '' E ∈ FA.internal ∧ piB '' E ∈ FB.internal := by
  constructor
  · rintro ⟨F, hF, hE, hR⟩
    obtain ⟨hA, hB⟩ := (weakRigid_iff_images FA FB piA piB F).mp hR
    rw [hE] at hA hB
    exact ⟨hA ▸ hF.1, hB ▸ hF.2⟩
  · intro h
    exact ⟨imageTriple piA piB E, h, rfl, imageTriple_weakRigid FA FB piA piB E⟩

/-- The precise richness condition needed to lift both leaf coordinates. -/
def JointlySurjective (piA : S → A) (piB : S → B) : Prop :=
  Function.Surjective (fun s => (piA s, piB s))

theorem left_cylinder_image_left (piA : S → A) (piB : S → B)
    (hpi : JointlySurjective piA piB) (b : B) (P : Set A) :
    piA '' (piA ⁻¹' P) = P := by
  apply Set.ext
  intro a
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro ha
    obtain ⟨s, hs⟩ := hpi (a, b)
    have hA : piA s = a := congrArg Prod.fst hs
    refine ⟨s, ?_, hA⟩
    change piA s ∈ P
    rw [hA]
    exact ha

theorem left_cylinder_image_right_of_nonempty (piA : S → A) (piB : S → B)
    (hpi : JointlySurjective piA piB) {P : Set A} (hP : P.Nonempty) :
    piB '' (piA ⁻¹' P) = Set.univ := by
  apply Set.ext
  intro b
  constructor
  · intro _
    exact Set.mem_univ b
  · intro _
    obtain ⟨a, ha⟩ := hP
    obtain ⟨s, hs⟩ := hpi (a, b)
    have hA : piA s = a := congrArg Prod.fst hs
    have hB : piB s = b := congrArg Prod.snd hs
    refine ⟨s, ?_, hB⟩
    change piA s ∈ P
    rw [hA]
    exact ha

theorem left_cylinder_image_right_of_empty (piA : S → A) (piB : S → B)
    {P : Set A} (hP : ¬P.Nonempty) :
    piB '' (piA ⁻¹' P) = ∅ := by
  apply Set.ext
  intro b
  constructor
  · rintro ⟨s, hs, _⟩
    exact (hP ⟨piA s, hs⟩).elim
  · intro h
    exact h.elim

theorem right_cylinder_image_right (piA : S → A) (piB : S → B)
    (hpi : JointlySurjective piA piB) (a : A) (Q : Set B) :
    piB '' (piB ⁻¹' Q) = Q := by
  apply Set.ext
  intro b
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro hb
    obtain ⟨s, hs⟩ := hpi (a, b)
    have hB : piB s = b := congrArg Prod.snd hs
    refine ⟨s, ?_, hB⟩
    change piB s ∈ Q
    rw [hB]
    exact hb

theorem right_cylinder_image_left_of_nonempty (piA : S → A) (piB : S → B)
    (hpi : JointlySurjective piA piB) {Q : Set B} (hQ : Q.Nonempty) :
    piA '' (piB ⁻¹' Q) = Set.univ := by
  apply Set.ext
  intro a
  constructor
  · intro _
    exact Set.mem_univ a
  · intro _
    obtain ⟨b, hb⟩ := hQ
    obtain ⟨s, hs⟩ := hpi (a, b)
    have hA : piA s = a := congrArg Prod.fst hs
    have hB : piB s = b := congrArg Prod.snd hs
    refine ⟨s, ?_, hA⟩
    change piB s ∈ Q
    rw [hB]
    exact hb

theorem right_cylinder_image_left_of_empty (piA : S → A) (piB : S → B)
    {Q : Set B} (hQ : ¬Q.Nonempty) :
    piA '' (piB ⁻¹' Q) = ∅ := by
  apply Set.ext
  intro a
  constructor
  · rintro ⟨s, hs, _⟩
    exact (hQ ⟨piB s, hs⟩).elim
  · intro h
    exact h.elim

theorem left_cylinder_admissible (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (hpi : JointlySurjective piA piB)
    (b : B) {P : Set A} (hP : P ∈ FA.internal) :
    Admissible FA FB (imageTriple piA piB (piA ⁻¹' P)) := by
  classical
  constructor
  · change piA '' (piA ⁻¹' P) ∈ FA.internal
    rw [left_cylinder_image_left piA piB hpi b P]
    exact hP
  · change piB '' (piA ⁻¹' P) ∈ FB.internal
    by_cases hn : P.Nonempty
    · rw [left_cylinder_image_right_of_nonempty piA piB hpi hn]
      exact FB.univ_mem
    · rw [left_cylinder_image_right_of_empty piA piB hn]
      exact FB.empty_mem

theorem right_cylinder_admissible (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (hpi : JointlySurjective piA piB)
    (a : A) {Q : Set B} (hQ : Q ∈ FB.internal) :
    Admissible FA FB (imageTriple piA piB (piB ⁻¹' Q)) := by
  classical
  constructor
  · change piA '' (piB ⁻¹' Q) ∈ FA.internal
    by_cases hn : Q.Nonempty
    · rw [right_cylinder_image_left_of_nonempty piA piB hpi hn]
      exact FA.univ_mem
    · rw [right_cylinder_image_left_of_empty piA piB hn]
      exact FA.empty_mem
  · change piB '' (piB ⁻¹' Q) ∈ FB.internal
    rw [right_cylinder_image_right piA piB hpi a Q]
    exact hQ

/-- Every internal left extension is the projection of an admissible weakly
rigid root property. The witness is its inverse-image cylinder. -/
theorem exists_weakRigid_left (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (hpi : JointlySurjective piA piB)
    (b : B) {P : Set A} (hP : P ∈ FA.internal) :
    ∃ F : PropertyTriple S A B, Admissible FA FB F ∧
      WeakRigid FA FB piA piB F ∧ F.left = P := by
  refine ⟨imageTriple piA piB (piA ⁻¹' P),
    left_cylinder_admissible FA FB piA piB hpi b hP,
    imageTriple_weakRigid FA FB piA piB _, ?_⟩
  exact left_cylinder_image_left piA piB hpi b P

theorem exists_weakRigid_right (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (hpi : JointlySurjective piA piB)
    (a : A) {Q : Set B} (hQ : Q ∈ FB.internal) :
    ∃ F : PropertyTriple S A B, Admissible FA FB F ∧
      WeakRigid FA FB piA piB F ∧ F.right = Q := by
  refine ⟨imageTriple piA piB (piB ⁻¹' Q),
    right_cylinder_admissible FA FB piA piB hpi a hQ,
    imageTriple_weakRigid FA FB piA piB _, ?_⟩
  exact right_cylinder_image_right piA piB hpi a Q

/-- Applied at the property domain, this is the projection fact needed for
rigidity of the collection of rigid properties. It is still a set theorem;
the interpretation of object-language rigidity is not assumed or proved here. -/
theorem left_image_of_weakRigid (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (hpi : JointlySurjective piA piB) (b : B) :
    PropertyTriple.left '' {F : PropertyTriple S A B |
      Admissible FA FB F ∧ WeakRigid FA FB piA piB F} = FA.internal := by
  apply Set.ext
  intro P
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact hF.1.1
  · intro hP
    obtain ⟨F, hFa, hFr, hF⟩ := exists_weakRigid_left FA FB piA piB hpi b hP
    exact ⟨F, ⟨hFa, hFr⟩, hF⟩

theorem right_image_of_weakRigid (FA : SetFamily A) (FB : SetFamily B)
    (piA : S → A) (piB : S → B) (hpi : JointlySurjective piA piB) (a : A) :
    PropertyTriple.right '' {F : PropertyTriple S A B |
      Admissible FA FB F ∧ WeakRigid FA FB piA piB F} = FB.internal := by
  apply Set.ext
  intro Q
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact hF.1.2
  · intro hQ
    obtain ⟨F, hFa, hFr, hF⟩ := exists_weakRigid_right FA FB piA piB hpi a hQ
    exact ⟨F, ⟨hFa, hFr⟩, hF⟩

end Classicism.Meta.Intensional.CoalescedProjection
