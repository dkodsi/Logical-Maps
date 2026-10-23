import Classicism.Models.ColourCollapseUnary

/-!
# Lifting rigid unary subobjects through the actual surjections

Original proofs (misc), 22 October 2026. Direct source:
research/2026-10-22/notes/colour-collapse-entrance.md, section 6
(unpaginated). Preimages are selected inside the antecedent extension;
surjectivity of the ambient individual map alone would not suffice.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

theorem weak_le_of_current {ρ : RTy} {W : cat.Ob} {F G : RD W ρ}
    (hF : WeakData F) (hG : WeakData G)
    (hc : ∀ a, prof F (𝟙 W) a → prof G (𝟙 W) a) :
    model.incl ρ W F ⊆ model.incl ρ W G :=
  hF.2 G (fun a ha V h => hG.1 a (hc a ha) h)

theorem unary_le_of_extension {W : cat.Ob} {F G : RD W et}
    (hF : WeakData F) (hG : WeakData G) (hs : extension F ⊆ extension G) :
    model.incl et W F ⊆ model.incl et W G := by
  apply weak_le_of_current hF hG
  rintro ⟨x, xu⟩ hx
  cases xu
  exact hs hx

theorem unary_eq_of_extension {W : cat.Ob} {F G : RD W et}
    (hF : WeakData F) (hG : WeakData G) (he : extension F = extension G) : F = G := by
  apply weak_eq_of_current hF hG
  rintro ⟨x, xu⟩
  cases xu
  change x ∈ extension F ↔ x ∈ extension G
  rw [he]

theorem extension_map {W V : cat.Ob} {F : RD W et} (hF : RigidData F) (h : W ⟶ V) :
    extension ((model.inner (.rel et)).map h F) = FunCat.fn h '' extension F := by
  ext y
  change prof ((model.inner (.rel et)).map h F) (𝟙 V) (y, PUnit.unit) ↔ _
  rw [prof_map, Category.comp_id, rigid_unary_exact F hF h]
  constructor
  · rintro ⟨⟨x, xu⟩, hx, hxy⟩
    cases xu
    exact ⟨x, hx, congrArg Prod.fst hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨(x, PUnit.unit), hx, Prod.ext hxy rfl⟩

theorem finite_preimage_inside {D E : Set Nat} {f : Nat → Nat}
    (hE : E.Finite) (hs : E ⊆ f '' D) :
    ∃ D' : Set Nat, D'.Finite ∧ D' ⊆ D ∧ f '' D' = E := by
  classical
  let g : Nat → Nat := fun y => if hy : y ∈ E then Classical.choose (hs hy) else 0
  have hg : ∀ y ∈ E, g y ∈ D ∧ f (g y) = y := by
    intro y hy
    dsimp [g]
    rw [dif_pos hy]
    exact Classical.choose_spec (hs hy)
  refine ⟨g '' E, hE.image g, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hg y hy).1
  · ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, hzy⟩
      rw [(hg z hz).2] at hzy
      exact hzy ▸ hz
    · intro hy
      exact ⟨g y, ⟨y, hy, rfl⟩, (hg y hy).2⟩

/-- Every rigid subrelation of a transported rigid unary relation is
itself the transport of a current rigid subrelation. -/
theorem lift_rigid_subobject {W V : cat.Ob} (F : RD W et) (hF : RigidData F)
    (h : W ⟶ V) (X : RD V et) (hX : RigidData X)
    (hXF : model.incl et V X ⊆ model.incl et V ((model.inner (.rel et)).map h F)) :
    ∃ Z : RD W et, RigidData Z ∧ model.incl et W Z ⊆ model.incl et W F ∧
      (model.inner (.rel et)).map h Z = X := by
  have hsub : extension X ⊆ FunCat.fn h '' extension F := by
    rw [← extension_map hF h]
    exact fun _ hx => hXF hx
  rcases rigid_extension X hX with hfin | hwhole
  · obtain ⟨D', hD', hDF, himage⟩ := finite_preimage_inside hfin hsub
    let Z := finiteEntity W D' hD'
    have hrZ : RigidData Z := finite_rigid W D' hD'
    have hzF : model.incl et W Z ⊆ model.incl et W F := by
      apply unary_le_of_extension (rigid_weak hrZ) (rigid_weak hF)
      simpa only [Z, extension_finite] using hDF
    refine ⟨Z, hrZ, hzF, ?_⟩
    apply unary_eq_of_extension (rigid_weak (rigid_map hrZ h)) (rigid_weak hX)
    rw [extension_map hrZ h]
    simpa only [Z, extension_finite] using himage
  · refine ⟨F, hF, Set.Subset.rfl, ?_⟩
    apply unary_eq_of_extension (rigid_weak (rigid_map hF h)) (rigid_weak hX)
    apply Set.Subset.antisymm
    · rw [hwhole]; exact Set.subset_univ _
    · exact fun _ hx => hXF hx

theorem map_preserves_subobject {ρ : RTy} {W V : cat.Ob} (h : W ⟶ V)
    {X F : RD W ρ} (hXF : model.incl ρ W X ⊆ model.incl ρ W F) :
    model.incl ρ V ((model.inner (.rel ρ)).map h X) ⊆
      model.incl ρ V ((model.inner (.rel ρ)).map h F) := by
  rintro ⟨U, a, k⟩ ha
  apply (prof_map F h k a).2
  exact hXF ((prof_map X h k a).1 ha)

/-- Once an admitted property is identified with the actual rigid-power
profile, the lifting theorem supplies its exact-image profile. The
object-language identification is discharged separately, not assumed in
the final RP theorem. -/
theorem rigid_power_exact_of_profile {W : cat.Ob} (F : RD W et) (hF : RigidData F)
    (Q : RD W (.arr (.rel et) .t))
    (hQ : ∀ {V : cat.Ob} (h : W ⟶ V) (X : RD V et),
      prof Q h (X, PUnit.unit) ↔ RigidData X ∧
        model.incl et V X ⊆ model.incl et V ((model.inner (.rel et)).map h F)) :
    ExactImage Q := by
  intro V h a
  rcases a with ⟨X, xu⟩
  cases xu
  constructor
  · intro hx
    obtain ⟨hrX, hXF⟩ := (hQ h X).1 hx
    obtain ⟨Z, hrZ, hZF, hZX⟩ := lift_rigid_subobject F hF h X hrX hXF
    refine ⟨(Z, PUnit.unit), (hQ (𝟙 W) Z).2 ?_, Prod.ext hZX rfl⟩
    exact ⟨hrZ, by simpa only [FunctorToTypes.map_id_apply] using hZF⟩
  · rintro ⟨⟨Z, zu⟩, hz, he⟩
    cases zu
    obtain ⟨hrZ, hZF⟩ := (hQ (𝟙 W) Z).1 hz
    have hZF' : model.incl et W Z ⊆ model.incl et W F := by
      simpa only [FunctorToTypes.map_id_apply] using hZF
    have hZX : (model.inner (.rel et)).map h Z = X := congrArg Prod.fst he
    subst X
    exact (hQ h _).2 ⟨rigid_map hrZ h, map_preserves_subobject h hZF'⟩

end
end Classicism.Meta.Intensional.ColourCollapse
