import Classicism.Models.FixedPointEntranceRigidity
import Classicism.Semantics.FullModels

/-!
# Root Rigid Comprehension in the fixed-point entrance model

Original formalization (misc), 23 October 2026, of
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 2
(unpaginated). Every actual extension has an admitted exact-image hull.
The hull is rigid and has that same actual extension, supplying the witness
for the official quoted Rigid Comprehension sentence at every relational
type, including propositions. Modelhood and hull admission are proved in
the imported concrete construction, not assumed here. Only root RC is
asserted; no boxed RC verdict is inferred.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Comprehension

open CategoryTheory Rigidity
noncomputable section

/-- The actual admitted relation with precisely the transported image of D. -/
def rigidRepresentative {ρ : RTy} (D : Set (TA ρ (A tail))) : RD (A tail) ρ :=
  Classical.choose (rootHull_mem D)

theorem incl_rigidRepresentative {ρ : RTy} (D : Set (TA ρ (A tail))) :
    model.incl ρ (A tail) (rigidRepresentative D) = rootHull D :=
  Classical.choose_spec (rootHull_mem D)

theorem profile_rigidRepresentative {ρ : RTy} (D : Set (TA ρ (A tail)))
    {V : cone.Ob} (h : A tail ⟶ V) (a : TA ρ V) :
    prof (rigidRepresentative D) h a ↔
      ∃ b : TA ρ (A tail), b ∈ D ∧ Args.map model.inner ρ h b = a := by
  unfold prof
  rw [incl_rigidRepresentative]
  rfl

theorem root_profile_rigidRepresentative {ρ : RTy} (D : Set (TA ρ (A tail)))
    (a : TA ρ (A tail)) :
    prof (rigidRepresentative D) (𝟙 (A tail)) a ↔ a ∈ D := by
  rw [profile_rigidRepresentative]
  constructor
  · rintro ⟨b, hb, he⟩
    have hba : b = a := (Args.map_id model.inner ρ (A tail) b).symm.trans he
    exact hba ▸ hb
  · intro ha
    exact ⟨a, ha, Args.map_id model.inner ρ (A tail) a⟩

theorem rigidRepresentative_exact {ρ : RTy} (D : Set (TA ρ (A tail))) :
    ExactImage (rigidRepresentative D) := by
  intro V h a
  constructor
  · intro ha
    obtain ⟨b, hb, he⟩ := (profile_rigidRepresentative D h a).1 ha
    exact ⟨b, (root_profile_rigidRepresentative D b).2 hb, he⟩
  · rintro ⟨b, hb, he⟩
    exact (profile_rigidRepresentative D h a).2
      ⟨b, (root_profile_rigidRepresentative D b).1 hb, he⟩

theorem rigidRepresentative_rigid {ρ : RTy} (D : Set (TA ρ (A tail))) :
    RigidData (rigidRepresentative D) :=
  exact_rigid (rigidRepresentative D) (rigidRepresentative_exact D)

/-- The actual quoted RC instance, without any fullness or RC premise. -/
theorem rigid_comprehension_at_root (ρ : RTy) :
    model.HoldsSentence (P.RigidComprehension.quoted ρ) := by
  simp only [Premodel.HoldsSentence, P.RigidComprehension.quoted,
    model.holds_forall isModel, model.holds_exists isModel, model.holds_conj isModel,
    model.holds_box isModel, model.holds_imp isModel, Premodel.holds_inclR isModel,
    Premodel.holds_coextR isModel, Premodel.sem_boxR isModel, Premodel.sem_var,
    IEnv.get, IEnv.get_map, model.incl_map, Intension.mem_map, Set.mem_ofPred_eq,
    Category.comp_id, Category.id_comp]
  intro X
  let D : Set (TA ρ (A tail)) := {a | prof X (𝟙 (A tail)) a}
  let Y : RD (A tail) ρ := rigidRepresentative D
  have hr : RigidData Y := rigidRepresentative_rigid D
  refine ⟨Y, ⟨?_, ?_⟩, ?_⟩
  · intro V k a ha U j
    have ha0 : prof Y k a := ha
    have he : prof Y (k ≫ 𝟙 V) a = prof Y k a :=
      congrArg (fun h : A tail ⟶ V => prof Y h a) (Category.comp_id k)
    have ha' : prof ((model.inner (.rel ρ)).map k Y) (𝟙 V) a :=
      (prof_map Y k (𝟙 V) a).2 (Eq.mpr he ha0)
    exact (prof_map Y k j _).1 ((hr k).1 a ha' j)
  · intro V k Z hZ U j a ha
    have hz := (hr k).2 Z (fun b hb T l => by
      have he : prof Y (k ≫ 𝟙 V) b = prof Y k b :=
        congrArg (fun h : A tail ⟶ V => prof Y h b) (Category.comp_id k)
      have hb0 : prof Y k b := Eq.mp he ((prof_map Y k (𝟙 V) b).1 hb)
      exact hZ b hb0 T l)
    exact hz ((prof_map Y k j a).2 ha)
  · intro a
    change prof X (𝟙 (A tail)) a ↔ prof Y (𝟙 (A tail)) a
    exact (root_profile_rigidRepresentative D a).symm

/-- All closed relational instances of root Rigid Comprehension hold. -/
theorem holds_rigid_comprehension_schema : model.HoldsAx P.RigidComprehension.schema := by
  rintro _ ⟨ρ, _, rfl⟩
  exact rigid_comprehension_at_root ρ

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Comprehension
