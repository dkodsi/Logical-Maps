import Classicism.Models.QualitativeLinksCodes
import Classicism.Models.QualitativeLinksPrescriptions

/-!
# Injectivity of the actual qualitative nonpoint codes

Original formalization (misc), 23 October 2026, of the pair-separation
and code-injectivity argument in `models/symmetric-qualitative-links.yaml`,
`tame-rigidity` (11 October 2026, unpaginated). The finite prescriptions
are actual surjective collapse maps proved in the imported module.
Equality of the model's actual propositions is tested along their lifted
arrows. No abstract code-injectivity or separation premise is assumed.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Codes.CodeInjectivity

open CategoryTheory
noncomputable section

theorem q_truth (u v : Node) (f : Node → Node) (hf : QualitativeLinks.Arrow f) :
    (⟨B tail, PUnit.unit, lift tail f hf⟩ : Tuple model.inner .t (B tail)) ∈
      model.incl .t (B tail) (q u v) ↔ f u = f v := by
  exact q_profile u v f hf

/-- Equal equality propositions have the same equality pattern along
every actual qualitative arrow. -/
theorem q_eq_pattern {u v x y : Node} (hq : q u v = q x y)
    (f : Node → Node) (hf : QualitativeLinks.Arrow f) :
    (f u = f v) ↔ (f x = f y) := by
  rw [← q_truth u v f hf, ← q_truth x y f hf, hq]

theorem q_eq_at_id {u v x y : Node} (hq : q u v = q x y) :
    (u = v) ↔ (x = y) :=
  q_eq_pattern hq id (Or.inl QualitativeLinks.sym_id)

theorem q_comm (u v : Node) : q u v = q v u := by
  apply model.incl_injective .t (B tail)
  calc
    model.incl .t (B tail) (q u v) =
        Barcan.externalEquality (W := B tail) (some u) (some v) :=
      Barcan.incl_equalityEntity (W := B tail) (some u) (some v)
    _ = Barcan.externalEquality (W := B tail) (some v) (some u) := by
      ext p
      exact eq_comm
    _ = model.incl .t (B tail) (q v u) :=
      (Barcan.incl_equalityEntity (W := B tail) (some v) (some u)).symm

/-- If a nontrivial equality proposition equals another, either of the
second pair's endpoints must occur in the first pair. Color a putative
new endpoint alone to contradict equality of the actual propositions. -/
theorem q_eq_left_mem {u v x y : Node}
    (hu : Nonpoint u) (hv : Nonpoint v) (hx : Nonpoint x) (hy : Nonpoint y)
    (hxy : x ≠ y) (hq : q u v = q x y) : x = u ∨ x = v := by
  classical
  by_contra h
  have hxu : x ≠ u := fun he => h (Or.inl he)
  have hxv : x ≠ v := fun he => h (Or.inr he)
  let U : Set Node := {u, v, x, y}
  have hU : U.Finite := (((Set.finite_singleton y).insert x).insert v).insert u
  have hV : ∀ z ∈ U, Nonpoint z := by
    intro z hz
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  let b : Node → Bool := fun z => if z = x then true else false
  obtain ⟨f, hf, hp⟩ := QualitativeLinks.Prescriptions.finite_prescription hU hV b
  have hfu : f u = .companion 0 false := by
    simpa only [b, if_neg hxu.symm] using hp u (by simp [U])
  have hfv : f v = .companion 0 false := by
    simpa only [b, if_neg hxv.symm] using hp v (by simp [U])
  have hfx : f x = .companion 0 true := by
    simpa only [b, if_pos rfl] using hp x (by simp [U])
  have hfy : f y = .companion 0 false := by
    simpa only [b, if_neg hxy.symm] using hp y (by simp [U])
  have he := (q_eq_pattern hq f (Or.inr hf)).1 (hfu.trans hfv.symm)
  rw [hfx, hfy] at he
  cases he

theorem q_eq_right_mem {u v x y : Node}
    (hu : Nonpoint u) (hv : Nonpoint v) (hx : Nonpoint x) (hy : Nonpoint y)
    (hxy : x ≠ y) (hq : q u v = q x y) : y = u ∨ y = v :=
  q_eq_left_mem hu hv hy hx hxy.symm (hq.trans (q_comm x y))

/-- Distinct nonpoint pairs define the same actual proposition only if
their unordered endpoint sets coincide. -/
theorem q_unordered_eq {u v x y : Node}
    (hu : Nonpoint u) (hv : Nonpoint v) (hx : Nonpoint x) (hy : Nonpoint y)
    (huv : u ≠ v) (hxy : x ≠ y) (hq : q u v = q x y) :
    ({u, v} : Set Node) = {x, y} := by
  have hxmem := q_eq_left_mem hu hv hx hy hxy hq
  have hymem := q_eq_right_mem hu hv hx hy hxy hq
  have humem := q_eq_left_mem hx hy hu hv huv hq.symm
  have hvmem := q_eq_right_mem hx hy hu hv huv hq.symm
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact humem
    · exact hvmem
  · rintro (rfl | rfl)
    · exact hxmem
    · exact hymem

theorem fresh_nonpoint (z z' : Node) :
    ∃ w : Node, Nonpoint w ∧ w ≠ z ∧ w ≠ z' := by
  let n := max (QualitativeLinks.Prescriptions.index z)
    (QualitativeLinks.Prescriptions.index z') + 1
  refine ⟨.companion n false, True.intro, ?_, ?_⟩
  · intro h
    have hi := congrArg QualitativeLinks.Prescriptions.index h
    change n = QualitativeLinks.Prescriptions.index z at hi
    dsimp [n] at hi
    omega
  · intro h
    have hi := congrArg QualitativeLinks.Prescriptions.index h
    change n = QualitativeLinks.Prescriptions.index z' at hi
    dsimp [n] at hi
    omega

/-- The actual admitted higher-type code distinguishes all nonpoints. -/
theorem code_injective_nonpoint {z z' : Node} (hz : Nonpoint z) (hz' : Nonpoint z')
    (hc : code z = code z') : z = z' := by
  obtain ⟨w, hw, hwz, hwz'⟩ := fresh_nonpoint z z'
  have hm : Rigidity.prof (code z) (𝟙 (B tail)) (q z w, PUnit.unit) := by
    exact (code_profile_id z (q z w)).2 ⟨w, hw, rfl⟩
  rw [hc] at hm
  obtain ⟨v, hv, hq⟩ := (code_profile_id z' (q z w)).1 hm
  have hne : z' ≠ v := by
    intro hev
    exact hwz ((q_eq_at_id hq).2 hev).symm
  rcases q_eq_left_mem hz hw hz' hv hne hq with heq | heq
  · exact heq.symm
  · exact (hwz' heq.symm).elim

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Codes.CodeInjectivity
