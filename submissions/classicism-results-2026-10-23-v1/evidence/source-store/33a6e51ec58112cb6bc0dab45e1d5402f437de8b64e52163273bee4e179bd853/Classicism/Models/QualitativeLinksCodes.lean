import Classicism.Models.FixedPointEntranceBarcan
import Classicism.Models.FixedPointEntranceRigidity

/-!
# Actual qualitative nonpoint codes in the entrance model

Original formalization (misc), 23 October 2026, supporting
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 5
(unpaginated). Equality propositions are the actual admitted external
equality intensions. A nonpoint code has, along h, precisely the equality
propositions between h(z) and the nonpoints at the target. Finite support,
symmetry, transport, exact-image behavior, and rigidity are proved here.
Injectivity of codes and the tail weak-rigidity counterexample are separate
obligations and are not assumed or claimed in this module.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Codes

open CategoryTheory
noncomputable section

abbrev Node := QualitativeLinks.Node
abbrev Nonpoint := QualitativeLinks.Nonpoint
abbrev tt : RTy := .arr (.rel .t) .t

/-- External equality propositions transport with their two parameters. -/
theorem equality_map {W V : cone.Ob} (h : W ⟶ V) (a b : cone.De.obj W) :
    (model.inner (.rel .t)).map h (Barcan.equalityEntity a b) =
      Barcan.equalityEntity (cone.De.map h a) (cone.De.map h b) := by
  apply model.incl_injective .t V
  rw [model.incl_map, Barcan.incl_equalityEntity, Barcan.incl_equalityEntity]
  ext ⟨U, x, k⟩
  change (cone.De.map (h ≫ k) a = cone.De.map (h ≫ k) b) ↔
    (cone.De.map k (cone.De.map h a) = cone.De.map k (cone.De.map h b))
  change (cone.De.map k (cone.De.map h a) = cone.De.map k (cone.De.map h b)) ↔
    (cone.De.map k (cone.De.map h a) = cone.De.map k (cone.De.map h b))
  rfl

def q (u v : Node) : model.Dom (B tail) (.rel .t) :=
  Barcan.equalityEntity (some u) (some v)

theorem q_map (u v : Node) (f : Node → Node) (hf : QualitativeLinks.Arrow f) :
    (model.inner (.rel .t)).map (lift tail f hf) (q u v) = q (f u) (f v) :=
  equality_map (lift tail f hf) (some u) (some v)

set_option backward.isDefEq.respectTransparency false in
theorem q_profile (u v : Node) (f : Node → Node) (hf : QualitativeLinks.Arrow f) :
    Rigidity.prof (q u v) (lift tail f hf) PUnit.unit ↔ f u = f v := by
  unfold Rigidity.prof q
  rw [Barcan.incl_equalityEntity]
  change some (f u) = some (f v) ↔ f u = f v
  exact ⟨Option.some.inj, congrArg some⟩

/-- Nonpoints in the external action; the isolated root has none. -/
def NonpointAt : (W : cone.Ob) → cone.De.obj W → Prop
  | false, _ => False
  | true, x => ∃ z : Node, Nonpoint z ∧ x = some z

theorem preserves_nonpoint {f : Node → Node} (hf : QualitativeLinks.Preserves f)
    {z : Node} (hz : Nonpoint z) : Nonpoint (f z) := by
  cases z with
  | point n => exact hz.elim
  | companion n b => exact (hf (QualitativeLinks.R.companion n b)).nonpoint
  | link n m k hnm => exact (hf (QualitativeLinks.R.link n m k hnm)).nonpoint

theorem reflects_nonpoint {f : Node → Node} (hf : QualitativeLinks.Preserves f)
    {z : Node} (hz : Nonpoint (f z)) : Nonpoint z := by
  cases z with
  | point n =>
      obtain ⟨m, hm⟩ := QualitativeLinks.preserves_points hf n
      rw [hm] at hz
      exact hz.elim
  | companion _ _ => trivial
  | link _ _ _ _ => trivial

theorem nonpoint_map {W V : cone.Ob} (h : W ⟶ V) {x : cone.De.obj W}
    (hx : NonpointAt W x) : NonpointAt V (cone.De.map h x) := by
  cases W with
  | false => exact hx.elim
  | true =>
      cases V with
      | false => exact h.property.elim
      | true =>
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨f, hf, he⟩ := h.property
          refine ⟨f z, preserves_nonpoint (QualitativeLinks.arrow_preserves hf) hz, ?_⟩
          exact he (some z)

set_option backward.isDefEq.respectTransparency false in
/-- Tail arrows cover all target nonpoints, using their actual surjectivity. -/
theorem nonpoint_surjective {V : cone.Ob} (h : B tail ⟶ V)
    {w : cone.De.obj V} (hw : NonpointAt V w) :
    ∃ v : cone.De.obj (B tail), NonpointAt (B tail) v ∧ cone.De.map h v = w := by
  cases V with
  | false => exact h.property.elim
  | true =>
      obtain ⟨z, hz, rfl⟩ := hw
      obtain ⟨f, hf, he⟩ := h.property
      obtain ⟨v, hv⟩ := QualitativeLinks.arrow_surjective hf z
      have hn : Nonpoint v := reflects_nonpoint (QualitativeLinks.arrow_preserves hf)
        (by rw [hv]; exact hz)
      refine ⟨some v, ⟨v, hn, rfl⟩, ?_⟩
      change FunCat.fn h (some v) = some z
      exact (he (some v)).trans (congrArg some hv)

/-- The profile of the code for z at each target. -/
def codeRaw (z : Node) : Intension model.inner tt (B tail) :=
  fun p => ∃ w : cone.De.obj p.1, NonpointAt p.1 w ∧
    p.2.1.1 = Barcan.equalityEntity (cone.De.map p.2.2 (some z)) w

set_option backward.isDefEq.respectTransparency false in
theorem codeRaw_mem (z : Node) : codeRaw z ∈ Set.range (model.incl tt (B tail)) := by
  apply (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
    (PinIdeal.fin cone.De) tt (B tail) (codeRaw z)).2
  refine ⟨⟨{some z}, Set.finite_singleton _, ?_⟩, ?_⟩
  · intro V h i hag
    have hz : cone.De.map h (some z) = cone.De.map i (some z) :=
      hag (some z) (Set.mem_singleton _)
    ext ⟨U, a, k⟩
    change (∃ w : cone.De.obj U, NonpointAt U w ∧
        a.1 = Barcan.equalityEntity (cone.De.map (h ≫ k) (some z)) w) ↔
      (∃ w : cone.De.obj U, NonpointAt U w ∧
        a.1 = Barcan.equalityEntity (cone.De.map (i ≫ k) (some z)) w)
    change (∃ w : cone.De.obj U, NonpointAt U w ∧
        a.1 = Barcan.equalityEntity (cone.De.map k (cone.De.map h (some z))) w) ↔
      (∃ w : cone.De.obj U, NonpointAt U w ∧
        a.1 = Barcan.equalityEntity (cone.De.map k (cone.De.map i (some z))) w)
    rw [hz]
  · intro V a k g _
    rintro ⟨w, hw, ha⟩
    refine ⟨cone.De.map g w, nonpoint_map g hw, ?_⟩
    change (model.inner (.rel .t)).map g a.1 =
      Barcan.equalityEntity (cone.De.map (k ≫ g) (some z)) (cone.De.map g w)
    rw [ha]
    change (model.inner (.rel .t)).map g
      (Barcan.equalityEntity (cone.De.map k (some z)) w) =
      Barcan.equalityEntity (cone.De.map g (cone.De.map k (some z))) (cone.De.map g w)
    exact equality_map g (cone.De.map k (some z)) w

def code (z : Node) : model.Dom (B tail) (.rel tt) :=
  Classical.choose (codeRaw_mem z)

theorem incl_code (z : Node) : model.incl tt (B tail) (code z) = codeRaw z :=
  Classical.choose_spec (codeRaw_mem z)

theorem code_profile (z : Node) {V : cone.Ob} (h : B tail ⟶ V)
    (a : Args model.inner tt V) :
    Rigidity.prof (code z) h a ↔
      ∃ w : cone.De.obj V, NonpointAt V w ∧
        a.1 = Barcan.equalityEntity (cone.De.map h (some z)) w := by
  unfold Rigidity.prof
  rw [incl_code]
  rfl

theorem code_profile_lift (z : Node) (f : Node → Node)
    (hf : QualitativeLinks.Arrow f) (r : model.Dom (B tail) (.rel .t)) :
    Rigidity.prof (code z) (lift tail f hf) (r, PUnit.unit) ↔
      ∃ w : Node, Nonpoint w ∧ r = q (f z) w := by
  rw [code_profile]
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, he⟩
    exact ⟨v, hv, he⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨some w, ⟨w, hw, rfl⟩, he⟩

set_option backward.isDefEq.respectTransparency false in
theorem code_profile_id (z : Node) (r : model.Dom (B tail) (.rel .t)) :
    Rigidity.prof (code z) (𝟙 (B tail)) (r, PUnit.unit) ↔
      ∃ w : Node, Nonpoint w ∧ r = q z w := by
  rw [code_profile]
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, he⟩
    refine ⟨v, hv, ?_⟩
    change r = q z v at he
    exact he
  · rintro ⟨w, hw, he⟩
    refine ⟨some w, ⟨w, hw, rfl⟩, ?_⟩
    change r = q z w
    exact he

theorem code_map (z : Node) (f : Node → Node) (hf : QualitativeLinks.Arrow f) :
    (model.inner (.rel tt)).map (lift tail f hf) (code z) = code (f z) := by
  apply model.incl_injective tt (B tail)
  rw [model.incl_map, incl_code, incl_code]
  ext ⟨V, a, h⟩
  exact Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every code has exactly the image of its actual extension at each arrow. -/
theorem code_exact (z : Node) : Rigidity.ExactImage (code z) := by
  intro V h a
  constructor
  · intro ha
    obtain ⟨w, hw, he⟩ := (code_profile z h a).1 ha
    obtain ⟨v, hv, hmap⟩ := nonpoint_surjective h hw
    refine ⟨(Barcan.equalityEntity (some z) v, PUnit.unit), ?_, ?_⟩
    · apply (code_profile z (𝟙 (B tail)) _).2
      refine ⟨v, hv, ?_⟩
      rfl
    · apply Prod.ext
      · change (model.inner (.rel .t)).map h (Barcan.equalityEntity (some z) v) = a.1
        rw [equality_map, hmap]
        exact he.symm
      · exact Subsingleton.elim _ _
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨v, hv, he⟩ := (code_profile z (𝟙 (B tail)) b).1 hb
    have he' : b.1 = Barcan.equalityEntity (W := B tail) (some z) v := by
      change b.1 = Barcan.equalityEntity (W := B tail) (some z) v at he
      exact he
    apply (code_profile z h _).2
    refine ⟨cone.De.map h v, nonpoint_map h hv, ?_⟩
    change (model.inner (.rel .t)).map h b.1 =
      Barcan.equalityEntity (cone.De.map h (some z)) (cone.De.map h v)
    rw [he', equality_map]

theorem code_rigid (z : Node) : Rigidity.RigidData (code z) :=
  Rigidity.exact_rigid (code z) (code_exact z)

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Codes
