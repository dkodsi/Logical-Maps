import Classicism.Models.QualitativeLinksCodes
import Classicism.Models.QualitativeLinksFibreExtension
import Classicism.Models.QualitativeLinksCodeInjectivity

/-!
# The qualitative fibre predicate at the tail

Original formalization (misc), 23 October 2026, of
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 5
(unpaginated). The actual predicate U contains, along h, the codes of the
qualitative fibre over the images of the distinguished two points. Finite
external support and symmetry give admission. The finite-support fibre
cover theorem proves its weak inextensibility, with no assumed witness or
rigidity verdict. A lambda-defined two-code test then refutes weak
inextensibility after the concrete collapse, giving failure of the official
Tame Rigidity sentence at the entrance arrow.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.TameWitness

open CategoryTheory Rigidity Codes
noncomputable section

abbrev ut : RTy := .arr (.rel tt) .t

theorem endo_eq_lift (h : B tail ⟶ B tail) :
    ∃ (f : Node → Node) (hf : QualitativeLinks.Arrow f), h = lift tail f hf := by
  obtain ⟨f, hf, he⟩ := h.property
  exact ⟨f, hf, FunCat.hom_ext (funext he)⟩

theorem lift_id : lift tail id (Or.inl QualitativeLinks.sym_id) = 𝟙 (B tail) := by
  apply FunCat.hom_ext
  funext x
  cases x <;> rfl

def Fibre (h : B tail ⟶ B tail) (z : Node) : Prop :=
  ∃ x y : Node,
    cone.De.map h (some (.point 0)) = some x ∧
    cone.De.map h (some (.point 1)) = some y ∧ QualitativeLinks.R x y z

theorem fibre_lift (f : Node → Node) (hf : QualitativeLinks.Arrow f) (z : Node) :
    Fibre (lift tail f hf) z ↔ QualitativeLinks.R (f (.point 0)) (f (.point 1)) z := by
  change (∃ x y : Node, some (f (.point 0)) = some x ∧
    some (f (.point 1)) = some y ∧ QualitativeLinks.R x y z) ↔ _
  constructor
  · rintro ⟨x, y, hx, hy, hr⟩
    rw [← Option.some.inj hx, ← Option.some.inj hy] at hr
    exact hr
  · intro hr
    exact ⟨_, _, rfl, rfl, hr⟩

def raw : Intension model.inner ut (B tail) :=
  fun p => match p with
  | ⟨false, _, _⟩ => False
  | ⟨true, a, h⟩ => ∃ z : Node, Fibre h z ∧ a.1 = code z

theorem raw_mem : raw ∈ Set.range (model.incl ut (B tail)) := by
  apply (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
    (PinIdeal.fin cone.De) ut (B tail) raw).2
  refine ⟨⟨{some (.point 0), some (.point 1)},
    (Set.finite_singleton _).insert _, ?_⟩, ?_⟩
  · intro V h i hag
    ext ⟨U, a, k⟩
    cases U with
    | false => rfl
    | true =>
      have h0 := (hag.comp_right cone.De k) (some (.point 0)) (Or.inl rfl)
      have h1 := (hag.comp_right cone.De k) (some (.point 1)) (Or.inr rfl)
      change (∃ z : Node, Fibre (h ≫ k) z ∧ a.1 = code z) ↔
        (∃ z : Node, Fibre (i ≫ k) z ∧ a.1 = code z)
      simp only [Fibre, h0, h1]
  · intro V a k g _ ha
    cases V with
    | false => exact False.elim ha
    | true =>
      obtain ⟨f, hf, rfl⟩ := endo_eq_lift g
      obtain ⟨z, ⟨x, y, hx, hy, hr⟩, ha⟩ := ha
      refine ⟨f z, ⟨f x, f y, ?_, ?_, QualitativeLinks.arrow_preserves hf hr⟩, ?_⟩
      · exact congrArg (Option.map f) hx
      · exact congrArg (Option.map f) hy
      · change (model.inner (.rel tt)).map (lift tail f hf) a.1 = code (f z)
        rw [ha, code_map]

def U : RD (B tail) ut := Classical.choose raw_mem

theorem incl_U : model.incl ut (B tail) U = raw := Classical.choose_spec raw_mem

theorem profile_lift (f : Node → Node) (hf : QualitativeLinks.Arrow f)
    (a : TA ut (B tail)) :
    prof U (lift tail f hf) a ↔
      ∃ z : Node, QualitativeLinks.R (f (.point 0)) (f (.point 1)) z ∧ a.1 = code z := by
  unfold prof
  rw [incl_U]
  change (∃ z : Node, Fibre (lift tail f hf) z ∧ a.1 = code z) ↔ _
  simp only [fibre_lift]

theorem profile_id (a : TA ut (B tail)) :
    prof U (𝟙 (B tail)) a ↔
      ∃ z : Node, QualitativeLinks.R (.point 0) (.point 1) z ∧ a.1 = code z := by
  calc
    prof U (𝟙 (B tail)) a ↔ prof U (lift tail id (Or.inl QualitativeLinks.sym_id)) a :=
      iff_of_eq (congrArg (fun h : B tail ⟶ B tail => prof U h a) lift_id).symm
    _ ↔ _ := profile_lift id (Or.inl QualitativeLinks.sym_id) a

theorem weak_persistence :
    ∀ a : TA ut (B tail), prof U (𝟙 (B tail)) a →
      ∀ {V : cone.Ob} (h : B tail ⟶ V), prof U h (Args.map model.inner ut h a) := by
  intro a ha V h
  cases V with
  | false => exact h.property.elim
  | true =>
    obtain ⟨f, hf, rfl⟩ := endo_eq_lift h
    obtain ⟨z, hz, ha⟩ := (profile_id a).1 ha
    apply (profile_lift f hf _).2
    refine ⟨f z, QualitativeLinks.arrow_preserves hf hz, ?_⟩
    change (model.inner (.rel tt)).map (lift tail f hf) a.1 = code (f z)
    rw [ha, code_map]

/-- The fibre-cover theorem repairs an arrow on a fresh source link while
preserving every external support value of the test relation. -/
theorem weak_inextensibility :
    ∀ Z : RD (B tail) ut,
      (∀ a : TA ut (B tail), prof U (𝟙 (B tail)) a →
        ∀ {V : cone.Ob} (h : B tail ⟶ V), prof Z h (Args.map model.inner ut h a)) →
      model.incl ut (B tail) U ⊆ model.incl ut (B tail) Z := by
  intro Z hZ
  obtain ⟨⟨N, hN, hp⟩, _⟩ :=
    (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
      (PinIdeal.fin cone.De) ut (B tail) (model.incl ut (B tail) Z)).1 ⟨Z, rfl⟩
  let S : Set Node := {z | some z ∈ N}
  have hinj : Function.Injective (some : Node → Option Node) := fun _ _ he => Option.some.inj he
  have hS : S.Finite := hN.preimage hinj.injOn
  rintro ⟨V, a, h⟩ ha
  cases V with
  | false => exact h.property.elim
  | true =>
    obtain ⟨f, hf, rfl⟩ := endo_eq_lift h
    obtain ⟨z, hz, ha⟩ := (profile_lift f hf a).1 ha
    obtain ⟨g, hg, hagree, z0, hz0, hgz⟩ :=
      QualitativeLinks.FibreExtension.fibre_cover hf hS hz
    have hag : AgreeOn cone.De N (lift tail g hg) (lift tail f hf) := by
      intro x hx
      cases x with
      | none => rfl
      | some x => exact congrArg some (hagree x hx)
    have hcurrent : prof U (𝟙 (B tail)) (code z0, PUnit.unit) :=
      (profile_id _).2 ⟨z0, hz0, rfl⟩
    have htest := hZ (code z0, PUnit.unit) hcurrent (lift tail g hg)
    have htuple : Args.map model.inner ut (lift tail g hg) (code z0, PUnit.unit) = a := by
      apply Prod.ext
      · change (model.inner (.rel tt)).map (lift tail g hg) (code z0) = a.1
        rw [code_map, hgz]
        exact ha.symm
      · exact Subsingleton.elim _ _
    rw [htuple] at htest
    have he := hp (B tail) (lift tail g hg) (lift tail f hf) hag
    have hi := Set.ext_iff.mp he
      (⟨B tail, a, 𝟙 (B tail)⟩ : Tuple model.inner ut (B tail))
    have hi' : prof Z (lift tail g hg) a ↔ prof Z (lift tail f hf) a := by
      change prof Z (lift tail g hg ≫ 𝟙 (B tail)) a ↔
        prof Z (lift tail f hf ≫ 𝟙 (B tail)) a at hi
      simpa only [Category.comp_id] using hi
    exact hi'.1 htest

theorem weak : WeakData U := ⟨weak_persistence, weak_inextensibility⟩

/-- The body of the actual finite-image test, with the tested relation
followed by its two parameters in the environment. -/
def pairBody : Formula Signature.pure [.rel tt, .rel tt, .rel tt] :=
  Term.disj (Term.eq' (.var .zero) (.var (.succ .zero)))
    (Term.eq' (.var .zero) (.var (.succ (.succ .zero))))

def pairTest (x y : RD (B tail) tt) : RD (B tail) ut :=
  Classical.choose (isModel (entrance tail) (.lam pairBody) (.cons x (.cons y .nil)))

theorem incl_pairTest (x y : RD (B tail) tt) :
    model.incl ut (B tail) (pairTest x y) =
      model.sem (entrance tail) (.lam pairBody) (.cons x (.cons y .nil)) :=
  Classical.choose_spec (isModel (entrance tail) (.lam pairBody) (.cons x (.cons y .nil)))

set_option backward.isDefEq.respectTransparency false in
theorem pairTest_profile (x y : RD (B tail) tt) {V : cone.Ob}
    (h : B tail ⟶ V) (a : RD V tt) :
    prof (pairTest x y) h (a, PUnit.unit) ↔
      a = (model.inner (.rel tt)).map h x ∨ a = (model.inner (.rel tt)).map h y := by
  unfold prof
  rw [incl_pairTest]
  change model.Holds ((entrance tail) ≫ h) pairBody
    (.cons a (model.push h (.cons x (.cons y .nil)))) ↔ _
  simp only [pairBody, model.holds_disj isModel, Premodel.holds_eq_var isModel,
    IEnv.get, IEnv.get_map]

def companionTest : RD (B tail) ut :=
  pairTest (code (.companion 0 false)) (code (.companion 0 true))

theorem collapsed_profile (a : TA ut (B tail)) :
    prof ((model.inner (.rel ut)).map collapse U) (𝟙 (B tail)) a ↔
      ∃ b : Bool, a.1 = code (.companion 0 b) := by
  rw [prof_map, Category.comp_id]
  constructor
  · intro ha
    obtain ⟨z, hz, he⟩ :=
      (profile_lift QualitativeLinks.collapseFn (Or.inr QualitativeLinks.collapse_collapses) a).1 ha
    obtain ⟨b, rfl⟩ := QualitativeLinks.FibreExtension.diagonal_companion hz
    exact ⟨b, he⟩
  · rintro ⟨b, he⟩
    apply (profile_lift QualitativeLinks.collapseFn
      (Or.inr QualitativeLinks.collapse_collapses) a).2
    exact ⟨.companion 0 b, QualitativeLinks.R.companion 0 b, he⟩

theorem companionTest_covers :
    ∀ a : TA ut (B tail),
      prof ((model.inner (.rel ut)).map collapse U) (𝟙 (B tail)) a →
      ∀ {V : cone.Ob} (h : B tail ⟶ V),
        prof companionTest h (Args.map model.inner ut h a) := by
  intro a ha V h
  obtain ⟨b, hb⟩ := (collapsed_profile a).1 ha
  change prof (pairTest (code (.companion 0 false)) (code (.companion 0 true))) h
    ((model.inner (.rel tt)).map h a.1, PUnit.unit)
  apply (pairTest_profile _ _ h _).2
  cases b with
  | false => exact Or.inl (congrArg ((model.inner (.rel tt)).map h) hb)
  | true => exact Or.inr (congrArg ((model.inner (.rel tt)).map h) hb)

theorem collapse_companion_code (b : Bool) :
    (model.inner (.rel tt)).map collapse (code (.companion 0 b)) =
      code (.companion 0 false) :=
  code_map (.companion 0 b) QualitativeLinks.collapseFn
    (Or.inr QualitativeLinks.collapse_collapses)

theorem after_two_collapses :
    prof U (collapse ≫ collapse) (code (.companion 0 true), PUnit.unit) := by
  unfold prof
  rw [incl_U]
  exact ⟨.companion 0 true,
    ⟨.point 0, .point 0, rfl, rfl, QualitativeLinks.R.companion 0 true⟩, rfl⟩

theorem companionTest_excludes :
    ¬ prof companionTest collapse (code (.companion 0 true), PUnit.unit) := by
  intro ht
  have hh := (pairTest_profile (code (.companion 0 false))
    (code (.companion 0 true)) collapse (code (.companion 0 true))).1 ht
  have he : code (.companion 0 true) = code (.companion 0 false) := by
    rcases hh with h | h
    · exact h.trans (collapse_companion_code false)
    · exact h.trans (collapse_companion_code true)
  have hn := Codes.CodeInjectivity.code_injective_nonpoint
    (z := .companion 0 true) (z' := .companion 0 false) True.intro True.intro he
  cases hn

theorem collapsed_not_weak : ¬ WeakData ((model.inner (.rel ut)).map collapse U) := by
  intro hw
  have hs := hw.2 companionTest companionTest_covers
  have hu := (prof_map U collapse collapse (code (.companion 0 true), PUnit.unit)).2
    after_two_collapses
  exact companionTest_excludes (hs hu)

theorem not_rigid : ¬ RigidData U := fun hr => collapsed_not_weak (hr collapse)

set_option backward.isDefEq.respectTransparency false in
/-- This is failure at the actual entrance arrow of the root model,
not a verdict about a separately assumed or rebased tail model. -/
theorem not_tail_tame :
    ¬ model.Holds (entrance tail) (P.TameRigidity.quoted ut) .nil := by
  intro H
  simp only [P.TameRigidity.quoted, model.holds_forall isModel,
    model.holds_imp isModel, model.holds_conj isModel, model.holds_box isModel,
    Premodel.holds_inclR isModel, Premodel.sem_boxR isModel, Premodel.sem_var,
    IEnv.get, IEnv.get_map, model.incl_map, Intension.mem_map,
    Set.mem_ofPred_eq, Category.comp_id, Category.id_comp] at H
  have hR := H U (by
    constructor
    · simpa only [prof] using weak.1
    · intro Z hZ V k a ha
      have hs := weak.2 Z (by simpa only [prof] using hZ)
      exact hs ha)
  apply not_rigid
  intro V k
  constructor
  · intro a ha T j
    have ha' : prof U k a := by
      simpa only [Category.comp_id] using (prof_map U k (𝟙 V) a).1 ha
    exact (prof_map U k j _).2 (hR.1 k a ha' T j)
  · intro Z hZ
    rintro ⟨T, a, j⟩ ha
    exact hR.2 k Z (fun b hb L l =>
      hZ b ((prof_map U k (𝟙 V) b).2
        (by simpa only [prof, Category.comp_id] using hb)) l)
      j a ((prof_map U k j a).1 ha)

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.TameWitness
