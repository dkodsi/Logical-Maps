import Classicism.Models.FixedPointEntranceDistinctness
import Classicism.Models.FixedPointEntranceBarcan
import Classicism.Semantics.Arrows

/-!
# Boxed Strong Actuality in the concrete fixed-point entrance

Original formalization (misc), 23 October 2026, of
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 6
(unpaginated). The root-only proposition witnesses Strong Actuality at
the root. At the tail, the complement of equality of the marked points
is exactly the symmetry-group proposition. Every future part of that
proposition consists of symmetries, and symmetric propositions have
constant truth on symmetries. These facts discharge the actual quoted
Strong Actuality formula, including its quantification over future
propositions, and then its necessitation.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Actuality

open CategoryTheory
noncomputable section

theorem rootOnly_profile (p : Tuple model.inner .t (A tail)) :
    p ∈ model.incl .t (A tail) Distinctness.rootOnly ↔ p.1 = false := Iff.rfl

theorem rootOnly_singleton : model.incl .t (A tail) Distinctness.rootOnly =
    {(⟨A tail, PUnit.unit, 𝟙 (A tail)⟩ : Tuple model.inner .t (A tail))} := by
  ext ⟨V, ⟨⟩, k⟩
  rw [rootOnly_profile, Set.mem_singleton_iff]
  cases V with
  | false =>
      rw [root_endo_unique tail k]
      simp
      rfl
  | true =>
      constructor
      · intro h
        cases h
      · intro h
        have he := congrArg Sigma.fst h
        cases he

theorem strongActuality_root (h : A tail ⟶ A tail) :
    model.Holds h P.StrongActuality.quoted .nil := by
  apply Premodel.holds_strongActuality_at isModel h Distinctness.rootOnly rootOnly_singleton
  intro V k r r' _ _
  cases V with
  | false => exact (root_endo_unique tail r).trans (root_endo_unique tail r').symm
  | true => exact r.property.elim

set_option backward.isDefEq.respectTransparency false in
/-- A tail arrow is a symmetry exactly when it does not merge the
two distinguished external points. -/
theorem unmerged_iff_sym (h : B tail ⟶ B tail) :
    cone.De.map h Barcan.nodeZero ≠ cone.De.map h Barcan.nodeOne ↔
      h ∈ syms tail (B tail) := by
  constructor
  · intro hn
    obtain ⟨f, hf, he⟩ := h.property
    rcases hf with hf | hf
    · exact ⟨f, hf, he⟩
    · exfalso
      apply hn
      change FunCat.fn h (some (.point 0)) = FunCat.fn h (some (.point 1))
      exact (he (some (.point 0))).trans
        ((congrArg some hf.2.2).trans (he (some (.point 1))).symm)
  · rintro ⟨f, hf, he⟩ hn
    change FunCat.fn h (some (.point 0)) = FunCat.fn h (some (.point 1)) at hn
    have hpoints : some (f (.point 0)) = some (f (.point 1)) :=
      (he (some (.point 0))).symm.trans (hn.trans (he (some (.point 1))))
    have hp := hf.1.1 (Option.some.inj hpoints)
    exact Nat.zero_ne_one (QualitativeLinks.Node.point.inj hp)

/-- If a composite is a symmetry, its second factor is a symmetry.
The first factor cannot merge the marked pair and therefore has an inverse. -/
theorem sym_right_factor (k m : B tail ⟶ B tail)
    (hkm : k ≫ m ∈ syms tail (B tail)) : m ∈ syms tail (B tail) := by
  have hnk : cone.De.map k Barcan.nodeZero ≠ cone.De.map k Barcan.nodeOne := by
    intro he
    apply (unmerged_iff_sym (k ≫ m)).2 hkm
    change cone.De.map m (cone.De.map k Barcan.nodeZero) =
      cone.De.map m (cone.De.map k Barcan.nodeOne)
    exact congrArg (cone.De.map m) he
  have hk := (unmerged_iff_sym k).1 hnk
  obtain ⟨ki, hki, _, hik⟩ := syms_inv tail (B tail) k hk
  have hh := syms_comp tail hki hkm
  have he : ki ≫ (k ≫ m) = m := by
    rw [← Category.assoc, hik, Category.id_comp]
  rwa [he] at hh

set_option backward.isDefEq.respectTransparency false in
/-- The symmetry-group proposition is the admitted complement of the
already constructed external equality proposition. -/
theorem group_mem : (model.incl .t (B tail) Barcan.witness)ᶜ ∈
    Set.range (model.incl .t (B tail)) := by
  have h := isModel (entrance tail)
    (Term.neg (Term.v0 : Formula Signature.pure [.rel .t]))
    (.cons Barcan.witness .nil)
  simp only [model.sem_neg isModel, Premodel.sem_var, IEnv.get] at h
  obtain ⟨y, hy⟩ := h
  refine ⟨y, ?_⟩
  change model.incl .t (B tail) y = (model.incl .t (B tail) Barcan.witness)ᶜ at hy
  exact hy

def group : model.Dom (B tail) (.rel .t) := Classical.choose group_mem

theorem incl_group : model.incl .t (B tail) group =
    (model.incl .t (B tail) Barcan.witness)ᶜ := Classical.choose_spec group_mem

theorem group_profile {V : cone.Ob} (k : B tail ⟶ V) :
    (⟨V, PUnit.unit, k⟩ : Tuple model.inner .t (B tail)) ∈ model.incl .t (B tail) group ↔
      cone.De.map k Barcan.nodeZero ≠ cone.De.map k Barcan.nodeOne := by
  rw [incl_group, Barcan.incl_witness]
  rfl

theorem group_true :
    (⟨B tail, PUnit.unit, 𝟙 (B tail)⟩ : Tuple model.inner .t (B tail)) ∈
      model.incl .t (B tail) group :=
  (group_profile _).2 ((unmerged_iff_sym _).2 (syms_id tail _))

/-- Every admitted tail proposition has its identity truth at every symmetry. -/
theorem proposition_sym_iff (y : model.Dom (B tail) (.rel .t))
    (m : B tail ⟶ B tail) (hm : m ∈ syms tail (B tail)) :
    (⟨B tail, PUnit.unit, m⟩ : Tuple model.inner .t (B tail)) ∈ model.incl .t (B tail) y ↔
      (⟨B tail, PUnit.unit, 𝟙 (B tail)⟩ : Tuple model.inner .t (B tail)) ∈
        model.incl .t (B tail) y := by
  have hs : model.Sym (syms tail) (model.incl .t (B tail) y) :=
    ((SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
      (PinIdeal.fin cone.De) .t (B tail) (model.incl .t (B tail) y)).1 ⟨y, rfl⟩).2
  exact Premodel.Sym.at_id_iff (B := model) (syms_inv tail) hs PUnit.unit hm

set_option backward.isDefEq.respectTransparency false in
/-- Every future part of the group proposition decides every proposition
at that future object, including propositions absent from earlier domains. -/
theorem group_decides {V : cone.Ob} (k : B tail ⟶ V) (y : model.Dom V (.rel .t)) :
    Intension.map model.inner k (model.incl .t (B tail) group) ⊆ model.incl .t V y ∨
    Intension.map model.inner k (model.incl .t (B tail) group) ⊆ (model.incl .t V y)ᶜ := by
  classical
  cases V with
  | false => exact k.property.elim
  | true =>
      have hm : ∀ (m : B tail ⟶ B tail),
          (⟨B tail, PUnit.unit, m⟩ : Tuple model.inner .t (B tail)) ∈
            Intension.map model.inner k (model.incl .t (B tail) group) →
          m ∈ syms tail (B tail) := by
        intro m hp
        rw [Intension.mem_map] at hp
        exact sym_right_factor k m ((unmerged_iff_sym _).1 ((group_profile _).1 hp))
      by_cases hy : (⟨B tail, PUnit.unit, 𝟙 (B tail)⟩ :
          Tuple model.inner .t (B tail)) ∈ model.incl .t (B tail) y
      · left
        rintro ⟨U, ⟨⟩, m⟩ hp
        cases U with
        | false => exact m.property.elim
        | true => exact (proposition_sym_iff y m (hm m hp)).2 hy
      · right
        rintro ⟨U, ⟨⟩, m⟩ hp
        cases U with
        | false => exact m.property.elim
        | true => exact fun h => hy ((proposition_sym_iff y m (hm m hp)).1 h)

set_option backward.isDefEq.respectTransparency false in
/-- The semantic criterion is derived from the exact quoted formula. -/
theorem strongActuality_of_decides {V : cone.Ob} (h : A tail ⟶ V)
    (x : model.Dom V (.rel .t))
    (ht : (⟨V, PUnit.unit, 𝟙 V⟩ : Tuple model.inner .t V) ∈ model.incl .t V x)
    (hd : ∀ {U : cone.Ob} (k : V ⟶ U) (y : model.Dom U (.rel .t)),
      Intension.map model.inner k (model.incl .t V x) ⊆ model.incl .t U y ∨
      Intension.map model.inner k (model.incl .t V x) ⊆ (model.incl .t U y)ᶜ) :
    model.Holds h P.StrongActuality.quoted .nil := by
  simp only [P.StrongActuality.quoted, model.holds_exists isModel, model.holds_conj isModel,
    model.holds_box isModel, model.holds_forall isModel, model.holds_disj isModel,
    Premodel.holds_var]
  simp only [model.holds_eq isModel, Premodel.sem_var, model.sem_disj isModel,
    model.sem_neg isModel, IEnv.get, IEnv.get_map, model.incl_map]
  refine ⟨x, ht, fun {U} k y => ?_⟩
  rcases hd k y with hsub | hsub
  · exact Or.inl (Set.union_eq_right.2 hsub).symm
  · exact Or.inr (Set.union_eq_right.2 hsub).symm

theorem strongActuality_tail (h : A tail ⟶ B tail) :
    model.Holds h P.StrongActuality.quoted .nil :=
  strongActuality_of_decides h group group_true group_decides

theorem strongActuality_at {V : cone.Ob} (h : A tail ⟶ V) :
    model.Holds h P.StrongActuality.quoted .nil := by
  cases V with
  | false => exact strongActuality_root h
  | true => exact strongActuality_tail h

theorem strongActuality : model.HoldsSentence P.StrongActuality.quoted :=
  strongActuality_at (𝟙 (A tail))

theorem boxed_strongActuality :
    model.HoldsSentence (Term.box P.StrongActuality.quoted) := by
  rw [Premodel.HoldsSentence, model.holds_box isModel]
  intro V k
  exact strongActuality_at _

theorem necessary_strongActuality : model.HoldsSentence P.NecStrongActuality.quoted :=
  boxed_strongActuality

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Actuality
