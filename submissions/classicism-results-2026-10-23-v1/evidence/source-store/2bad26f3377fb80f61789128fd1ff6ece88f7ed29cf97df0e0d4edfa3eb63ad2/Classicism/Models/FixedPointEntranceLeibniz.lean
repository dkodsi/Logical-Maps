import Classicism.Models.FixedPointEntranceBarcan
import Classicism.Certified.Schemas

/-!
# Strong Leibniz fails at every relational type of the entrance model

Original formalization (misc), 23 October 2026, strengthening the direct
proof of `research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 6
(unpaginated). At each relational type the future-only constant relation
is admitted and nonempty. Any nonempty root relation below it contains
a tuple at the tail. Unique outgoing root arrows force that same tuple
to remain in its profile both at the tail identity and at the collapse.
The admitted constant equality-of-marked-points relation separates these
two arrows, preventing the candidate from deciding every future relation.

This proves each quoted Strong Leibniz instance directly. It does not
assume a general transfer from relational Strong Leibniz to its t-instance.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Leibniz

open CategoryTheory
noncomputable section

theorem empty_mem (ρ : RTy) (W : cone.Ob) :
    (∅ : Intension model.inner ρ W) ∈ Set.range (model.incl ρ W) := by
  apply (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
    (PinIdeal.fin cone.De) ρ W ∅).2
  refine ⟨⟨∅, Set.finite_empty, fun _ _ _ _ => rfl⟩, ?_⟩
  intro _ _ _ _ _ h
  exact False.elim h

theorem dom_nonempty (σ : Ty) (W : cone.Ob) : Nonempty (model.Dom W σ) := by
  cases σ with
  | e => exact ⟨PUnit.unit⟩
  | var _ => exact ⟨PUnit.unit⟩
  | rel ρ =>
      obtain ⟨x, _⟩ := empty_mem ρ W
      exact ⟨x⟩

theorem args_nonempty (ρ : RTy) (W : cone.Ob) : Nonempty (Args model.inner ρ W) := by
  induction ρ using RTy.induction with
  | t => exact ⟨PUnit.unit⟩
  | arr σ ρ ih =>
      obtain ⟨a⟩ := dom_nonempty σ W
      obtain ⟨b⟩ := ih
      exact ⟨(a, b)⟩

def futureRaw (ρ : RTy) : Intension model.inner ρ (A tail) := fun p => p.1 = true

theorem future_mem (ρ : RTy) : futureRaw ρ ∈ Set.range (model.incl ρ (A tail)) := by
  apply (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
    (PinIdeal.fin cone.De) ρ (A tail) (futureRaw ρ)).2
  refine ⟨⟨∅, Set.finite_empty, ?_⟩, ?_⟩
  · intro V h i _
    have he : h = i := (root_hom_subsingleton tail V).elim h i
    subst i
    rfl
  · intro _ _ _ _ _ h
    exact h

def futureOnly (ρ : RTy) : model.Dom (A tail) (.rel ρ) := Classical.choose (future_mem ρ)

theorem incl_futureOnly (ρ : RTy) : model.incl ρ (A tail) (futureOnly ρ) = futureRaw ρ :=
  Classical.choose_spec (future_mem ρ)

theorem futureOnly_ne_empty (ρ : RTy) : model.incl ρ (A tail) (futureOnly ρ) ≠ ∅ := by
  obtain ⟨a⟩ := args_nonempty ρ (B tail)
  have hp : (⟨B tail, a, entrance tail⟩ : Tuple model.inner ρ (A tail)) ∈
      model.incl ρ (A tail) (futureOnly ρ) := by
    rw [incl_futureOnly]
    rfl
  intro he
  rw [he] at hp
  exact hp

/-- A nonempty part of the future-only relation has a tuple at the entrance. -/
theorem future_tuple {ρ : RTy} (W : model.Dom (A tail) (.rel ρ))
    (hW : model.incl ρ (A tail) W ≠ ∅)
    (hsub : model.incl ρ (A tail) W ⊆ model.incl ρ (A tail) (futureOnly ρ)) :
    ∃ a : Args model.inner ρ (B tail),
      (⟨B tail, a, entrance tail⟩ : Tuple model.inner ρ (A tail)) ∈ model.incl ρ (A tail) W := by
  obtain ⟨⟨V, a, k⟩, hp⟩ := Set.nonempty_iff_ne_empty.2 hW
  have hv := hsub hp
  rw [incl_futureOnly] at hv
  change V = true at hv
  cases V with
  | false => cases hv
  | true =>
      refine ⟨a, ?_⟩
      simpa only [entrance_unique tail k] using hp

/-- The marked-pair equality proposition, made constant on every tuple. -/
def splitRaw (ρ : RTy) : Intension model.inner ρ (B tail) :=
  fun p => cone.De.map p.2.2 Barcan.nodeZero = cone.De.map p.2.2 Barcan.nodeOne

theorem split_mem (ρ : RTy) : splitRaw ρ ∈ Set.range (model.incl ρ (B tail)) := by
  apply (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
    (PinIdeal.fin cone.De) ρ (B tail) (splitRaw ρ)).2
  refine ⟨⟨{Barcan.nodeZero, Barcan.nodeOne},
    (Set.finite_singleton _).insert _, ?_⟩, ?_⟩
  · intro V h i hag
    have h0 := hag Barcan.nodeZero (by simp)
    have h1 := hag Barcan.nodeOne (by simp)
    ext ⟨U, a, k⟩
    change (cone.De.map (h ≫ k) Barcan.nodeZero = cone.De.map (h ≫ k) Barcan.nodeOne) ↔
      (cone.De.map (i ≫ k) Barcan.nodeZero = cone.De.map (i ≫ k) Barcan.nodeOne)
    change (cone.De.map k (cone.De.map h Barcan.nodeZero) =
        cone.De.map k (cone.De.map h Barcan.nodeOne)) ↔
      (cone.De.map k (cone.De.map i Barcan.nodeZero) =
        cone.De.map k (cone.De.map i Barcan.nodeOne))
    rw [h0, h1]
  · intro V a k g _ he
    change cone.De.map (k ≫ g) Barcan.nodeZero = cone.De.map (k ≫ g) Barcan.nodeOne
    change cone.De.map g (cone.De.map k Barcan.nodeZero) =
      cone.De.map g (cone.De.map k Barcan.nodeOne)
    exact congrArg (cone.De.map g) he

def splitter (ρ : RTy) : model.Dom (B tail) (.rel ρ) := Classical.choose (split_mem ρ)

theorem incl_splitter (ρ : RTy) : model.incl ρ (B tail) (splitter ρ) = splitRaw ρ :=
  Classical.choose_spec (split_mem ρ)

theorem splitter_false {ρ : RTy} (a : Args model.inner ρ (B tail)) :
    (⟨B tail, a, 𝟙 (B tail)⟩ : Tuple model.inner ρ (B tail)) ∉
      model.incl ρ (B tail) (splitter ρ) := by
  rw [incl_splitter]
  change ¬ cone.De.map (𝟙 (B tail)) Barcan.nodeZero =
    cone.De.map (𝟙 (B tail)) Barcan.nodeOne
  rw [cone.De.map_id_apply (B tail) Barcan.nodeZero,
    cone.De.map_id_apply (B tail) Barcan.nodeOne]
  intro he
  exact Nat.zero_ne_one (QualitativeLinks.Node.point.inj (Option.some.inj he))

theorem splitter_true {ρ : RTy} (a : Args model.inner ρ (B tail)) :
    (⟨B tail, a, collapse⟩ : Tuple model.inner ρ (B tail)) ∈
      model.incl ρ (B tail) (splitter ρ) := by
  rw [incl_splitter]
  change some (QualitativeLinks.collapseFn (.point 0)) =
    some (QualitativeLinks.collapseFn (.point 1))
  rfl

/-- No nonempty part of the future-only relation can decide all future relations. -/
theorem no_strong_part {ρ : RTy} (W : model.Dom (A tail) (.rel ρ))
    (hW : model.incl ρ (A tail) W ≠ ∅)
    (hsub : model.incl ρ (A tail) W ⊆ model.incl ρ (A tail) (futureOnly ρ)) :
    ¬ (∀ {V : cone.Ob} (k : A tail ⟶ V) (Y : model.Dom V (.rel ρ)),
      Intension.map model.inner k (model.incl ρ (A tail) W) ⊆ model.incl ρ V Y ∨
      Intension.map model.inner k (model.incl ρ (A tail) W) ⊆ (model.incl ρ V Y)ᶜ) := by
  obtain ⟨a, ha⟩ := future_tuple W hW hsub
  have hi : (⟨B tail, a, 𝟙 (B tail)⟩ : Tuple model.inner ρ (B tail)) ∈
      Intension.map model.inner (entrance tail) (model.incl ρ (A tail) W) := by
    rw [Intension.mem_map, Category.comp_id]
    exact ha
  have hc : (⟨B tail, a, collapse⟩ : Tuple model.inner ρ (B tail)) ∈
      Intension.map model.inner (entrance tail) (model.incl ρ (A tail) W) := by
    rw [Intension.mem_map, entrance_comp]
    exact ha
  intro hdec
  rcases hdec (entrance tail) (splitter ρ) with hleft | hright
  · exact splitter_false a (hleft hi)
  · exact hright hc (splitter_true a)

set_option backward.isDefEq.respectTransparency false in
theorem sem_botR {Γ : Ctx} {V : cone.Ob} (h : model.W₀ ⟶ V)
    (g : IEnv (model.Dom V) Γ) (ρ : RTy) :
    model.sem h (Term.botR ρ : Term Signature.pure Γ ρ) g = ∅ := by
  obtain ⟨b, hb⟩ := isModel h (Term.bot : Formula Signature.pure Γ) g
  have hb' : model.incl .t V b = ∅ := by
    change model.incl .t V b = model.sem h (Term.bot : Formula Signature.pure Γ) g at hb
    exact hb.trans (model.sem_bot isModel h g)
  show model.apply (model.constRead ρ V) (model.sem h Term.bot g) = ∅
  rw [← hb, model.apply_Incl, model.app_constRead]
  ext p
  simp only [Set.mem_ofPred_eq, hb', Set.mem_empty_iff_false]

set_option backward.isDefEq.respectTransparency false in
/-- Each actual quoted relational Strong Leibniz instance fails. -/
theorem not_strongLeibniz (ρ : RTy) : ¬ model.HoldsSentence (P.StrongLeibniz.quoted ρ) := by
  simp only [Premodel.HoldsSentence, P.StrongLeibniz.quoted, model.holds_forall isModel,
    model.holds_imp isModel, model.holds_exists isModel, model.holds_conj isModel,
    model.holds_neg isModel, model.holds_box isModel, model.holds_disj isModel]
  simp only [model.holds_eq isModel, Premodel.sem_var, sem_botR, model.sem_orR isModel,
    Premodel.sem_negR isModel, IEnv.get, IEnv.get_map, model.incl_map]
  intro H
  obtain ⟨W, ⟨hW, hbox⟩, hle⟩ := H (futureOnly ρ) (futureOnly_ne_empty ρ)
  apply no_strong_part W hW (Set.union_eq_right.1 hle.symm)
  intro V k Y
  rcases @hbox V k Y with he | he
  · exact Or.inl (Set.union_eq_right.1 he.symm)
  · exact Or.inr (Set.union_eq_right.1 he.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The separately quoted propositional principle has the same actual obstruction. -/
theorem not_strongLeibniz_t : ¬ model.HoldsSentence P.StrongLeibnizT.quoted := by
  have sem_bot' : ∀ {Γ : Ctx} {V : cone.Ob} (h : model.W₀ ⟶ V)
      (g : IEnv (model.Dom V) Γ),
      model.sem h (Term.bot : Formula Signature.pure Γ) g = ∅ :=
    fun h g => model.sem_bot isModel h g
  simp only [Premodel.HoldsSentence, P.StrongLeibnizT.quoted, model.holds_forall isModel,
    model.holds_imp isModel, model.holds_exists isModel, model.holds_conj isModel,
    model.holds_neg isModel, model.holds_box isModel, model.holds_disj isModel]
  simp only [model.holds_eq isModel, Premodel.sem_var, sem_bot', model.sem_disj isModel,
    model.sem_neg isModel, IEnv.get, IEnv.get_map, model.incl_map]
  intro H
  obtain ⟨W, ⟨hW, hbox⟩, hle⟩ := H (futureOnly .t) (futureOnly_ne_empty .t)
  apply no_strong_part W hW (Set.union_eq_right.1 hle.symm)
  intro V k Y
  rcases @hbox V k Y with he | he
  · exact Or.inl (Set.union_eq_right.1 he.symm)
  · exact Or.inr (Set.union_eq_right.1 he.symm)

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Leibniz
