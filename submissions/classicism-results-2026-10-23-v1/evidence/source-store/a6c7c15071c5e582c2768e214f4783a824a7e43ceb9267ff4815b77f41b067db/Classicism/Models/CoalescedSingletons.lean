import Classicism.Models.CoalescedModel
import Classicism.Semantics.SingletonAtomicity

/-!
# Singleton intensions and atomicity in the two-leaf coalescence

Every one-world Henkin model admits singleton extensions: at `t` use truth;
at `σ → ρ` use `λx. const_ρ (x = a) ∧_ρ Y`, where `Y` is the previously
constructed singleton for the remaining arguments. This uses only term closure,
not fullness. Bottom is similarly the denotation of `const_ρ false`.

The free root can isolate a tuple at any of its three arrows by placing the
matching singleton in that coordinate and bottom in the others. Thus every
singleton intension is admitted at every world, and the general singleton
atomicity theorem applies to the actual premodel.
-/

namespace Classicism.Meta.Intensional.Coalesced

open CategoryTheory

private theorem sem_andR_local (A : Premodel Signature.pure One) (hA : A.IsModel)
    {Γ : Ctx} (h : A.W₀ ⟶ One.point) (g : IEnv (A.Dom .point) Γ) (ρ : RTy)
    (p q : Term Signature.pure Γ ρ) :
    A.sem h (.app (.app (.andR ρ) p) q) g = A.sem h p g ∩ A.sem h q g := by
  obtain ⟨p', hp⟩ := Set.mem_range.mp (hA h p g)
  obtain ⟨q', hq⟩ := Set.mem_range.mp (hA h q g)
  show A.apply (A.apply (A.andRead ρ .point) (A.sem h p g)) (A.sem h q g) = _
  rw [← hp, ← hq, A.apply_Incl, A.apply_Incl]
  exact A.app_andRead p' q'

private theorem mem_sem_constR_local (A : Premodel Signature.pure One)
    (hA : A.IsModel) {Γ : Ctx} (h : A.W₀ ⟶ One.point)
    (g : IEnv (A.Dom .point) Γ) (ρ : RTy) (p : Formula Signature.pure Γ)
    (a : Args A.inner ρ .point) :
    (⟨.point, a, 𝟙 One.point⟩ : Tuple A.inner ρ .point) ∈
      A.sem h (.app (.constR ρ) p) g ↔ A.Holds h p g := by
  obtain ⟨p', hp⟩ := Set.mem_range.mp (hA h p g)
  change _ ∈ A.apply (A.constRead ρ .point) (A.sem h p g) ↔
    (⟨.point, PUnit.unit, 𝟙 One.point⟩ : Tuple A.inner .t .point) ∈ A.sem h p g
  rw [← hp, A.apply_Incl, A.app_constRead]
  rfl

/-- Bottom is admitted at every relational type in any terminal Henkin model. -/
theorem one_extension_empty (A : Premodel Signature.pure One) (hA : A.IsModel)
    (ρ : RTy) : ∃ y : A.Dom .point (.rel ρ), extension A ρ y = ∅ := by
  let h : A.W₀ ⟶ One.point := PUnit.unit
  obtain ⟨y, hy⟩ := Set.mem_range.mp (hA h (Term.botR ρ) .nil)
  have hy' : A.incl ρ .point y = A.sem h (Term.botR ρ) .nil := hy
  refine ⟨y, ?_⟩
  apply Set.ext
  intro a
  change (⟨.point, a, 𝟙 One.point⟩ : Tuple A.inner ρ .point) ∈ A.incl ρ .point y ↔ False
  rw [hy', mem_sem_constR_local A hA]
  change (⟨.point, PUnit.unit, 𝟙 One.point⟩ : Tuple A.inner .t .point) ∈
    A.sem h Term.bot .nil ↔ False
  rw [A.sem_bot hA]
  rfl

/-- The singleton is built recursively from equality, truth, and conjunction. -/
theorem one_extension_singleton (A : Premodel Signature.pure One) (hA : A.IsModel) :
    ∀ (ρ : RTy) (a : Args A.inner ρ .point),
      ∃ y : A.Dom .point (.rel ρ), extension A ρ y = {a}
  | .t, a => by
    let h : A.W₀ ⟶ One.point := PUnit.unit
    obtain ⟨y, hy⟩ := Set.mem_range.mp (hA h (Term.top : Sentence Signature.pure) .nil)
    have hy' : A.incl .t .point y = A.sem h Term.top .nil := hy
    refine ⟨y, ?_⟩
    apply Set.ext
    intro b
    cases a
    cases b
    change (⟨.point, PUnit.unit, 𝟙 One.point⟩ : Tuple A.inner .t .point) ∈
      A.incl .t .point y ↔ PUnit.unit = PUnit.unit
    rw [hy', A.sem_top hA]
    simp
  | .arr σ ρ, (a, b) => by
    obtain ⟨y, hy⟩ := one_extension_singleton A hA ρ b
    let h : A.W₀ ⟶ One.point := PUnit.unit
    let body : Term Signature.pure [σ, σ, .rel ρ] ρ :=
      .app (.app (.andR ρ)
        (.app (.constR ρ) (Term.eq' (.var .zero) (.var (.succ .zero)))))
        (.var (.succ (.succ .zero)))
    let g : IEnv (A.Dom .point) [σ, .rel ρ] := .cons a (.cons y .nil)
    obtain ⟨z, hz⟩ := Set.mem_range.mp (hA h (Term.lam body) g)
    have hz' : A.incl (.arr σ ρ) .point z = A.sem h (Term.lam body) g := hz
    refine ⟨z, ?_⟩
    apply Set.ext
    rintro ⟨x, xs⟩
    change (⟨.point, (x, xs), 𝟙 One.point⟩ : Tuple A.inner (.arr σ ρ) .point) ∈
      A.incl (.arr σ ρ) .point z ↔ (x, xs) = (a, b)
    rw [hz', A.mem_sem_lam, Category.comp_id, A.push_id]
    change (⟨.point, xs, 𝟙 One.point⟩ : Tuple A.inner ρ .point) ∈
      A.sem h (.app (.app (.andR ρ)
        (.app (.constR ρ) (Term.eq' (.var .zero) (.var (.succ .zero)))))
        (.var (.succ (.succ .zero)))) (.cons x (.cons a (.cons y .nil))) ↔ _
    rw [sem_andR_local A hA, Set.mem_inter_iff, mem_sem_constR_local A hA,
      Premodel.holds_eq_var hA]
    change (x = a ∧ xs ∈ extension A ρ y) ↔ (x, xs) = (a, b)
    rw [hy]
    simp only [Set.mem_singleton_iff, Prod.mk.injEq]

/-- A terminal model is singleton-complete even when its relation domains are
proper Henkin subdomains of the external powersets. -/
theorem one_hasSingletons (A : Premodel Signature.pure One) (hA : A.IsModel)
    (ρ : RTy) : A.HasSingletons ρ .point := by
  rintro ⟨V, a, h⟩
  cases V
  have hh : h = 𝟙 One.point := Subsingleton.elim _ _
  subst h
  obtain ⟨y, hy⟩ := one_extension_singleton A hA ρ a
  refine ⟨y, ?_⟩
  apply Set.ext
  rintro ⟨U, b, k⟩
  cases U
  have hk : k = 𝟙 One.point := Subsingleton.elim _ _
  subst k
  change b ∈ extension A ρ y ↔
    (⟨One.point, b, 𝟙 One.point⟩ : Tuple A.inner ρ .point) = ⟨.point, a, 𝟙 One.point⟩
  rw [hy]
  simp

variable (L R : Premodel Signature.pure One)

theorem hasSingletons_left (hL : L.IsModel) (ρ : RTy) :
    (model L R).HasSingletons ρ .left := by
  rintro ⟨V, a, h⟩
  cases h
  obtain ⟨y, hy⟩ := one_extension_singleton L hL ρ (leftArgsEquiv L R ρ a)
  refine ⟨y, ?_⟩
  apply Set.ext
  rintro ⟨U, b, k⟩
  cases k
  have he : leftArgsEquiv L R ρ b = leftArgsEquiv L R ρ a ↔ b = a :=
        ⟨fun h => (leftArgsEquiv L R ρ).injective h,
          fun h => congrArg (leftArgsEquiv L R ρ) h⟩
  change leftArgsEquiv L R ρ b ∈ extension L ρ y ↔ _
  rw [hy]
  simpa [Set.mem_singleton_iff] using he

theorem hasSingletons_right (hR : R.IsModel) (ρ : RTy) :
    (model L R).HasSingletons ρ .right := by
  rintro ⟨V, a, h⟩
  cases h
  obtain ⟨y, hy⟩ := one_extension_singleton R hR ρ (rightArgsEquiv L R ρ a)
  refine ⟨y, ?_⟩
  apply Set.ext
  rintro ⟨U, b, k⟩
  cases k
  have he : rightArgsEquiv L R ρ b = rightArgsEquiv L R ρ a ↔ b = a :=
        ⟨fun h => (rightArgsEquiv L R ρ).injective h,
          fun h => congrArg (rightArgsEquiv L R ρ) h⟩
  change rightArgsEquiv L R ρ b ∈ extension R ρ y ↔ _
  rw [hy]
  simpa [Set.mem_singleton_iff] using he

theorem hasSingletons_root (hL : L.IsModel) (hR : R.IsModel) (ρ : RTy) :
    (model L R).HasSingletons ρ .root := by
  obtain ⟨l0, hl0⟩ := one_extension_empty L hL ρ
  obtain ⟨r0, hr0⟩ := one_extension_empty R hR ρ
  rintro ⟨V, a, h⟩
  cases h with
  | rootId =>
    refine ⟨({rootArgsEquiv L R ρ a}, l0, r0), ?_⟩
    apply Set.ext
    rintro ⟨U, b, k⟩
    cases k with
    | rootId =>
      have he : rootArgsEquiv L R ρ b = rootArgsEquiv L R ρ a ↔ b = a :=
        ⟨fun h => (rootArgsEquiv L R ρ).injective h,
          fun h => congrArg (rootArgsEquiv L R ρ) h⟩
      change rootArgsEquiv L R ρ b ∈ ({rootArgsEquiv L R ρ a} : Set (RootArgs L R ρ)) ↔ _
      simpa [Set.mem_singleton_iff] using he
    | toLeft =>
      change leftArgsEquiv L R ρ b ∈ extension L ρ l0 ↔ _
      rw [hl0]
      simp
    | toRight =>
      change rightArgsEquiv L R ρ b ∈ extension R ρ r0 ↔ _
      rw [hr0]
      simp
  | toLeft =>
    obtain ⟨l, hl⟩ := one_extension_singleton L hL ρ (leftArgsEquiv L R ρ a)
    refine ⟨(∅, l, r0), ?_⟩
    apply Set.ext
    rintro ⟨U, b, k⟩
    cases k with
    | rootId =>
      change rootArgsEquiv L R ρ b ∈ (∅ : Set (RootArgs L R ρ)) ↔ _
      simp
    | toLeft =>
      have he : leftArgsEquiv L R ρ b = leftArgsEquiv L R ρ a ↔ b = a :=
        ⟨fun h => (leftArgsEquiv L R ρ).injective h,
          fun h => congrArg (leftArgsEquiv L R ρ) h⟩
      change leftArgsEquiv L R ρ b ∈ extension L ρ l ↔ _
      rw [hl]
      simpa [Set.mem_singleton_iff] using he
    | toRight =>
      change rightArgsEquiv L R ρ b ∈ extension R ρ r0 ↔ _
      rw [hr0]
      simp
  | toRight =>
    obtain ⟨r, hr⟩ := one_extension_singleton R hR ρ (rightArgsEquiv L R ρ a)
    refine ⟨(∅, l0, r), ?_⟩
    apply Set.ext
    rintro ⟨U, b, k⟩
    cases k with
    | rootId =>
      change rootArgsEquiv L R ρ b ∈ (∅ : Set (RootArgs L R ρ)) ↔ _
      simp
    | toLeft =>
      change leftArgsEquiv L R ρ b ∈ extension L ρ l0 ↔ _
      rw [hl0]
      simp
    | toRight =>
      have he : rightArgsEquiv L R ρ b = rightArgsEquiv L R ρ a ↔ b = a :=
        ⟨fun h => (rightArgsEquiv L R ρ).injective h,
          fun h => congrArg (rightArgsEquiv L R ρ) h⟩
      change rightArgsEquiv L R ρ b ∈ extension R ρ r ↔ _
      rw [hr]
      simpa [Set.mem_singleton_iff] using he

theorem hasSingletons (hL : L.IsModel) (hR : R.IsModel) (ρ : RTy) (W : World) :
    (model L R).HasSingletons ρ W := by
  cases W with
  | root => exact hasSingletons_root L R hL hR ρ
  | left => exact hasSingletons_left L R hL ρ
  | right => exact hasSingletons_right L R hR ρ

/-- Actual all-relational-type Atomicity, with no fullness premise. -/
theorem holds_atomicity (hL : L.IsModel) (hR : R.IsModel)
    {W : World} (h : (model L R).W₀ ⟶ W) (ρ : RTy) :
    (model L R).Holds h (P.Atomicity.quoted ρ) .nil :=
  Premodel.holds_atomicity_of_singletons (isModel L R hL hR) h ρ
    (hasSingletons L R hL hR ρ W)

/-- The same witness construction is available at every reachable world. -/
theorem holds_box_atomicity (hL : L.IsModel) (hR : R.IsModel)
    {W : World} (h : (model L R).W₀ ⟶ W) (ρ : RTy) :
    (model L R).Holds h (P.NecAtomicity.quoted ρ) .nil :=
  Premodel.holds_box_atomicity_of_singletons (isModel L R hL hR) h ρ
    (fun {V} _ => hasSingletons L R hL hR ρ V)

#print axioms one_hasSingletons
#print axioms hasSingletons
#print axioms holds_atomicity
#print axioms holds_box_atomicity

end Classicism.Meta.Intensional.Coalesced
