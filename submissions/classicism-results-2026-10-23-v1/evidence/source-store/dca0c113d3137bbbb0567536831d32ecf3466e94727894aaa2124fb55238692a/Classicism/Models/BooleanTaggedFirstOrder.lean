import Classicism.Models.BooleanSmallFormulaSemantics
import Classicism.Models.BooleanFirstOrderSemantics
import Classicism.Models.ChoiceFirstOrderMathlib

/-!
# The actual Boolean tagged first-order interpretation

Original supporting formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md`, sections 3--4 and 9
(unpaginated). The carrier is the tagged union of the actual supported
typed domains. Different tags have equality zero. Sort predicates are
crisp, and profile predicates are the coherent extension of actual typed
profile evaluation. Their value on correctly tagged tuples is proved
exactly, rather than supplied as a model-verdict assumption.

The guarded translation is MathlibBridge's existing translation, and the
Boolean evaluator is the actual evaluator used by the extraction module.
This file asserts no Choice, protected-table coverage, or separating verdict.
-/

namespace Classicism.Meta.ChoiceBoolean.TaggedFirstOrder

open ChoiceFirstOrder TypedHierarchy

variable {K B : Type} [CompleteBooleanAlgebra B]
variable (a : BooleanAction K B) (E : Type)

noncomputable section

abbrev Carrier := Sigma (Dom a E)

/-- Equality transports within a tag and is zero between different tags. -/
def taggedEq : Carrier a E → Carrier a E → B := by
  classical
  exact fun ⟨σ, x⟩ ⟨τ, y⟩ =>
    if h : σ = τ then (DomSpace a E τ).space.eqv (h ▸ x) y else ⊥

@[simp] theorem taggedEq_same (σ : Ty) (x y : Dom a E σ) :
    taggedEq a E ⟨σ, x⟩ ⟨σ, y⟩ = (DomSpace a E σ).space.eqv x y := by
  simp [taggedEq]

theorem taggedEq_different {σ τ : Ty} (h : σ ≠ τ)
    (x : Dom a E σ) (y : Dom a E τ) :
    taggedEq a E ⟨σ, x⟩ ⟨τ, y⟩ = ⊥ := by
  simp [taggedEq, h]

abbrev space : EqualitySpace B where
  Carrier := Carrier a E
  eqv := taggedEq a E
  refl := by
    rintro ⟨σ, x⟩
    rw [taggedEq_same, (DomSpace a E σ).space.refl]
  symm := by
    rintro ⟨σ, x⟩ ⟨τ, y⟩
    by_cases h : σ = τ
    · subst τ
      simp only [taggedEq_same, (DomSpace a E σ).space.symm x y]
    · rw [taggedEq_different a E h, taggedEq_different a E (Ne.symm h)]
  trans := by
    rintro ⟨σ, x⟩ ⟨τ, y⟩ ⟨υ, z⟩
    by_cases h : σ = τ
    · subst τ
      by_cases h' : σ = υ
      · subst υ
        simpa only [taggedEq_same] using (DomSpace a E σ).space.trans x y z
      · rw [taggedEq_different a E h' y z, inf_bot_eq]
        exact bot_le
    · rw [taggedEq_different a E h x y, bot_inf_eq]
      exact bot_le

/-- The action preserves type tags and acts on the enclosed entity. -/
def actionSpace : ActionSpace a where
  space := space a E
  action :=
    { act := fun π ⟨σ, x⟩ => ⟨σ, (DomSpace a E σ).action.act π x⟩
      one_act := by
        rintro ⟨σ, x⟩
        exact congrArg (Sigma.mk σ) ((DomSpace a E σ).action.one_act x)
      mul_act := by
        rintro π η ⟨σ, x⟩
        exact congrArg (Sigma.mk σ) ((DomSpace a E σ).action.mul_act π η x) }
  semilinear := by
    rintro π ⟨σ, x⟩ ⟨τ, y⟩
    change taggedEq a E ⟨σ, (DomSpace a E σ).action.act π x⟩
      ⟨τ, (DomSpace a E τ).action.act π y⟩ = a.map π (taggedEq a E ⟨σ, x⟩ ⟨τ, y⟩)
    by_cases h : σ = τ
    · subst τ
      simp only [taggedEq_same, (DomSpace a E σ).semilinear]
    · simp only [taggedEq_different a E h, OrderIso.map_bot]

theorem carrier_finitelySupported (x : Carrier a E) :
    (actionSpace a E).action.FinitelySupported x := by
  obtain ⟨σ, x⟩ := x
  obtain ⟨S, hS, hx⟩ := dom_finitelySupported a E σ x
  refine ⟨S, hS, ?_⟩
  intro π hπ
  exact congrArg (Sigma.mk σ) (hx π hπ)

/-- Equality of a finite vector of tagged entities. -/
abbrev vectorSpace (n : Nat) : EqualitySpace B where
  Carrier := Fin n → Carrier a E
  eqv := FirstOrderSemantics.assignmentEq (space a E)
  refl := FirstOrderSemantics.assignmentEq_refl (space a E)
  symm := by
    intro xs ys
    apply iInf_congr
    intro i
    exact (space a E).symm (xs i) (ys i)
  trans := by
    intro xs ys zs
    apply le_iInf
    intro i
    exact (inf_le_inf (iInf_le _ i) (iInf_le _ i)).trans
      ((space a E).trans (xs i) (ys i) (zs i))

abbrev vectorEq {n : Nat} (xs ys : Fin n → Carrier a E) : B :=
  (vectorSpace a E n).eqv xs ys

@[simp] theorem vectorEq_refl {n : Nat} (xs : Fin n → Carrier a E) :
    vectorEq a E xs xs = ⊤ :=
  (vectorSpace a E n).refl xs

theorem vectorEq_cons {n : Nat} (x y : Carrier a E)
    (xs ys : Fin n → Carrier a E) :
    vectorEq a E (Fin.cons x xs) (Fin.cons y ys) =
      taggedEq a E x y ⊓ vectorEq a E xs ys := by
  change (⨅ i : Fin (n + 1), taggedEq a E
    (Fin.cons (α := fun _ => Carrier a E) x xs i)
    (Fin.cons (α := fun _ => Carrier a E) y ys i)) =
      taggedEq a E x y ⊓ (⨅ i : Fin n, taggedEq a E (xs i) (ys i))
  apply le_antisymm
  · apply le_inf
    · simpa only [Fin.cons_zero] using
        (iInf_le (fun i : Fin (n + 1) => taggedEq a E
          (Fin.cons (α := fun _ => Carrier a E) x xs i)
          (Fin.cons (α := fun _ => Carrier a E) y ys i)) 0)
    · apply le_iInf
      intro i
      simpa only [Fin.cons_succ] using
        (iInf_le (fun j : Fin (n + 1) => taggedEq a E
          (Fin.cons (α := fun _ => Carrier a E) x xs j)
          (Fin.cons (α := fun _ => Carrier a E) y ys j)) i.succ)
  · apply le_iInf
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact inf_le_left
    · simp only [Fin.cons_succ]
      exact inf_le_right.trans (iInf_le (fun k => taggedEq a E (xs k) (ys k)) j)

def tagArgs (ρ : RTy) (xs : Args (Dom a E) ρ) :
    Fin ρ.args.length → Carrier a E :=
  MathlibBridge.flatten (fun σ x => (⟨σ, x⟩ : Carrier a E)) ρ xs

theorem vectorEq_tagArgs : ∀ ρ (xs ys : Args (Dom a E) ρ),
    vectorEq a E (tagArgs a E ρ xs) (tagArgs a E ρ ys) = argsEq a E ρ xs ys
  | .t, xs, ys => by
    cases xs
    cases ys
    exact (vectorEq_refl a E (tagArgs a E .t PUnit.unit)).trans
      ((TupleSpace a E .t).space.refl (toTuple a E .t PUnit.unit)).symm
  | .arr σ ρ, xs, ys => by
    change Dom a E σ × Args (Dom a E) ρ at xs ys
    rcases xs with ⟨x, xs⟩
    rcases ys with ⟨y, ys⟩
    change vectorEq a E
      (Fin.cons (α := fun _ => Carrier a E) ⟨σ, x⟩ (tagArgs a E ρ xs))
      (Fin.cons (α := fun _ => Carrier a E) ⟨σ, y⟩ (tagArgs a E ρ ys)) =
      (DomSpace a E σ).space.eqv x y ⊓ argsEq a E ρ xs ys
    exact (vectorEq_cons a E ⟨σ, x⟩ ⟨σ, y⟩ _ _).trans
      (congrArg₂ (fun b c : B => b ⊓ c) (taggedEq_same a E σ x y)
        (vectorEq_tagArgs ρ xs ys))

def profileTuple (ρ : RTy) (F : Dom a E (.rel ρ)) (xs : Args (Dom a E) ρ) :
    Fin (ρ.args.length + 1) → Carrier a E :=
  Fin.cons (α := fun _ : Fin (ρ.args.length + 1) => Carrier a E)
    ⟨.rel ρ, F⟩ (tagArgs a E ρ xs)

theorem vectorEq_profileTuple (ρ : RTy) (F G : Dom a E (.rel ρ))
    (xs ys : Args (Dom a E) ρ) :
    vectorEq a E (profileTuple a E ρ F xs) (profileTuple a E ρ G ys) =
      (DomSpace a E (.rel ρ)).space.eqv F G ⊓ argsEq a E ρ xs ys := by
  rw [profileTuple, profileTuple, vectorEq_cons, taggedEq_same, vectorEq_tagArgs]

/-- Extend typed profile evaluation coherently to all tagged tuples. -/
def profileValue (ρ : RTy) (zs : Fin (ρ.args.length + 1) → Carrier a E) : B :=
  ⨆ F : Dom a E (.rel ρ), ⨆ xs : Args (Dom a E) ρ,
    vectorEq a E zs (profileTuple a E ρ F xs) ⊓ profile a E ρ F xs

theorem profileValue_coherent (ρ : RTy) :
    Coherent (vectorSpace a E (ρ.args.length + 1)) (profileValue a E ρ) := by
  intro zs ws
  change vectorEq a E zs ws ⊓
      (⨆ F : Dom a E (.rel ρ), ⨆ xs : Args (Dom a E) ρ,
        vectorEq a E zs (profileTuple a E ρ F xs) ⊓ profile a E ρ F xs) ≤
      ⨆ F : Dom a E (.rel ρ), ⨆ xs : Args (Dom a E) ρ,
        vectorEq a E ws (profileTuple a E ρ F xs) ⊓ profile a E ρ F xs
  rw [inf_iSup_eq]
  apply iSup_le
  intro F
  rw [inf_iSup_eq]
  apply iSup_le
  intro xs
  apply le_trans _ (le_iSup_of_le F (le_iSup_of_le xs le_rfl))
  apply le_inf
  · have hsym : vectorEq a E zs ws = vectorEq a E ws zs :=
      (vectorSpace a E _).symm zs ws
    exact (le_inf (inf_le_left.trans hsym.le) (inf_le_right.trans inf_le_left)).trans
      ((vectorSpace a E _).trans ws zs (profileTuple a E ρ F xs))
  · exact inf_le_right.trans inf_le_right

/-- The coherent extension agrees exactly on well-sorted tuples. -/
theorem profileValue_correct (ρ : RTy) (F : Dom a E (.rel ρ))
    (xs : Args (Dom a E) ρ) :
    profileValue a E ρ (profileTuple a E ρ F xs) = profile a E ρ F xs := by
  apply le_antisymm
  · apply iSup_le
    intro G
    apply iSup_le
    intro ys
    rw [vectorEq_profileTuple]
    exact (le_iffValue_iff.mp (profile_congr a E ρ F G xs ys)).2
  · apply le_iSup_of_le F
    apply le_iSup_of_le xs
    rw [vectorEq_refl, top_inf_eq]

def sortValue (σ : Ty) (x : Carrier a E) : B := by
  classical
  exact if x.1 = σ then ⊤ else ⊥

@[simp] theorem sortValue_same (σ : Ty) (x : Dom a E σ) :
    sortValue a E σ ⟨σ, x⟩ = ⊤ := by simp [sortValue]

theorem sortValue_different {σ τ : Ty} (h : τ ≠ σ) (x : Dom a E τ) :
    sortValue a E σ ⟨τ, x⟩ = ⊥ := by simp [sortValue, h]

theorem sortValue_coherent (σ : Ty) : Coherent (space a E) (sortValue a E σ) := by
  rintro ⟨τ, x⟩ ⟨υ, y⟩
  change taggedEq a E ⟨τ, x⟩ ⟨υ, y⟩ ⊓ sortValue a E σ ⟨τ, x⟩ ≤
    sortValue a E σ ⟨υ, y⟩
  by_cases h : τ = υ
  · subst υ
    exact inf_le_right
  · rw [taggedEq_different a E h, bot_inf_eq]
    exact bot_le

/-- An actual Boolean structure for the existing countable relational language. -/
def booleanStructure (hE : Nonempty E) :
    FirstOrderSemantics.Structure (space a E) MathlibBridge.language where
  nonempty := hE.map (fun x => (⟨.e, x⟩ : Carrier a E))
  relMap := fun {n} r => match r with
    | .sort σ => fun xs => sortValue a E σ (xs 0)
    | .profile ρ => fun xs => profileValue a E ρ xs
  rel_subst := by
    intro n r xs ys
    cases r with
    | sort σ =>
      exact (inf_le_inf_right _ (iInf_le _ 0)).trans
        (sortValue_coherent a E σ (xs 0) (ys 0))
    | profile ρ => exact profileValue_coherent a E ρ xs ys

local instance language_relational : MathlibBridge.language.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- Typed contexts use the same reversed de Bruijn levels as the existing bridge. -/
def envVector : ∀ {Γ : Ctx}, IEnv (Dom a E) Γ → Fin Γ.length → Carrier a E
  | [], .nil => Fin.elim0
  | σ :: Γ, .cons x g =>
      Fin.snoc (α := fun _ : Fin (Γ.length + 1) => Carrier a E) (envVector g) ⟨σ, x⟩

theorem variable_value : ∀ {Γ : Ctx} {σ : Ty} (v : Var Γ σ)
    (g : IEnv (Dom a E) Γ),
    FirstOrderSemantics.termValue (Sum.elim Empty.elim (envVector a E g))
      (MathlibBridge.variableTerm v) = (⟨σ, g.get v⟩ : Carrier a E)
  | _, _, .zero, .cons x g => by
    simp only [MathlibBridge.variableTerm, FirstOrderSemantics.termValue, Sum.elim_inr,
      MathlibBridge.variableIndex, envVector, Fin.snoc_last, IEnv.get]
  | _, _, .succ v, .cons x g => by
    simpa only [MathlibBridge.variableTerm, FirstOrderSemantics.termValue, Sum.elim_inr,
      MathlibBridge.variableIndex, envVector, Fin.snoc_castSucc, IEnv.get] using
      variable_value v g

theorem flatten_variables_value {Γ : Ctx} (g : IEnv (Dom a E) Γ) :
    ∀ ρ (xs : Args (fun σ => Var Γ σ) ρ),
    (fun i => FirstOrderSemantics.termValue
      (Sum.elim Empty.elim (envVector a E g))
      (MathlibBridge.flatten (fun _ v => MathlibBridge.variableTerm v) ρ xs i)) =
      tagArgs a E ρ (mapArgs (fun _ v => g.get v) ρ xs)
  | .t, _ => by funext i; exact i.elim0
  | .arr σ ρ, xs => by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [MathlibBridge.flatten, tagArgs, mapArgs, Fin.cons_zero] using
        variable_value a E xs.1 g
    · simpa only [MathlibBridge.flatten, tagArgs, mapArgs, Fin.cons_succ] using
        congrFun (flatten_variables_value g ρ xs.2) j

def valueAt (hE : Nonempty E) {Γ : Ctx} (φ : MathlibBridge.FormulaAt Γ)
    (g : IEnv (Dom a E) Γ) : B :=
  FirstOrderSemantics.value (booleanStructure a E hE) φ Empty.elim (envVector a E g)

theorem sortGuard_value (hE : Nonempty E) (σ : Ty) (n : Nat)
    (xs : Fin n → Carrier a E) (z : Carrier a E) :
    FirstOrderSemantics.value (booleanStructure a E hE) (MathlibBridge.sortGuard σ n)
      Empty.elim (Fin.snoc xs z) = sortValue a E σ z := by
  change sortValue a E σ
    (Fin.snoc (α := fun _ : Fin (n + 1) => Carrier a E) xs z (Fin.last n)) =
      sortValue a E σ z
  rw [Fin.snoc_last]

theorem guardedAll_value (hE : Nonempty E) (σ : Ty) {Γ : Ctx}
    (φ : MathlibBridge.FormulaAt (σ :: Γ)) (g : IEnv (Dom a E) Γ) :
    valueAt a E hE (MathlibBridge.guardedAll σ (Γ := Γ) φ) g =
      ⨅ x : Dom a E σ, valueAt a E hE φ (.cons x g) := by
  -- Fix the structure, environment, and finite-vector index before rewriting.
  have hguard (z : Carrier a E) :
      FirstOrderSemantics.value (booleanStructure a E hE)
        (MathlibBridge.sortGuard σ Γ.length) Empty.elim
        (Fin.snoc (envVector a E g) z) = sortValue a E σ z :=
    sortGuard_value a E hE σ Γ.length (envVector a E g) z
  simp only [valueAt, MathlibBridge.guardedAll, FirstOrderSemantics.value_all,
    FirstOrderSemantics.value_imp, hguard, envVector]
  apply le_antisymm
  · apply le_iInf
    intro x
    simpa only [sortValue_same, top_himp] using
      (iInf_le (fun z : Carrier a E => sortValue a E σ z ⇨
        FirstOrderSemantics.value (booleanStructure a E hE) φ Empty.elim
          (Fin.snoc (envVector a E g) z)) ⟨σ, x⟩)
  · apply le_iInf
    rintro ⟨τ, x⟩
    by_cases h : τ = σ
    · subst τ
      rw [sortValue_same, top_himp]
      exact iInf_le _ x
    · rw [sortValue_different a E h, bot_himp]
      exact le_top

theorem guardedEx_value (hE : Nonempty E) (σ : Ty) {Γ : Ctx}
    (φ : MathlibBridge.FormulaAt (σ :: Γ)) (g : IEnv (Dom a E) Γ) :
    valueAt a E hE (MathlibBridge.guardedEx σ (Γ := Γ) φ) g =
      ⨆ x : Dom a E σ, valueAt a E hE φ (.cons x g) := by
  -- Fix the structure, environment, and finite-vector index before rewriting.
  have hguard (z : Carrier a E) :
      FirstOrderSemantics.value (booleanStructure a E hE)
        (MathlibBridge.sortGuard σ Γ.length) Empty.elim
        (Fin.snoc (envVector a E g) z) = sortValue a E σ z :=
    sortGuard_value a E hE σ Γ.length (envVector a E g) z
  simp only [valueAt, MathlibBridge.guardedEx, FirstOrderSemantics.value_ex,
    FirstOrderSemantics.value_inf, hguard, envVector]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨τ, x⟩
    by_cases h : τ = σ
    · subst τ
      rw [sortValue_same, top_inf_eq]
      exact le_iSup (fun y : Dom a E σ =>
        FirstOrderSemantics.value (booleanStructure a E hE) φ Empty.elim
          (Fin.snoc (envVector a E g) ⟨σ, y⟩)) x
    · rw [sortValue_different a E h, bot_inf_eq]
      exact bot_le
  · apply iSup_le
    intro x
    simpa only [sortValue_same, top_inf_eq] using
      (le_iSup (fun z : Carrier a E => sortValue a E σ z ⊓
        FirstOrderSemantics.value (booleanStructure a E hE) φ Empty.elim
          (Fin.snoc (envVector a E g) z)) ⟨σ, x⟩)

theorem allArgs_value (hE : Nonempty E) : ∀ (ρ : RTy) (Γ : Ctx)
    (φ : MathlibBridge.FormulaAt (ρ.args ++ Γ)) (g : IEnv (Dom a E) Γ),
    valueAt a E hE (MathlibBridge.allArgs ρ Γ φ) g =
      ⨅ xs : Args (Dom a E) ρ,
        valueAt a E hE φ (appendEnv (argsEnv ρ xs) g)
  | .t, Γ, φ, g => by
    apply le_antisymm
    · apply le_iInf
      intro xs
      exact le_rfl
    · exact iInf_le _ PUnit.unit
  | .arr σ ρ, Γ, φ, g => by
    rw [MathlibBridge.allArgs, allArgs_value hE ρ Γ]
    calc
      _ = ⨅ ys : Args (Dom a E) ρ, ⨅ x : Dom a E σ,
          valueAt a E hE φ (.cons x (appendEnv (argsEnv ρ ys) g)) := by
        apply iInf_congr
        intro ys
        exact guardedAll_value a E hE σ φ (appendEnv (argsEnv ρ ys) g)
      _ = _ := by
        apply le_antisymm
        · apply le_iInf
          intro xs
          exact (iInf_le _ xs.2).trans (iInf_le _ xs.1)
        · apply le_iInf
          intro ys
          apply le_iInf
          intro x
          exact iInf_le _ (x, ys)

theorem exArgs_value (hE : Nonempty E) : ∀ (ρ : RTy) (Γ : Ctx)
    (φ : MathlibBridge.FormulaAt (ρ.args ++ Γ)) (g : IEnv (Dom a E) Γ),
    valueAt a E hE (MathlibBridge.exArgs ρ Γ φ) g =
      ⨆ xs : Args (Dom a E) ρ,
        valueAt a E hE φ (appendEnv (argsEnv ρ xs) g)
  | .t, Γ, φ, g => by
    change valueAt a E hE φ g = ⨆ _ : PUnit, valueAt a E hE φ g
    simp only [iSup_const]
  | .arr σ ρ, Γ, φ, g => by
    rw [MathlibBridge.exArgs, exArgs_value hE ρ Γ]
    calc
      _ = ⨆ ys : Args (Dom a E) ρ, ⨆ x : Dom a E σ,
          valueAt a E hE φ (.cons x (appendEnv (argsEnv ρ ys) g)) := by
        apply iSup_congr
        intro ys
        exact guardedEx_value a E hE σ φ (appendEnv (argsEnv ρ ys) g)
      _ = _ := by
        change (⨆ ys : Args (Dom a E) ρ, ⨆ x : Dom a E σ,
          valueAt a E hE φ (.cons x (appendEnv (argsEnv ρ ys) g))) =
          ⨆ xs : Dom a E σ × Args (Dom a E) ρ,
            valueAt a E hE φ (.cons xs.1 (appendEnv (argsEnv ρ xs.2) g))
        apply le_antisymm
        · apply iSup_le
          intro ys
          apply iSup_le
          intro x
          exact le_iSup (fun xs : Dom a E σ × Args (Dom a E) ρ =>
            valueAt a E hE φ (.cons xs.1 (appendEnv (argsEnv ρ xs.2) g))) (x, ys)
        · apply iSup_le
          intro xs
          exact (le_iSup (fun x : Dom a E σ =>
            valueAt a E hE φ (.cons x (appendEnv (argsEnv ρ xs.2) g))) xs.1).trans
              (le_iSup (fun ys : Args (Dom a E) ρ => ⨆ x : Dom a E σ,
                valueAt a E hE φ (.cons x (appendEnv (argsEnv ρ ys) g))) xs.2)

/-- Exact Boolean agreement with the already defined guarded translation. -/
theorem translate_value (hE : Nonempty E) : ∀ {Γ : Ctx} (φ : SmallFormula Γ)
    (g : IEnv (Dom a E) Γ),
    valueAt a E hE (MathlibBridge.translate φ) g =
      SmallFormulaSemantics.smallValue a E φ g
  | _, .equal (σ := σ) x y, g => by
    change taggedEq a E
      (FirstOrderSemantics.termValue (Sum.elim Empty.elim (envVector a E g))
        (MathlibBridge.variableTerm x))
      (FirstOrderSemantics.termValue (Sum.elim Empty.elim (envVector a E g))
        (MathlibBridge.variableTerm y)) = _
    rw [variable_value, variable_value, taggedEq_same] <;> rfl
  | Γ, .rel ρ x xs, g => by
    change profileValue a E ρ
      (fun i : Fin (ρ.args.length + 1) => FirstOrderSemantics.termValue
        (Sum.elim Empty.elim (envVector a E g))
        (Fin.cons (α := fun _ => MathlibBridge.language.Term (Empty ⊕ Fin Γ.length))
          (MathlibBridge.variableTerm x)
          (MathlibBridge.flatten (fun _ v => MathlibBridge.variableTerm v) ρ xs) i)) = _
    have hv : (fun i : Fin (ρ.args.length + 1) => FirstOrderSemantics.termValue
        (Sum.elim Empty.elim (envVector a E g))
        (Fin.cons (α := fun _ => MathlibBridge.language.Term (Empty ⊕ Fin Γ.length))
          (MathlibBridge.variableTerm x)
          (MathlibBridge.flatten (fun _ v => MathlibBridge.variableTerm v) ρ xs) i)) =
        profileTuple a E ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ xs) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [profileTuple, Fin.cons_zero] using variable_value a E x g
      · simpa only [profileTuple, Fin.cons_succ] using
          congrFun (flatten_variables_value a E g ρ xs) j
    rw [hv, profileValue_correct] <;> rfl
  | _, .falsum, _ => rfl
  | _, .neg p, g => by
    change FirstOrderSemantics.value (booleanStructure a E hE)
      (MathlibBridge.translate p).not Empty.elim (envVector a E g) = _
    rw [FirstOrderSemantics.value_not]
    exact congrArg (fun b : B => bᶜ) (translate_value hE p g)
  | _, .conj p q, g => by
    change FirstOrderSemantics.value (booleanStructure a E hE)
      (MathlibBridge.translate p ⊓ MathlibBridge.translate q)
      Empty.elim (envVector a E g) = _
    rw [FirstOrderSemantics.value_inf]
    exact congrArg₂ (fun b c : B => b ⊓ c) (translate_value hE p g) (translate_value hE q g)
  | _, .disj p q, g => by
    change FirstOrderSemantics.value (booleanStructure a E hE)
      (MathlibBridge.translate p ⊔ MathlibBridge.translate q)
      Empty.elim (envVector a E g) = _
    rw [FirstOrderSemantics.value_sup]
    exact congrArg₂ (fun b c : B => b ⊔ c) (translate_value hE p g) (translate_value hE q g)
  | Γ, .all ρ p, g => by
    change valueAt a E hE (MathlibBridge.allArgs ρ Γ (MathlibBridge.translate p)) g = _
    rw [allArgs_value]
    apply iInf_congr
    intro xs
    exact translate_value hE p (appendEnv (argsEnv ρ xs) g)
  | Γ, .ex ρ p, g => by
    change valueAt a E hE (MathlibBridge.exArgs ρ Γ (MathlibBridge.translate p)) g = _
    rw [exArgs_value]
    apply iSup_congr
    intro xs
    exact translate_value hE p (appendEnv (argsEnv ρ xs) g)

/-- Closed small sentences have exactly the value used by countable extraction. -/
theorem sentence_value (hE : Nonempty E) (φ : SmallFormula []) :
    FirstOrderSemantics.sentenceValue (booleanStructure a E hE) (MathlibBridge.translate φ) =
      SmallFormulaSemantics.smallValue a E φ .nil :=
  translate_value a E hE φ .nil

end

end Classicism.Meta.ChoiceBoolean.TaggedFirstOrder
