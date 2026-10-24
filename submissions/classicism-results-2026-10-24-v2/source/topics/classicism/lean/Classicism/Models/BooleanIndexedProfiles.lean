import Classicism.Models.BooleanGroundChecks
import Classicism.Models.BooleanColumnCoordinates

/-!
# Actual supported column profiles and their disjoint Boolean equality

Original formalization (misc), 23 October 2026, of section 7 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
An injection of the row indices into a ground domain gives explicit
coherent profiles whose values at those checked arguments are the actual
column bits. Each profile has singleton support. Distinct column profiles
have Boolean equality zero, by imposing opposite bits at a fresh row.
The injection is an explicit cardinal input; no model verdict is assumed.
-/

namespace Classicism.Meta.ChoiceBoolean.IndexedProfiles

open GroundChecks

noncomputable section

variable {K B : Type} [CompleteBooleanAlgebra B] {a : BooleanAction K B}
variable {X : ActionSpace a} {G J : Type}

def weightedPredicate (c : GroundMap X G) (f : J → G) (v : J → B) : Predicate X.space where
  toFun x := ⨆ j, X.space.eqv x (c.check (f j)) ⊓ v j
  coherent x y := by
    rw [inf_iSup_eq]
    apply iSup_le
    intro j
    have h : X.space.eqv x y ⊓ X.space.eqv x (c.check (f j)) ≤
        X.space.eqv y (c.check (f j)) := by
      rw [X.space.symm x y]
      exact X.space.trans y x (c.check (f j))
    calc
      X.space.eqv x y ⊓ (X.space.eqv x (c.check (f j)) ⊓ v j)
          = (X.space.eqv x y ⊓ X.space.eqv x (c.check (f j))) ⊓ v j :=
        (inf_assoc _ _ _).symm
      _ ≤ X.space.eqv y (c.check (f j)) ⊓ v j := inf_le_inf_right _ h
      _ ≤ ⨆ k, X.space.eqv y (c.check (f k)) ⊓ v k :=
        le_iSup (fun k : J => X.space.eqv y (c.check (f k)) ⊓ v k) j

theorem weightedPredicate_check (c : GroundMap X G) (f : J → G)
    (hf : Function.Injective f) (v : J → B) (j : J) :
    weightedPredicate c f v (c.check (f j)) = v j := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hk : j = k
    · subst k
      rw [X.space.refl, top_inf_eq]
    · rw [c.eqv]
      have hfk : f j ≠ f k := fun h => hk (hf h)
      simp only [crispSpace, if_neg hfk, bot_inf_eq, bot_le]
  · exact le_iSup_of_le j (by rw [X.space.refl, top_inf_eq])

theorem weightedPredicate_action (c : GroundMap X G) (f : J → G)
    (v : J → B) (π : Equiv.Perm K) :
    actPredicate X π (weightedPredicate c f v) =
      weightedPredicate c f (fun j => a.map π (v j)) := by
  apply Predicate.ext
  intro x
  change a.map π (⨆ j, X.space.eqv (X.action.act π⁻¹ x) (c.check (f j)) ⊓ v j) =
    ⨆ j, X.space.eqv x (c.check (f j)) ⊓ a.map π (v j)
  rw [(a.map π).map_iSup]
  apply iSup_congr
  intro j
  rw [(a.map π).map_inf, ← X.semilinear, X.action.act_inv_act, c.fixed]

section Columns

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
variable {X : ActionSpace (ColumnAlgebra.action κ)} {G : Type}
variable (c : GroundMap X G) (f : κ.out → G)

def column (i : κ.out) : Predicate X.space :=
  weightedPredicate c f (ColumnCoordinates.coordinate hκ i)

theorem column_action (π : Equiv.Perm κ.out) (i : κ.out) :
    actPredicate X π (column hκ c f i) = column hκ c f (π i) := by
  rw [column, weightedPredicate_action]
  congr 1
  funext r
  exact ColumnCoordinates.coordinate_equivariant hκ π i r

def supportedColumn (i : κ.out) : SupportedPredicate X :=
  ⟨column hκ c f i, {i}, Set.finite_singleton i, by
    intro π hπ
    change actPredicate X π (column hκ c f i) = column hκ c f i
    rw [column_action, hπ i (Set.mem_singleton i)]⟩

theorem supportedColumn_action (π : Equiv.Perm κ.out) (i : κ.out) :
    (supportedPredicateSpace X).action.act π (supportedColumn hκ c f i) =
      supportedColumn hκ c f (π i) := by
  apply Subtype.ext
  exact column_action hκ c f π i

theorem column_check (hf : Function.Injective f) (i r : κ.out) :
    column hκ c f i (c.check (f r)) = ColumnCoordinates.coordinate hκ i r :=
  weightedPredicate_check c f hf _ r

/-- Pairwise Boolean equality is zero, proved by the concrete condition
extension at a fresh row. No external generic objects are used. -/
theorem columns_eqv_zero (hf : Function.Injective f) (i j : κ.out) (hij : i ≠ j) :
    (supportedPredicateSpace X).space.eqv
      (supportedColumn hκ c f i) (supportedColumn hκ c f j) = ⊥ := by
  by_contra hn
  obtain ⟨p, hp⟩ := ConditionCompletion.dense_cone (ColumnConditions.Condition κ) _ hn
  obtain ⟨r, q, hqp, hqi, hqj⟩ := ColumnCoordinates.opposite_refinement hκ p i j hij
  have hqeq := (ConditionCompletion.cone_mono (ColumnConditions.Condition κ) hqp).trans hp
  have ht : ColumnCoordinates.cone q ≤
      iffValue (ColumnCoordinates.coordinate hκ i r) (ColumnCoordinates.coordinate hκ j r) := by
    have he := hqeq.trans
      (predicateEq_le (column hκ c f i) (column hκ c f j) (c.check (f r)))
    simpa only [column_check hκ c f hf] using he
  have hj : ColumnCoordinates.cone q ≤ ColumnCoordinates.coordinate hκ j r :=
    (le_inf ht hqi).trans (iffValue_inf_left _ _)
  have hz : ColumnCoordinates.cone q ≤ (⊥ : ColumnAlgebra.Values κ) :=
    (le_inf hj hqj).trans_eq (inf_compl_self _)
  exact ConditionCompletion.cone_ne_bot (ColumnConditions.Condition κ) q (bot_unique hz)

end Columns

end

end Classicism.Meta.ChoiceBoolean.IndexedProfiles
