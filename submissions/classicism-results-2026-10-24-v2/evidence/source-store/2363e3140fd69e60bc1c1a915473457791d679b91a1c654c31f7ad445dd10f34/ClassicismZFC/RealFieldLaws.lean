import ClassicismZFC.RealFieldSentence
import ClassicismZFC.SetLaws

/-!
# Unpacked real-field clauses in arbitrary first-order models

The semantic predicates below adapt the Flypitch Project's Apache-2.0
`StdSemantics.StdSem` definitions, pinned at
218d1c1e46f77d4db80e566d1721782e85b94a17, to arbitrary interpretations of
membership and the primitive set operations. They do not use external set
membership, transitivity, or standard natural numbers.

`isField_iff` proves the correspondence with the actual quoted twenty-clause
formula. It is not a field of a model interface. Internal completeness ranges
over all objects belonging to the model's power-set object.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.RealFieldLaws

open SetLaws RealFieldSentence

universe u
variable {M : Type u} [L.Structure M]

local infix:50 " ∈ₘ " => memM

/-- `x < y`, for an order relation `ltR` given as a set of ordered pairs (`ltF`). -/
def lt (ltR x y : M) : Prop := pairM x y ∈ₘ ltR

/-- `x ≤ y`, i.e. `x < y ∨ x = y` (`leF`). -/
def le (ltR x y : M) : Prop := lt ltR x y ∨ x = y

/-- `f(x) = y`, for a function `f` given as a set of ordered pairs (`appF`). -/
def app (f x y : M) : Prop := pairM x y ∈ₘ f

/-- `op(x, y) = z`, for a binary operation `op` given as a set of pairs `((x, y), z)` (`app2F`). -/
def app2 (op x y z : M) : Prop := pairM (pairM x y) z ∈ₘ op

/-- `f` is a (total, single-valued) function from `dom` to `cod` (`isFunF`). -/
def isFun (dom cod f : M) : Prop :=
  ∀ x : M, x ∈ₘ dom → ∃ y : M, y ∈ₘ cod ∧
    (app f x y ∧ ∀ y' : M, app f x y' → y' = y)

/-- `op` is a binary operation on `R` (`isOp2F`). -/
def isOp2 (R op : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∀ y : M, y ∈ₘ R → ∃ z : M, z ∈ₘ R ∧
    (app2 op x y z ∧ ∀ z' : M, app2 op x y z' → z' = z)

/-- `m = n ∪ {n}` (`succF`). -/
def succ (n m : M) : Prop :=
  ∀ z : M, (z ∈ₘ m ↔ z ∈ₘ n ∨ z = n)

/-! #### The axioms of a complete ordered field, one by one -/

/-- Associativity of `op` on `R`. -/
def assoc (R op : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∀ y : M, y ∈ₘ R → ∀ z : M, z ∈ₘ R →
    ∀ u : M, ∀ v : M, ∀ w : M, ∀ w' : M,
      app2 op x y u → (app2 op u z v → (app2 op y z w → (app2 op x w w' → v = w')))

/-- Commutativity of `op` on `R`. -/
def comm (R op : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∀ y : M, y ∈ₘ R → ∀ u : M,
    app2 op x y u → app2 op y x u

/-- `e` is a right identity for `op` on `R`: `x ∘ e = x`. -/
def ident (R op e : M) : Prop :=
  ∀ x : M, x ∈ₘ R → app2 op x e x

/-- Additive inverses. -/
def addInv (R plus zero : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∃ y : M, y ∈ₘ R ∧ app2 plus x y zero

/-- Multiplicative inverses of nonzero elements. -/
def mulInv (R times zero one : M) : Prop :=
  ∀ x : M, x ∈ₘ R → (¬ x = zero → ∃ y : M, y ∈ₘ R ∧ app2 times x y one)

/-- Distributivity. -/
def distrib (R plus times : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∀ y : M, y ∈ₘ R → ∀ z : M, z ∈ₘ R →
    ∀ u : M, ∀ v : M, ∀ w : M, ∀ t : M, ∀ t' : M,
      app2 plus y z u → (app2 times x u v → (app2 times x y w → (app2 times x z t →
        (app2 plus w t t' → v = t'))))

/-- Irreflexivity of `<` on `R`. -/
def irrefl (R ltR : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ¬ lt ltR x x

/-- Transitivity of `<` on `R`. -/
def trans (R ltR : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∀ y : M, y ∈ₘ R → ∀ z : M, z ∈ₘ R →
    (lt ltR x y → (lt ltR y z → lt ltR x z))

/-- Totality of `<` on `R`. -/
def total (R ltR : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∀ y : M, y ∈ₘ R →
    (lt ltR x y ∨ (x = y ∨ lt ltR y x))

/-- `<` is compatible with `+`. -/
def addCompat (R plus ltR : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∀ y : M, y ∈ₘ R → ∀ z : M, z ∈ₘ R →
    ∀ u : M, ∀ v : M,
      lt ltR x y → (app2 plus x z u → (app2 plus y z v → lt ltR u v))

/-- Products of positive elements are positive. -/
def mulPos (R times ltR zero : M) : Prop :=
  ∀ x : M, x ∈ₘ R → ∀ y : M, y ∈ₘ R → ∀ u : M,
    lt ltR zero x → (lt ltR zero y → (app2 times x y u → lt ltR zero u))

/-- Dedekind completeness. -/
def complete (R ltR : M) : Prop :=
  ∀ S : M, S ∈ₘ powerM R →
    (¬ S = emptyM →
      ((∃ b : M, b ∈ₘ R ∧ ∀ s : M, s ∈ₘ S → le ltR s b) →
        ∃ u : M, u ∈ₘ R ∧
          ((∀ s : M, s ∈ₘ S → le ltR s u) ∧
            ∀ v : M, v ∈ₘ R → ((∀ s : M, s ∈ₘ S → le ltR s v) → le ltR u v))))

/-- `(R, plus, times, ltR, zero, one)` is a complete ordered field (`CompleteOrderedFieldF`). -/
def completeOrderedField (R plus times ltR zero one : M) : Prop :=
  isOp2 R plus ∧
  (isOp2 R times ∧
  (zero ∈ₘ R ∧
  (one ∈ₘ R ∧
  (assoc R plus ∧
  (comm R plus ∧
  (ident R plus zero ∧
  (addInv R plus zero ∧
  (assoc R times ∧
  (comm R times ∧
  (ident R times one ∧
  (mulInv R times zero one ∧
  (¬ zero = one ∧
  (distrib R plus times ∧
  (irrefl R ltR ∧
  (trans R ltR ∧
  (total R ltR ∧
  (addCompat R plus ltR ∧
  (mulPos R times ltR zero ∧
  complete R ltR))))))))))))))))))

/-- Unfolding the actual finite formula gives precisely these internal clauses. -/
theorem isField_iff (R plus times ltR zero one : M) :
    IsField R plus times ltR zero one ↔
      completeOrderedField R plus times ltR zero one := by
  simp [RealFieldSentence.IsField, RealFieldSentence.fieldBody, completeOrderedFieldF, andsF,
    allF, exF, allIn, exIn, andF, orF, impF, notF, memF, eqF,
    varT, isOp2F, app2F, ltF, leF,
    SetLaws.realize_pairT, SetLaws.realize_powT, SetLaws.realize_empT,
    completeOrderedField, isOp2, assoc, comm, ident, addInv, mulInv,
    distrib, irrefl, trans, total, addCompat, mulPos, complete,
    app2, lt, le, memM, Fin.snoc]

/-- Totality and global output uniqueness are already present before graph restriction. -/
theorem plus_operation {R plus times ltR zero one : M}
    (h : IsField R plus times ltR zero one) : isOp2 R plus :=
  ((isField_iff R plus times ltR zero one).mp h).1

theorem times_operation {R plus times ltR zero one : M}
    (h : IsField R plus times ltR zero one) : isOp2 R times :=
  ((isField_iff R plus times ltR zero one).mp h).2.1

theorem zero_mem {R plus times ltR zero one : M}
    (h : IsField R plus times ltR zero one) : memM zero R :=
  ((isField_iff R plus times ltR zero one).mp h).2.2.1

theorem one_mem {R plus times ltR zero one : M}
    (h : IsField R plus times ltR zero one) : memM one R :=
  ((isField_iff R plus times ltR zero one).mp h).2.2.2.1

/-- Completeness is for every internally coded nonempty bounded subset. -/
theorem internal_complete {R plus times ltR zero one : M}
    (h : IsField R plus times ltR zero one) : complete R ltR := by
  rcases (isField_iff R plus times ltR zero one).mp h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩
  exact hc

/-- The internal empty-code condition follows from actual nonemptiness;
no external full powerset is introduced. -/
theorem nonempty_complete {R plus times ltR zero one : M}
    (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (h : IsField R plus times ltR zero one) (S : M)
    (hS : memM S (powerM R)) (hne : ∃ x, memM x S)
    (hb : ∃ b, memM b R ∧ ∀ s, memM s S → le ltR s b) :
    ∃ u, memM u R ∧
      (∀ s, memM s S → le ltR s u) ∧
      ∀ v, memM v R → (∀ s, memM s S → le ltR s v) → le ltR u v := by
  have hnot : S ≠ emptyM := by
    rintro rfl
    obtain ⟨x, hx⟩ := hne
    exact empty_mem hZFC x hx
  exact internal_complete h S hS hnot hb

#print axioms isField_iff
#print axioms nonempty_complete

end ClassicismZFC.RealFieldLaws
