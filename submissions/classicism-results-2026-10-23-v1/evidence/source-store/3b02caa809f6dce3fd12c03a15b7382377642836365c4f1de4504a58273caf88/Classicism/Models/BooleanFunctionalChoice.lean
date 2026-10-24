import Classicism.Models.BooleanSupportedSelection
import Classicism.Models.BooleanProtectedCoverage
import Classicism.Models.BooleanAxiomTheory
import Classicism.Semantics.FullModels
import Classicism.Semantics.IntensionalFacts

/-!
# Actual Functional Choice sentences for covered relational outputs

Original formalization (misc), 23 October 2026, of section 6 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
An operation's application is expressed in the actual small first-order
syntax by equality of its complete output profile. The supported selecting
profile is an actual entity of the typed hierarchy. Its row equation proves
that the resulting Functional Choice sentence has Boolean value one,
including when the seriality antecedent has an intermediate Boolean value.

The protected-output corollary uses the concrete column coverage theorem.
No Choice verdict, semantic-agreement field, or model-existence hypothesis
is an input. Kernel verification is separate from this source construction.
-/

namespace Classicism.Meta.ChoiceBoolean.FunctionalChoice

open ChoiceFirstOrder ChoiceFirstOrder.MathlibBridge.AxiomTheory
open TypedHierarchy SmallFormulaSemantics BooleanAxiomTheory GroundChecks
open CategoryTheory

variable {K B : Type} [CompleteBooleanAlgebra B]
variable (a : BooleanAction K B) (E : Type)

noncomputable section

local instance language_relational : MathlibBridge.language.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

def relationType (σ : Ty) (ρ : RTy) : RTy := .arr σ (.arr (.rel ρ) .t)

/-- Equality of an output entity with an operation's slice, expressed only
with existing small-syntax profile atoms and a finite tuple quantifier. -/
def sliceGraph (σ : Ty) (ρ : RTy) {Γ : Ctx}
    (f : Var Γ (.rel (σ ⇒ ρ))) (x : Var Γ σ) (y : Var Γ (.rel ρ)) :
    SmallFormula Γ :=
  .all ρ (smallIff
    (.rel ρ (rightVar ρ.args y) (prefixArgs Γ ρ))
    (.rel (σ ⇒ ρ) (rightVar ρ.args f)
      (rightVar ρ.args x, prefixArgs Γ ρ)))

theorem smallImp_realize (S : ChoiceFirstOrder.Structure) {Γ : Ctx}
    (p q : SmallFormula Γ) (g : IEnv S.D Γ) :
    (smallImp p q).Realize S g ↔ (p.Realize S g → q.Realize S g) := by
  classical
  change (¬p.Realize S g ∨ q.Realize S g) ↔ _
  constructor
  · intro h hp
    exact h.elim (fun hn => False.elim (hn hp)) id
  · intro h
    by_cases hp : p.Realize S g
    · exact Or.inr (h hp)
    · exact Or.inl hp

theorem smallIff_realize (S : ChoiceFirstOrder.Structure) {Γ : Ctx}
    (p q : SmallFormula Γ) (g : IEnv S.D Γ) :
    (smallIff p q).Realize S g ↔ (p.Realize S g ↔ q.Realize S g) := by
  change ((smallImp p q).Realize S g ∧ (smallImp q p).Realize S g) ↔ _
  rw [smallImp_realize, smallImp_realize]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem allOne_realize (S : ChoiceFirstOrder.Structure) (σ : Ty) {Γ : Ctx}
    (φ : SmallFormula (σ :: Γ)) (g : IEnv S.D Γ) :
    (allOne σ φ).Realize S g ↔ ∀ x : S.D σ, φ.Realize S (.cons x g) := by
  change (∀ p : S.D σ × PUnit, φ.Realize S (.cons p.1 g)) ↔ _
  exact ⟨fun h x => h (x, PUnit.unit), fun h p => h p.1⟩

theorem exOne_realize (S : ChoiceFirstOrder.Structure) (σ : Ty) {Γ : Ctx}
    (φ : SmallFormula (σ :: Γ)) (g : IEnv S.D Γ) :
    (exOne σ φ).Realize S g ↔ ∃ x : S.D σ, φ.Realize S (.cons x g) := by
  change (∃ p : S.D σ × PUnit, φ.Realize S (.cons p.1 g)) ↔ _
  exact ⟨fun ⟨p, h⟩ => ⟨p.1, h⟩, fun ⟨x, h⟩ => ⟨(x, PUnit.unit), h⟩⟩

/-- The graph has its literal pointwise meaning in every ordinary typed
structure; this theorem needs no comprehension or model hypothesis. -/
theorem sliceGraph_realize (S : ChoiceFirstOrder.Structure) (σ : Ty) (ρ : RTy)
    {Γ : Ctx} (f : Var Γ (.rel (σ ⇒ ρ))) (x : Var Γ σ) (y : Var Γ (.rel ρ))
    (g : IEnv S.D Γ) :
    (sliceGraph σ ρ f x y).Realize S g ↔
      ∀ xs : Args S.D ρ, S.rel ρ (g.get y) xs ↔
        S.rel (σ ⇒ ρ) (g.get f) (g.get x, xs) := by
  change (∀ xs : Args S.D ρ, _) ↔ _
  apply forall_congr'
  intro xs
  rw [smallIff_realize]
  change (S.rel ρ ((appendEnv (argsEnv ρ xs) g).get (rightVar ρ.args y))
      (mapArgs (fun _ v => (appendEnv (argsEnv ρ xs) g).get v) ρ (prefixArgs Γ ρ)) ↔
    S.rel (σ ⇒ ρ) ((appendEnv (argsEnv ρ xs) g).get (rightVar ρ.args f))
      (((appendEnv (argsEnv ρ xs) g).get (rightVar ρ.args x)),
        mapArgs (fun _ v => (appendEnv (argsEnv ρ xs) g).get v) ρ (prefixArgs Γ ρ))) ↔ _
  rw [get_append_right, get_append_right, get_append_right, eval_prefixArgs] <;> rfl

/-- The same graph is equality to the denotation of actual object-language
application in the ordinary one-world premodel. -/
theorem sliceGraph_sem (S : ChoiceFirstOrder.Structure) (σ : Ty) (ρ : RTy)
    {Γ : Ctx} (f : Var Γ (.rel (σ ⇒ ρ))) (x : Var Γ σ) (y : Var Γ (.rel ρ))
    (g : IEnv S.D Γ) :
    (sliceGraph σ ρ f x y).Realize S g ↔
      S.model.Incl (.rel ρ) World.star (g.get y) =
        S.model.sem (𝟙 World.star) (.app (.var f) (.var x)) g := by
  rw [sliceGraph_realize]
  have hs : S.model.sem (𝟙 World.star) (.app (.var f) (.var x)) g =
      (S.model.incl (σ ⇒ ρ) World.star (g.get f)).app (inner S.D) (g.get x) :=
    S.model.apply_Incl _ _
  constructor
  · intro h
    apply intension_ext S
    intro xs
    rw [hs]
    exact h xs
  · intro h xs
    have hc := congrArg (fun Z : Intensional.Intension (inner S.D) ρ World.star =>
      (⟨World.star, xs, 𝟙 World.star⟩ : Intensional.Tuple (inner S.D) ρ World.star) ∈ Z) h
    rw [hs] at hc
    exact iff_of_eq hc

/-- At the single object and arrow, boxing preserves any sentence's truth. -/
theorem holdsSentence_box_iff (S : ChoiceFirstOrder.Structure) (hM : S.model.IsModel)
    (p : Sentence Signature.pure) :
    S.model.HoldsSentence (Term.box p) ↔ S.model.HoldsSentence p := by
  change S.model.Holds (𝟙 World.star) (Term.box p) .nil ↔ _
  rw [S.model.holds_box hM]
  constructor
  · intro h
    exact h (𝟙 World.star)
  · intro h V k
    cases V
    cases k
    exact h

theorem sliceGraph_value (σ : Ty) (ρ : RTy) {Γ : Ctx}
    (f : Var Γ (.rel (σ ⇒ ρ))) (x : Var Γ σ) (y : Var Γ (.rel ρ))
    (g : IEnv (Dom a E) Γ) :
    smallValue a E (sliceGraph σ ρ f x y) g =
      (DomSpace a E (.rel ρ)).space.eqv (g.get y)
        (app a E σ ρ (g.get f) (g.get x)) := by
  rw [profile_eqv]
  apply iInf_congr
  intro xs
  rw [value_iff, value_profile_prefix]
  change iffValue (profile a E ρ (g.get y) xs)
    (profile a E (σ ⇒ ρ)
      ((appendEnv (argsEnv ρ xs) g).get (rightVar ρ.args f))
      (((appendEnv (argsEnv ρ xs) g).get (rightVar ρ.args x)),
        mapArgs (fun _ v => (appendEnv (argsEnv ρ xs) g).get v) ρ (prefixArgs Γ ρ))) = _
  rw [get_append_right, get_append_right, eval_prefixArgs, app_profile] <;> rfl

/-- Eliminate only the final nullary-tuple component of the binary relation. -/
def binaryRelation (σ : Ty) (ρ : RTy) (U : Dom a E (.rel (relationType σ ρ))) :
    SupportedPredicate (ActionSpace.product (DomSpace a E σ) (DomSpace a E (.rel ρ))) := by
  let f : Predicate (prod (DomSpace a E σ).space (DomSpace a E (.rel ρ)).space) :=
    { toFun p := Predicate.toFun (X := (TupleSpace a E (relationType σ ρ)).space)
            U.val (p.1, (p.2, PUnit.unit))
      coherent := by
        intro p q
        have h := Predicate.coherent (X := (TupleSpace a E (relationType σ ρ)).space)
          U.val (p.1, (p.2, PUnit.unit)) (q.1, (q.2, PUnit.unit))
        change (((DomSpace a E σ).space.eqv p.1 q.1 ⊓
          ((DomSpace a E (.rel ρ)).space.eqv p.2 q.2 ⊓
            (TupleSpace a E .t).space.eqv PUnit.unit PUnit.unit)) ⊓
          Predicate.toFun (X := (TupleSpace a E (relationType σ ρ)).space)
            U.val (p.1, (p.2, PUnit.unit))) ≤ Predicate.toFun (X := (TupleSpace a E (relationType σ ρ)).space)
            U.val (q.1, (q.2, PUnit.unit)) at h
        have hunit : (TupleSpace a E .t).space.eqv PUnit.unit PUnit.unit = (⊤ : B) :=
          (TupleSpace a E .t).space.refl PUnit.unit
        have hrow : (DomSpace a E (.rel ρ)).space.eqv p.2 q.2 ⊓
            (TupleSpace a E .t).space.eqv PUnit.unit PUnit.unit =
            (DomSpace a E (.rel ρ)).space.eqv p.2 q.2 :=
          (congrArg (fun b : B => (DomSpace a E (.rel ρ)).space.eqv p.2 q.2 ⊓ b)
            hunit).trans (inf_top_eq _)
        have he := congrArg
          (fun b : B => ((DomSpace a E σ).space.eqv p.1 q.1 ⊓ b) ⊓
            Predicate.toFun (X := (TupleSpace a E (relationType σ ρ)).space)
              U.val (p.1, (p.2, PUnit.unit))) hrow
        exact he ▸ h }
  refine ⟨f, ?_⟩
  obtain ⟨S, hS, hU⟩ := U.property
  refine ⟨S, hS, ?_⟩
  intro π hπ
  apply Predicate.ext
  intro p
  change Dom a E σ × Dom a E (.rel ρ) at p
  have h := congrArg
    (fun F : Predicate (TupleSpace a E (relationType σ ρ)).space =>
      F (p.1, (p.2, PUnit.unit))) (hU π hπ)
  change a.map π (Predicate.toFun (X := (TupleSpace a E (relationType σ ρ)).space)
      U.val ((DomSpace a E σ).action.act π⁻¹ p.1,
        ((DomSpace a E (.rel ρ)).action.act π⁻¹ p.2, PUnit.unit))) =
    Predicate.toFun (X := (TupleSpace a E (relationType σ ρ)).space)
      U.val (p.1, (p.2, PUnit.unit)) at h
  change a.map π (Predicate.toFun (X := (TupleSpace a E (relationType σ ρ)).space)
      U.val ((DomSpace a E σ).action.act π⁻¹ p.1,
        ((DomSpace a E (.rel ρ)).action.act π⁻¹ p.2, PUnit.unit))) =
    Predicate.toFun (X := (TupleSpace a E (relationType σ ρ)).space)
      U.val (p.1, (p.2, PUnit.unit))
  exact h

@[simp] theorem binaryRelation_apply (σ : Ty) (ρ : RTy)
    (U : Dom a E (.rel (relationType σ ρ))) (x : Dom a E σ) (y : Dom a E (.rel ρ)) :
    Predicate.toFun
      (X := (ActionSpace.product (DomSpace a E σ) (DomSpace a E (.rel ρ))).space)
      (binaryRelation a E σ ρ U).val (x, y) = profile a E (relationType σ ρ) U
      (x, (y, PUnit.unit)) := rfl

variable {G : Type} [LinearOrder G]

def selectingOperation (σ : Ty) (ρ : RTy)
    (c : GroundMap (DomSpace a E (.rel ρ)) G)
    (U : Dom a E (.rel (relationType σ ρ))) (g₀ : G) : Dom a E (.rel (σ ⇒ ρ)) :=
  SupportedSelection.selector c (binaryRelation a E σ ρ U) g₀

theorem selectingOperation_row [WellFoundedLT G] (σ : Ty) (ρ : RTy)
    (c : GroundMap (DomSpace a E (.rel ρ)) G) (hc : Covers c)
    (U : Dom a E (.rel (relationType σ ρ))) (g₀ : G) (x : Dom a E σ) :
    profile a E (relationType σ ρ) U
      (x, (app a E σ ρ (selectingOperation a E σ ρ c U g₀) x, PUnit.unit)) =
      ⨆ y : Dom a E (.rel ρ), profile a E (relationType σ ρ) U (x, (y, PUnit.unit)) := by
  have h := SupportedSelection.row_equation c (binaryRelation a E σ ρ U) hc g₀ x
    (dom_finitelySupported a E σ x)
  change profile a E (relationType σ ρ) U
      (x, (app a E σ ρ (selectingOperation a E σ ρ c U g₀) x, PUnit.unit)) =
    ⨆ y : Dom a E (.rel ρ), profile a E (relationType σ ρ) U (x, (y, PUnit.unit)) at h
  exact h

/-- The actual seriality formula in context [U]. -/
def serialSmall (σ : Ty) (ρ : RTy) : SmallFormula [.rel (relationType σ ρ)] :=
  allOne σ (exOne (.rel ρ)
    (.rel (relationType σ ρ) (.succ (.succ .zero))
      (.succ .zero, (.zero, PUnit.unit))))

/-- The selecting formula in context [F,U]. Application is expressed by
its entire relational profile; no new function symbol is introduced. -/
def selectingSmall (σ : Ty) (ρ : RTy) :
    SmallFormula [.rel (σ ⇒ ρ), .rel (relationType σ ρ)] :=
  allOne σ (exOne (.rel ρ) (.conj
    (sliceGraph σ ρ (.succ (.succ .zero)) (.succ .zero) .zero)
    (.rel (relationType σ ρ) (.succ (.succ (.succ .zero)))
      (.succ .zero, (.zero, PUnit.unit)))))

def small (σ : Ty) (ρ : RTy) : SmallFormula [] :=
  allOne (.rel (relationType σ ρ))
    (smallImp (serialSmall σ ρ) (exOne (.rel (σ ⇒ ρ)) (selectingSmall σ ρ)))

/-- An ordinary semantic description, used only to verify the exact small
and quoted formulations below. This is a definition, not a verdict input. -/
def Ordinary (S : ChoiceFirstOrder.Structure) (σ : Ty) (ρ : RTy) : Prop :=
  ∀ U : S.D (.rel (relationType σ ρ)),
    (∀ x : S.D σ, ∃ y : S.D (.rel ρ), S.rel (relationType σ ρ) U (x, (y, PUnit.unit))) →
    ∃ F : S.D (.rel (σ ⇒ ρ)), ∀ x : S.D σ, ∃ y : S.D (.rel ρ),
      (∀ xs : Args S.D ρ, S.rel ρ y xs ↔ S.rel (σ ⇒ ρ) F (x, xs)) ∧
        S.rel (relationType σ ρ) U (x, (y, PUnit.unit))

theorem serialSmall_realize (S : ChoiceFirstOrder.Structure) (σ : Ty) (ρ : RTy)
    (U : S.D (.rel (relationType σ ρ))) :
    (serialSmall σ ρ).Realize S (.cons U .nil) ↔
      ∀ x : S.D σ, ∃ y : S.D (.rel ρ), S.rel (relationType σ ρ) U (x, (y, PUnit.unit)) := by
  rw [serialSmall, allOne_realize]
  apply forall_congr'
  intro x
  rw [exOne_realize] <;> rfl

theorem selectingSmall_realize (S : ChoiceFirstOrder.Structure) (σ : Ty) (ρ : RTy)
    (F : S.D (.rel (σ ⇒ ρ))) (U : S.D (.rel (relationType σ ρ))) :
    (selectingSmall σ ρ).Realize S (.cons F (.cons U .nil)) ↔
      ∀ x : S.D σ, ∃ y : S.D (.rel ρ),
        (∀ xs : Args S.D ρ, S.rel ρ y xs ↔ S.rel (σ ⇒ ρ) F (x, xs)) ∧
          S.rel (relationType σ ρ) U (x, (y, PUnit.unit)) := by
  rw [selectingSmall, allOne_realize]
  apply forall_congr'
  intro x
  rw [exOne_realize]
  apply exists_congr
  intro y
  exact and_congr
    (sliceGraph_realize S σ ρ (.succ (.succ .zero)) (.succ .zero) .zero
      (.cons y (.cons x (.cons F (.cons U .nil))))) Iff.rfl

theorem small_realize (S : ChoiceFirstOrder.Structure) (σ : Ty) (ρ : RTy) :
    (small σ ρ).Realize S .nil ↔ Ordinary S σ ρ := by
  simp only [small, allOne_realize, smallImp_realize, serialSmall_realize,
    exOne_realize, selectingSmall_realize, Ordinary]

private theorem holds_binary (S : ChoiceFirstOrder.Structure) (σ : Ty) (ρ : RTy)
    {Γ : Ctx} (u : Var Γ (.rel (relationType σ ρ))) (x : Var Γ σ)
    (y : Var Γ (.rel ρ)) (g : IEnv S.D Γ) :
    S.model.Holds (𝟙 World.star) (.app (.app (.var u) (.var x)) (.var y)) g ↔
      S.rel (relationType σ ρ) (g.get u) (g.get x, (g.get y, PUnit.unit)) :=
  Intensional.Premodel.holds_app_var2 (A := S.model) (𝟙 World.star) g u x y

private theorem holds_binary_operation (S : ChoiceFirstOrder.Structure)
    (hM : S.model.IsModel) (σ : Ty) (ρ : RTy) {Γ : Ctx}
    (u : Var Γ (.rel (relationType σ ρ))) (f : Var Γ (.rel (σ ⇒ ρ)))
    (x : Var Γ σ) (g : IEnv S.D Γ) :
    S.model.Holds (𝟙 World.star)
      (.app (.app (.var u) (.var x)) (.app (.var f) (.var x))) g ↔
      ∃ y : S.D (.rel ρ),
        (∀ xs : Args S.D ρ, S.rel ρ y xs ↔ S.rel (σ ⇒ ρ) (g.get f) (g.get x, xs)) ∧
          S.rel (relationType σ ρ) (g.get u) (g.get x, (y, PUnit.unit)) := by
  have hs (y : S.D (.rel ρ)) :
      (∀ xs : Args S.D ρ, S.rel ρ y xs ↔ S.rel (σ ⇒ ρ) (g.get f) (g.get x, xs)) ↔
      S.model.Incl (.rel ρ) World.star y =
        S.model.sem (𝟙 World.star) (.app (.var f) (.var x)) g := by
    exact (sliceGraph_realize S σ ρ (.succ f) (.succ x) .zero (.cons y g)).symm.trans
      (sliceGraph_sem S σ ρ (.succ f) (.succ x) .zero (.cons y g))
  have he (y : S.D (.rel ρ))
      (hy : S.model.Incl (.rel ρ) World.star y =
        S.model.sem (𝟙 World.star) (.app (.var f) (.var x)) g) :
      S.model.Holds (𝟙 World.star)
        (.app (.app (.var u) (.var x)) (.app (.var f) (.var x))) g ↔
        S.rel (relationType σ ρ) (g.get u) (g.get x, (y, PUnit.unit)) := by
    rw [S.model.holds_app (𝟙 World.star) g (.app (.var u) (.var x))
      (.app (.var f) (.var x)) hy]
    change (⟨World.star, (y, PUnit.unit), 𝟙 World.star⟩ :
        Intensional.Tuple S.model.inner (.arr (.rel ρ) .t) World.star) ∈
      S.model.apply (S.model.incl (relationType σ ρ) World.star (g.get u))
        (S.model.Incl σ World.star (g.get x)) ↔ _
    have hp := S.model.apply_Incl (σ := σ) (ρ := .arr (.rel ρ) .t)
      (S.model.incl (relationType σ ρ) World.star (g.get u)) (g.get x)
    exact Iff.of_eq (congrArg
      (fun F : Intensional.Intension S.model.inner (.arr (.rel ρ) .t) World.star =>
        F ⟨World.star, (y, PUnit.unit), 𝟙 World.star⟩) hp)
  constructor
  · intro h
    obtain ⟨y, hy⟩ := hM (𝟙 World.star) (.app (.var f) (.var x)) g
    exact ⟨y, (hs y).mpr hy, (he y hy).mp h⟩
  · rintro ⟨y, hy, hU⟩
    exact (he y ((hs y).mp hy)).mpr hU

/-- The literal generated original FC quotation has the same ordinary
meaning; no strengthened selector scheme is substituted for it. -/
theorem quoted_realize (S : ChoiceFirstOrder.Structure) (hM : S.model.IsModel)
    (σ : Ty) (ρ : RTy) :
    S.model.HoldsSentence (P.FunctionalChoice.quoted σ ρ) ↔ Ordinary S σ ρ := by
  simp only [P.FunctionalChoice.quoted, Intensional.Premodel.HoldsSentence,
    S.model.holds_forall hM, S.model.holds_exists hM, S.model.holds_imp hM]
  apply forall_congr'
  intro U
  apply imp_congr
  · apply forall_congr'
    intro x
    apply exists_congr
    intro y
    exact holds_binary S σ ρ (.succ (.succ .zero)) (.succ .zero) .zero
      (.cons y (.cons x (.cons U .nil)))
  · apply exists_congr
    intro F
    apply forall_congr'
    intro x
    exact holds_binary_operation S hM σ ρ (.succ (.succ .zero)) (.succ .zero) .zero
      (.cons x (.cons F (.cons U .nil)))

theorem small_realize_iff_quoted (S : ChoiceFirstOrder.Structure) (hM : S.model.IsModel)
    (σ : Ty) (ρ : RTy) :
    (small σ ρ).Realize S .nil ↔ S.model.HoldsSentence (P.FunctionalChoice.quoted σ ρ) :=
  (small_realize S σ ρ).trans (quoted_realize S hM σ ρ).symm

theorem small_realize_iff_boxed (S : ChoiceFirstOrder.Structure) (hM : S.model.IsModel)
    (σ : Ty) (ρ : RTy) :
    (small σ ρ).Realize S .nil ↔ S.model.HoldsSentence (P.NecFunctionalChoice.quoted σ ρ) := by
  change (small σ ρ).Realize S .nil ↔ S.model.HoldsSentence (Term.box (P.FunctionalChoice.quoted σ ρ))
  exact (small_realize_iff_quoted S hM σ ρ).trans
    (holdsSentence_box_iff S hM (P.FunctionalChoice.quoted σ ρ)).symm

theorem serialSmall_value (σ : Ty) (ρ : RTy)
    (U : Dom a E (.rel (relationType σ ρ))) :
    smallValue a E (serialSmall σ ρ) (.cons U .nil) =
      ⨅ x : Dom a E σ, ⨆ y : Dom a E (.rel ρ),
        profile a E (relationType σ ρ) U (x, (y, PUnit.unit)) := by
  rw [serialSmall, value_allOne]
  apply iInf_congr
  intro x
  rw [value_exOne] <;> rfl

private theorem iSup_outputGraph (σ : Ty) (ρ : RTy)
    (U : Dom a E (.rel (relationType σ ρ))) (x : Dom a E σ)
    (z : Dom a E (.rel ρ)) :
    (⨆ y : Dom a E (.rel ρ), (DomSpace a E (.rel ρ)).space.eqv y z ⊓
      profile a E (relationType σ ρ) U (x, (y, PUnit.unit))) =
      profile a E (relationType σ ρ) U (x, (z, PUnit.unit)) := by
  apply le_antisymm
  · apply iSup_le
    intro y
    have h := Predicate.coherent
      (X := prod (DomSpace a E σ).space (DomSpace a E (.rel ρ)).space)
      (binaryRelation a E σ ρ U).val (x, y) (x, z)
    change ((DomSpace a E σ).space.eqv x x ⊓
        (DomSpace a E (.rel ρ)).space.eqv y z) ⊓
      profile a E (relationType σ ρ) U (x, (y, PUnit.unit)) ≤
        profile a E (relationType σ ρ) U (x, (z, PUnit.unit)) at h
    simpa only [(DomSpace a E σ).space.refl, top_inf_eq] using h
  · apply le_iSup_of_le z
    rw [(DomSpace a E (.rel ρ)).space.refl, top_inf_eq]

theorem selectingSmall_value (σ : Ty) (ρ : RTy)
    (F : Dom a E (.rel (σ ⇒ ρ))) (U : Dom a E (.rel (relationType σ ρ))) :
    smallValue a E (selectingSmall σ ρ) (.cons F (.cons U .nil)) =
      ⨅ x : Dom a E σ, profile a E (relationType σ ρ) U
        (x, (app a E σ ρ F x, PUnit.unit)) := by
  rw [selectingSmall, value_allOne]
  apply iInf_congr
  intro x
  rw [value_exOne]
  calc
    _ = ⨆ y : Dom a E (.rel ρ), (DomSpace a E (.rel ρ)).space.eqv y (app a E σ ρ F x) ⊓
        profile a E (relationType σ ρ) U (x, (y, PUnit.unit)) := by
      apply iSup_congr
      intro y
      change smallValue a E (sliceGraph σ ρ (.succ (.succ .zero)) (.succ .zero) .zero)
        (.cons y (.cons x (.cons F (.cons U .nil)))) ⊓ _ = _
      rw [sliceGraph_value] <;> rfl
    _ = _ := iSup_outputGraph a E σ ρ U x (app a E σ ρ F x)

/-- The actual small Functional Choice sentence has value one. Its
antecedent is allowed to have any Boolean value. -/
theorem value_one [WellFoundedLT G] (σ : Ty) (ρ : RTy)
    (c : GroundMap (DomSpace a E (.rel ρ)) G) (hc : Covers c) (g₀ : G) :
    smallValue a E (small σ ρ) .nil = ⊤ := by
  rw [small, value_allOne]
  apply top_le_iff.mp
  apply le_iInf
  intro U
  rw [value_imp]
  apply le_himp_iff.mpr
  rw [top_inf_eq, value_exOne]
  apply le_iSup_of_le (selectingOperation a E σ ρ c U g₀)
  rw [serialSmall_value, selectingSmall_value]
  apply le_of_eq
  apply iInf_congr
  intro x
  exact (selectingOperation_row a E σ ρ c hc U g₀ x).symm

/-- The same result is an actual sentence value for the tagged Mathlib
language consumed by countable model extraction. -/
theorem sentence_value_one [WellFoundedLT G] (hE : Nonempty E) (σ : Ty) (ρ : RTy)
    (c : GroundMap (DomSpace a E (.rel ρ)) G) (hc : Covers c) (g₀ : G) :
    FirstOrderSemantics.sentenceValue (TaggedFirstOrder.booleanStructure a E hE)
      (MathlibBridge.translate (small σ ρ)) = ⊤ := by
  rw [TaggedFirstOrder.sentence_value]
  exact value_one a E σ ρ c hc g₀

/-- Concrete protected outputs supply the required coverage. The ground
output carrier is well-ordered in the external metatheory, not internally. -/
theorem protected_value_one (κ : Cardinal) (hκ : κ.IsRegular) (σ : Ty) (ρ : RTy)
    (hρ : ProtectedCoverage.Protected κ E (.rel ρ)) :
    smallValue (ColumnAlgebra.action κ) E (small σ ρ) .nil = ⊤ := by
  let G := ChoiceFirstOrder.Full.Dom E (.rel ρ)
  obtain ⟨ord, hWF⟩ := exists_wellFoundedLT G
  exact @value_one _ _ _ (ColumnAlgebra.action κ) E G ord hWF σ ρ
    (domMap (ColumnAlgebra.action κ) E (.rel ρ))
    (ProtectedCoverage.dom_covers κ E hκ (.rel ρ) hρ)
    (∅ : Set (ChoiceFirstOrder.Full.Tuple E ρ))

end

end Classicism.Meta.ChoiceBoolean.FunctionalChoice
