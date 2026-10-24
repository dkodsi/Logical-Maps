import Classicism.Models.BooleanSelectorObstruction
import Classicism.Models.BooleanFunctionalChoice
import Classicism.Results.ChoiceHierarchySchemas
import Classicism.Semantics.FullModels

/-!
# The actual selector sentence at the supported higher type

Original formalization (misc), 23 October 2026, of section 8 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
The finite-support obstruction is connected to an explicit small-language
selector sentence. Unary typed predicates have a final PUnit argument;
padding and restricting actual supported profiles removes precisely that
argument before applying the previously proved obstruction. No quotation
agreement, Choice verdict, or model-existence certificate is assumed.

The ordinary interpretation theorem identifies the explicit sentence with
the project's quoted Selector in every recovered one-world structure with
small comprehension. Kernel verification is separate from this source.
-/

namespace Classicism.Meta.ChoiceBoolean.SelectorFailure

open ChoiceFirstOrder ChoiceFirstOrder.MathlibBridge.AxiomTheory
open TypedHierarchy SmallFormulaSemantics BooleanAxiomTheory
open TypedTermSemantics FunctionalChoice

noncomputable section

local instance language_relational : MathlibBridge.language.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

variable {K B : Type} [CompleteBooleanAlgebra B]
variable {a : BooleanAction K B}

/-- Pullback constructs an actual supported predicate and preserves its
support, since the argument map is equivariant. -/
def predicatePullback {X Y : ActionSpace a} (f : Map X Y) :
    Map (supportedPredicateSpace Y) (supportedPredicateSpace X) where
  toFun P :=
    ⟨{ toFun x := Predicate.toFun (X := Y.space) P.val (f x)
       coherent x y :=
         (inf_le_inf_right _ (f.congr x y)).trans (Predicate.coherent (X := Y.space) P.val (f x) (f y)) }, by
      obtain ⟨S, hS, hP⟩ := P.property
      refine ⟨S, hS, ?_⟩
      intro π hπ
      apply Predicate.ext
      intro x
      change a.map π (Predicate.toFun (X := Y.space) P.val (f (X.action.act π⁻¹ x))) = Predicate.toFun (X := Y.space) P.val (f x)
      rw [f.equivariant]
      exact congrArg (fun Q : Predicate Y.space => Q (f x)) (hP π hπ)⟩
  congr P Q := by
    apply le_iInf
    intro x
    exact iInf_le _ (f x)
  equivariant π P := by
    apply Subtype.ext
    apply Predicate.ext
    intro x
    change a.map π (Predicate.toFun (X := Y.space) P.val (Y.action.act π⁻¹ (f x))) =
      a.map π (Predicate.toFun (X := Y.space) P.val (f (X.action.act π⁻¹ x)))
    rw [f.equivariant]

/-- Add the trailing nullary tuple required by the project's unary type. -/
def pad (Y : ActionSpace a) :
    Map (supportedPredicateSpace Y)
      (supportedPredicateSpace (ActionSpace.product Y (ActionSpace.crisp a PUnit))) :=
  predicatePullback (Map.fst Y (ActionSpace.crisp a PUnit))

@[simp] theorem pad_apply (Y : ActionSpace a) (P : SupportedPredicate Y)
    (y : Y.space.Carrier) (u : PUnit) :
    Predicate.toFun (X := (ActionSpace.product Y (ActionSpace.crisp a PUnit)).space)
      (pad Y P).val (y, u) = Predicate.toFun (X := Y.space) P.val y := rfl

def predicateType (ρ : RTy) : RTy := .arr (.rel ρ) .t
def operationType (ρ : RTy) : RTy := .arr (.rel (predicateType ρ)) ρ

/-- An operation's selecting clause, in the context [predicate, operation]. -/
def selectingBody (ρ : RTy) :
    SmallFormula [.rel (predicateType ρ), .rel (operationType ρ)] :=
  smallImp
    (exOne (.rel ρ) (.rel (predicateType ρ) (.succ .zero) (.zero, PUnit.unit)))
    (exOne (.rel ρ) (.conj
      (sliceGraph (.rel (predicateType ρ)) ρ (.succ (.succ .zero)) (.succ .zero) .zero)
      (.rel (predicateType ρ) (.succ .zero) (.zero, PUnit.unit))))

/-- The actual finite-syntax selector sentence. Application is represented
by equality of complete relational profiles, using the existing graph code. -/
def small (ρ : RTy) : SmallFormula [] :=
  exOne (.rel (operationType ρ))
    (allOne (.rel (predicateType ρ)) (selectingBody ρ))

variable (a) (E : Type)

private theorem outputGraph_value (ρ : RTy)
    (P : Dom a E (.rel (predicateType ρ))) (z : Dom a E (.rel ρ)) :
    (⨆ y : Dom a E (.rel ρ), (DomSpace a E (.rel ρ)).space.eqv y z ⊓
      profile a E (predicateType ρ) P (y, PUnit.unit)) =
      profile a E (predicateType ρ) P (z, PUnit.unit) := by
  apply le_antisymm
  · apply iSup_le
    intro y
    have h := Predicate.coherent (X := (TupleSpace a E (predicateType ρ)).space)
      P.val (y, PUnit.unit) (z, PUnit.unit)
    change (((DomSpace a E (.rel ρ)).space.eqv y z ⊓
      (TupleSpace a E .t).space.eqv PUnit.unit PUnit.unit) ⊓
      Predicate.toFun (X := (TupleSpace a E (predicateType ρ)).space)
        P.val (y, PUnit.unit)) ≤
      Predicate.toFun (X := (TupleSpace a E (predicateType ρ)).space)
        P.val (z, PUnit.unit) at h
    have hunit : (TupleSpace a E .t).space.eqv PUnit.unit PUnit.unit = (⊤ : B) :=
      (TupleSpace a E .t).space.refl PUnit.unit
    have hrow : (DomSpace a E (.rel ρ)).space.eqv y z ⊓
        (TupleSpace a E .t).space.eqv PUnit.unit PUnit.unit =
        (DomSpace a E (.rel ρ)).space.eqv y z :=
      (congrArg (fun b : B => (DomSpace a E (.rel ρ)).space.eqv y z ⊓ b)
        hunit).trans (inf_top_eq _)
    have he := congrArg
      (fun b : B => b ⊓ Predicate.toFun
        (X := (TupleSpace a E (predicateType ρ)).space) P.val (y, PUnit.unit)) hrow
    exact he ▸ h
  · apply le_iSup_of_le z
    rw [(DomSpace a E (.rel ρ)).space.refl, top_inf_eq]

theorem selectingBody_value (ρ : RTy)
    (F : Dom a E (.rel (operationType ρ))) (P : Dom a E (.rel (predicateType ρ))) :
    smallValue a E (selectingBody ρ) (.cons P (.cons F .nil)) =
      (⨆ y : Dom a E (.rel ρ), profile a E (predicateType ρ) P (y, PUnit.unit)) ⇨
        profile a E (predicateType ρ) P
          (app a E (.rel (predicateType ρ)) ρ F P, PUnit.unit) := by
  rw [selectingBody, value_imp, value_exOne, value_exOne]
  congr 1
  calc
    _ = ⨆ y : Dom a E (.rel ρ), (DomSpace a E (.rel ρ)).space.eqv y
        (app a E (.rel (predicateType ρ)) ρ F P) ⊓
        profile a E (predicateType ρ) P (y, PUnit.unit) := by
      apply iSup_congr
      intro y
      change smallValue a E
        (sliceGraph (.rel (predicateType ρ)) ρ (.succ (.succ .zero)) (.succ .zero) .zero)
        (.cons y (.cons P (.cons F .nil))) ⊓ _ = _
      rw [sliceGraph_value] <;> rfl
    _ = _ := outputGraph_value a E ρ P _

theorem small_value (ρ : RTy) :
    smallValue a E (small ρ) .nil =
      ⨆ F : Dom a E (.rel (operationType ρ)),
        ⨅ P : Dom a E (.rel (predicateType ρ)),
          (⨆ y : Dom a E (.rel ρ), profile a E (predicateType ρ) P (y, PUnit.unit)) ⇨
            profile a E (predicateType ρ) P
              (app a E (.rel (predicateType ρ)) ρ F P, PUnit.unit) := by
  rw [small, value_exOne]
  apply iSup_congr
  intro F
  rw [value_allOne]
  apply iInf_congr
  intro P
  exact selectingBody_value a E ρ F P

/-- Restrict an actual typed operation to padded predicates. This is an
actual admitted profile, not an assumed closure operation. -/
def restrictOperation (ρ : RTy) (F : Dom a E (.rel (operationType ρ))) :
    SupportedPredicate
      (ActionSpace.product (supportedPredicateSpace (DomSpace a E (.rel ρ)))
        (TupleSpace a E ρ)) :=
  predicatePullback
    (Map.pair
      (Map.comp (pad (DomSpace a E (.rel ρ)))
        (Map.fst (supportedPredicateSpace (DomSpace a E (.rel ρ))) (TupleSpace a E ρ)))
      (Map.snd (supportedPredicateSpace (DomSpace a E (.rel ρ))) (TupleSpace a E ρ))) F

variable {κ : Cardinal}

theorem restrictOperation_selected (ρ : RTy) (F : Dom (ColumnAlgebra.action κ) E (.rel (operationType ρ)))
    (P : SupportedPredicate (DomSpace (ColumnAlgebra.action κ) E (.rel ρ))) :
    SelectorObstruction.selected (restrictOperation (ColumnAlgebra.action κ) E ρ F) P =
      app (ColumnAlgebra.action κ) E (.rel (predicateType ρ)) ρ F (pad (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)) P) := by
  apply Subtype.ext
  apply Predicate.ext
  intro xs
  change Predicate.toFun
      (X := (TupleSpace (ColumnAlgebra.action κ) E (operationType ρ)).space)
      F.val (pad (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)) P, xs) =
    Predicate.toFun
      (X := (TupleSpace (ColumnAlgebra.action κ) E (operationType ρ)).space)
      F.val (pad (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)) P, xs)
  rfl

theorem selecting_value_le (ρ : RTy) (F : Dom (ColumnAlgebra.action κ) E (.rel (operationType ρ))) :
    (⨅ P : Dom (ColumnAlgebra.action κ) E (.rel (predicateType ρ)),
      (⨆ y : Dom (ColumnAlgebra.action κ) E (.rel ρ), profile (ColumnAlgebra.action κ) E (predicateType ρ) P (y, PUnit.unit)) ⇨
        profile (ColumnAlgebra.action κ) E (predicateType ρ) P
          (app (ColumnAlgebra.action κ) E (.rel (predicateType ρ)) ρ F P, PUnit.unit)) ≤
      SelectorObstruction.selectorValue (restrictOperation (ColumnAlgebra.action κ) E ρ F) := by
  apply le_iInf
  intro P
  have h := iInf_le
    (fun Q : Dom (ColumnAlgebra.action κ) E (.rel (predicateType ρ)) =>
      (⨆ y : Dom (ColumnAlgebra.action κ) E (.rel ρ), profile (ColumnAlgebra.action κ) E (predicateType ρ) Q (y, PUnit.unit)) ⇨
        profile (ColumnAlgebra.action κ) E (predicateType ρ) Q
          (app (ColumnAlgebra.action κ) E (.rel (predicateType ρ)) ρ F Q, PUnit.unit))
    (pad (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)) P)
  rw [restrictOperation_selected]
  change _ ≤
    (⨆ y : Dom (ColumnAlgebra.action κ) E (.rel ρ),
      Predicate.toFun (X := (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)).space)
        P.val y) ⇨
      Predicate.toFun (X := (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)).space)
        P.val (app (ColumnAlgebra.action κ) E (.rel (predicateType ρ)) ρ F
          (pad (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)) P)) at h
  exact h


/-- The support obstruction is the value of the explicit object-language
selector sentence at precisely the displayed relational output type. -/
theorem small_value_zero (ρ : RTy)
    (C : SelectorObstruction.ColumnFamily (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)))
    (hκ : Cardinal.aleph0 ≤ κ) :
    smallValue (ColumnAlgebra.action κ) E (small ρ) .nil = ⊥ := by
  rw [small_value]
  apply bot_unique
  apply iSup_le
  intro F
  exact (selecting_value_le E ρ F).trans
    (le_of_eq (SelectorObstruction.selectorValue_zero C hκ
      (restrictOperation (ColumnAlgebra.action κ) E ρ F)))

theorem neg_small_value_one (ρ : RTy)
    (C : SelectorObstruction.ColumnFamily (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)))
    (hκ : Cardinal.aleph0 ≤ κ) :
    smallValue (ColumnAlgebra.action κ) E (.neg (small ρ)) .nil = ⊤ := by
  change (smallValue (ColumnAlgebra.action κ) E (small ρ) .nil)ᶜ = ⊤
  rw [small_value_zero E ρ C hκ, compl_bot]

theorem sentence_value_zero (hE : Nonempty E) (ρ : RTy)
    (C : SelectorObstruction.ColumnFamily (DomSpace (ColumnAlgebra.action κ) E (.rel ρ)))
    (hκ : Cardinal.aleph0 ≤ κ) :
    FirstOrderSemantics.sentenceValue
      (TaggedFirstOrder.booleanStructure (ColumnAlgebra.action κ) E hE)
      (MathlibBridge.translate (small ρ)) = ⊥ := by
  rw [TaggedFirstOrder.sentence_value]
  exact small_value_zero E ρ C hκ

/-- The small sentence has its literal ordinary first-order meaning;
no semantic closure hypothesis is needed for this expansion. -/
theorem small_realize (S : ChoiceFirstOrder.Structure) (ρ : RTy) :
    (small ρ).Realize S .nil ↔
      ∃ F : S.D (.rel (operationType ρ)),
        ∀ P : S.D (.rel (predicateType ρ)),
          (∃ y : S.D (.rel ρ), S.rel (predicateType ρ) P (y, PUnit.unit)) →
          ∃ y : S.D (.rel ρ),
            (∀ xs : Args S.D ρ, S.rel ρ y xs ↔
              S.rel (operationType ρ) F (P, xs)) ∧
            S.rel (predicateType ρ) P (y, PUnit.unit) := by
  rw [small, exOne_realize]
  apply exists_congr
  intro F
  rw [allOne_realize]
  apply forall_congr'
  intro P
  rw [selectingBody, smallImp_realize, exOne_realize, exOne_realize]
  apply imp_congr Iff.rfl
  apply exists_congr
  intro y
  change ((sliceGraph (.rel (predicateType ρ)) ρ (.succ (.succ .zero)) (.succ .zero) .zero).Realize S
    (.cons y (.cons P (.cons F .nil))) ∧ _) ↔ _
  rw [sliceGraph_realize] <;> rfl

open CategoryTheory

/-- An actual application in the one-world premodel is the relational
slice, whose admitted witness follows from small comprehension. -/
theorem holds_selector_application (S : ChoiceFirstOrder.Structure)
    (hC : SmallComprehension S) (ρ : RTy)
    (F : S.D (.rel (operationType ρ))) (P : S.D (.rel (predicateType ρ))) :
    S.model.Holds (𝟙 World.star)
      (.app (.var .zero) (.app (.var (.succ .zero)) (.var .zero)))
      (.cons P (.cons F .nil)) ↔
      ∃ y : S.D (.rel ρ),
        (∀ xs : Args S.D ρ, S.rel ρ y xs ↔ S.rel (operationType ρ) F (P, xs)) ∧
        S.rel (predicateType ρ) P (y, PUnit.unit) := by
  let g : IEnv S.D [.rel (predicateType ρ), .rel (operationType ρ)] :=
    .cons P (.cons F .nil)
  let t : Term Signature.pure [.rel (predicateType ρ), .rel (operationType ρ)] (.rel ρ) :=
    .app (.var (.succ .zero)) (.var .zero)
  obtain ⟨y, hy⟩ := isModel_of_small_comprehension S hC (𝟙 World.star) t g
  have hs : ∀ xs : Args S.D ρ,
      S.rel ρ y xs ↔ S.rel (operationType ρ) F (P, xs) := by
    exact (sliceGraph_realize S (.rel (predicateType ρ)) ρ
      (.succ (.succ .zero)) (.succ .zero) .zero (.cons y g)).mp
        ((sliceGraph_sem S (.rel (predicateType ρ)) ρ
          (.succ (.succ .zero)) (.succ .zero) .zero (.cons y g)).mpr hy)
  have ht : S.model.Holds (𝟙 World.star) (.app (.var .zero) t) g ↔
      S.rel (predicateType ρ) P (y, PUnit.unit) := by
    exact S.model.holds_app (σ := .rel ρ) (𝟙 World.star) g (.var .zero) t hy
  change S.model.Holds (𝟙 World.star) (.app (.var .zero) t) g ↔ _
  rw [ht]
  constructor
  · intro hP
    exact ⟨y, hs, hP⟩
  · rintro ⟨z, hz, hP⟩
    have he : z = y := S.rel_injective ρ (funext fun xs =>
      propext ((hz xs).trans (hs xs).symm))
    exact he ▸ hP

/-- The explicit small sentence is equivalent to the project's actual
quoted Selector. The only premise is the first-order comprehension scheme
already supplied by the extraction theory. -/
theorem small_realize_iff_quoted (S : ChoiceFirstOrder.Structure)
    (hC : SmallComprehension S) (ρ : RTy) :
    (small ρ).Realize S .nil ↔
      S.model.HoldsSentence (Classicism.ChoiceHierarchy.Selector.quoted ρ) := by
  rw [small_realize]
  have M : S.model.IsModel := isModel_of_small_comprehension S hC
  simp only [Intensional.Premodel.HoldsSentence, Classicism.ChoiceHierarchy.Selector.quoted,
    S.model.holds_exists M, S.model.holds_forall M, S.model.holds_imp M,
    Intensional.Premodel.holds_app_var1]
  apply exists_congr
  intro F
  apply forall_congr'
  intro P
  apply imp_congr Iff.rfl
  exact (holds_selector_application S hC ρ F P).symm

/-- In this one-world interpretation, the closed box adds no condition. -/
theorem holds_box_iff (S : ChoiceFirstOrder.Structure) (hC : SmallComprehension S)
    (p : Sentence Signature.pure) :
    S.model.HoldsSentence (Term.box p) ↔ S.model.HoldsSentence p :=
  FunctionalChoice.holdsSentence_box_iff S (isModel_of_small_comprehension S hC) p

theorem small_realize_iff_necQuoted (S : ChoiceFirstOrder.Structure)
    (hC : SmallComprehension S) (ρ : RTy) :
    (small ρ).Realize S .nil ↔
      S.model.HoldsSentence (Classicism.ChoiceHierarchy.NecSelector.quoted ρ) := by
  change (small ρ).Realize S .nil ↔
    S.model.HoldsSentence (Term.box (Classicism.ChoiceHierarchy.Selector.quoted ρ))
  exact (small_realize_iff_quoted S hC ρ).trans
    (holds_box_iff S hC (Classicism.ChoiceHierarchy.Selector.quoted ρ)).symm

end

end Classicism.Meta.ChoiceBoolean.SelectorFailure
