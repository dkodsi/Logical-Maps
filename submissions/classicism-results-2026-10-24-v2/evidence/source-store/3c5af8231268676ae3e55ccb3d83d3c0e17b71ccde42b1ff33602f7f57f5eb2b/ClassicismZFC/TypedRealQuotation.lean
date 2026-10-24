import ClassicismZFC.TypedRealVocabulary
import Classicism.Models.CoalescedFirstOrder
import Classicism.Results.Research.AnalyticHasRealTerm
import Classicism.Results.Research.CoalescedCHMaximalism

/-!
# Truth of the original quoted real-structure and structural-CH sentences

Original formalization by Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. The formulas are the existing quotations in
`AnalyticReuseQuotation` and `CoalescedCHVocabularyCertificates`; no new
quotation or shallow reflection principle is introduced here.

Every unary or binary quantifier in the semantic matrices ranges over the
admitted domain of the given first-order structure. In particular structural
CH here concerns internal subproperties and internal graphs. The only model
hypothesis is the actual intensional term-closure property used by the
previously proved connective and quantifier truth lemmas. For the ZFC
hierarchy this property is supplied by `InternalHierarchy.firstOrder_isModel`.
This file itself does not assert CH or its negation in that hierarchy.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option pp.maxSteps 100

open CategoryTheory
open Classicism.Meta

namespace ClassicismZFC.TypedRealQuotation

open TypedReal

set_option allowUnsafeReducibility true in
attribute [local reducible] ChoiceFirstOrder.Structure.model
  ChoiceFirstOrder.inner ChoiceFirstOrder.action

variable (S : ChoiceFirstOrder.Structure)

/-- Exactly the admitted-graph interpretation of the original injection matrix. -/
def Injection (Y Z : Unary S) (G : Binary S) : Prop :=
  (∀ x y, bin S G x y → un S Y x ∧ un S Z y) ∧
  (∀ x, un S Y x → ∃ y, bin S G x y) ∧
  (∀ x y z, bin S G x y → bin S G x z → y = z) ∧
  (∀ x y z, bin S G x z → bin S G y z → x = y)

def Bijection (Y Z : Unary S) (G : Binary S) : Prop :=
  Injection S Y Z G ∧ ∀ y, un S Z y → ∃ x, bin S G x y

/-- Structural CH with both relation quantifiers restricted to admitted objects. -/
def StructuralCH (X N : Unary S) : Prop :=
  ∀ Y : Unary S, (∀ x, un S Y x → un S X x) →
    (∃ G : Binary S, Injection S Y N G) ∨
    (∃ G : Binary S, Bijection S Y X G)

/-! The atomic leaves of the already quoted terms. These lemmas interpret
actual applications, not an independently defined first-order translation. -/

theorem holds_un {Γ : Ctx} (g : IEnv S.D Γ)
    (F : Var Γ (.rel unaryTy)) (x : Var Γ .e) :
    S.model.Holds (𝟙 ChoiceFirstOrder.World.star)
      (.app (.var F) (.var x)) g ↔ un S (g.get F) (g.get x) := by
  rw [S.model.holds_app (𝟙 ChoiceFirstOrder.World.star) g
    (.var F) (.var x) (a' := g.get x) rfl] <;> rfl

theorem holds_bin {Γ : Ctx} (g : IEnv S.D Γ)
    (F : Var Γ (.rel binaryTy)) (x y : Var Γ .e) :
    S.model.Holds (𝟙 ChoiceFirstOrder.World.star)
      (.app (.app (.var F) (.var x)) (.var y)) g ↔
      bin S (g.get F) (g.get x) (g.get y) := by
  simp only [Intensional.Premodel.Holds, Intensional.Premodel.sem,
    S.model.apply_Incl] <;> rfl

theorem holds_tri {Γ : Ctx} (g : IEnv S.D Γ)
    (F : Var Γ (.rel ternaryTy)) (x y z : Var Γ .e) :
    S.model.Holds (𝟙 ChoiceFirstOrder.World.star)
      (.app (.app (.app (.var F) (.var x)) (.var y)) (.var z)) g ↔
      tri S (g.get F) (g.get x) (g.get y) (g.get z) := by
  simp only [Intensional.Premodel.Holds, Intensional.Premodel.sem,
    S.model.apply_Incl] <;> rfl

theorem holds_equal (hModel : S.model.IsModel) {Γ : Ctx}
    (g : IEnv S.D Γ) (x y : Var Γ .e) :
    S.model.Holds (𝟙 ChoiceFirstOrder.World.star)
      (Term.eq' (.var x) (.var y)) g ↔ g.get x = g.get y := by
  exact (S.model.holds_eq hModel (𝟙 ChoiceFirstOrder.World.star) g
    (.var x) (.var y)).trans Iff.rfl

/-- The existing quotation of real-structure existence, with its exact seven
binders and all internal completeness/least-inductivity quantifiers. -/
theorem holds_hasReal_iff (hModel : S.model.IsModel) :
    S.model.HoldsSentence (Classicism.Research.Analytic.HasReal.term .e) ↔
      ∃ (X : Unary S) (le : Binary S) (add mul : Ternary S)
        (zero one : Base S) (N : Unary S),
        IsReal S X le add mul zero one N := by
  classical
  simp only [Classicism.Research.Analytic.HasReal.term,
    Intensional.Premodel.HoldsSentence,
    S.model.holds_exists hModel, S.model.holds_forall hModel,
    S.model.holds_conj hModel, S.model.holds_disj hModel,
    S.model.holds_neg hModel, S.model.holds_imp hModel,
    holds_un, holds_bin, holds_tri, holds_equal S hModel, IEnv.get,
    TypedReal.IsReal, TypedReal.OrderedField, TypedReal.LinearOrder, TypedReal.BinaryOperation,
    TypedReal.AdditiveLaws, TypedReal.MultiplicativeLaws, TypedReal.Distributive, TypedReal.OrderCompatible,
    TypedReal.CompleteNonempty, TypedReal.CompleteClause, TypedReal.LeastUpperBound, TypedReal.UpperBound,
    TypedReal.LeastInductive, TypedReal.LeastClause, TypedReal.Inductive, Ne, ← imp_iff_not_or]

/-- Truth of the exact sentence consumed by the existing CH/Maximalism chain. -/
theorem holds_existsRealCH_iff (hModel : S.model.IsModel) :
    S.model.HoldsSentence (Classicism.Meta.Research.CoalescedCH.existsRealCH .e) ↔
      ∃ (X : Unary S) (le : Binary S) (add mul : Ternary S)
        (zero one : Base S) (N : Unary S),
        IsReal S X le add mul zero one N ∧ StructuralCH S X N := by
  classical
  simp only [Classicism.Meta.Research.CoalescedCH.existsRealCH,
    Classicism.Research.CoalescedCH.HasRealCH.quoted,
    Intensional.Premodel.HoldsSentence,
    S.model.holds_exists hModel, S.model.holds_forall hModel,
    S.model.holds_conj hModel, S.model.holds_disj hModel,
    S.model.holds_neg hModel, S.model.holds_imp hModel,
    holds_un, holds_bin, holds_tri, holds_equal S hModel, IEnv.get,
    TypedReal.IsReal, TypedReal.OrderedField, TypedReal.LinearOrder, TypedReal.BinaryOperation,
    TypedReal.AdditiveLaws, TypedReal.MultiplicativeLaws, TypedReal.Distributive, TypedReal.OrderCompatible,
    TypedReal.CompleteNonempty, TypedReal.CompleteClause, TypedReal.LeastUpperBound, TypedReal.UpperBound,
    TypedReal.LeastInductive, TypedReal.LeastClause, TypedReal.Inductive,
    StructuralCH, Injection, Bijection, Ne, ← imp_iff_not_or]

/-- The negation remains inside the seven existential binders, exactly as in
the original `HasRealNotCH` quotation. -/
theorem holds_existsRealNotCH_iff (hModel : S.model.IsModel) :
    S.model.HoldsSentence (Classicism.Meta.Research.CoalescedCH.existsRealNotCH .e) ↔
      ∃ (X : Unary S) (le : Binary S) (add mul : Ternary S)
        (zero one : Base S) (N : Unary S),
        IsReal S X le add mul zero one N ∧ ¬ StructuralCH S X N := by
  classical
  simp only [Classicism.Meta.Research.CoalescedCH.existsRealNotCH,
    Classicism.Research.CoalescedCH.HasRealNotCH.quoted,
    Intensional.Premodel.HoldsSentence,
    S.model.holds_exists hModel, S.model.holds_forall hModel,
    S.model.holds_conj hModel, S.model.holds_disj hModel,
    S.model.holds_neg hModel, S.model.holds_imp hModel,
    holds_un, holds_bin, holds_tri, holds_equal S hModel, IEnv.get,
    TypedReal.IsReal, TypedReal.OrderedField, TypedReal.LinearOrder, TypedReal.BinaryOperation,
    TypedReal.AdditiveLaws, TypedReal.MultiplicativeLaws, TypedReal.Distributive, TypedReal.OrderCompatible,
    TypedReal.CompleteNonempty, TypedReal.CompleteClause, TypedReal.LeastUpperBound, TypedReal.UpperBound,
    TypedReal.LeastInductive, TypedReal.LeastClause, TypedReal.Inductive,
    StructuralCH, Injection, Bijection, Ne, ← imp_iff_not_or]

theorem holds_hasReal_of (hModel : S.model.IsModel)
    {X : Unary S} {le : Binary S} {add mul : Ternary S}
    {zero one : Base S} {N : Unary S}
    (hReal : IsReal S X le add mul zero one N) :
    S.model.HoldsSentence (Classicism.Research.Analytic.HasReal.term .e) :=
  (holds_hasReal_iff S hModel).mpr ⟨X, le, add, mul, zero, one, N, hReal⟩

theorem holds_existsRealCH_of (hModel : S.model.IsModel)
    {X : Unary S} {le : Binary S} {add mul : Ternary S}
    {zero one : Base S} {N : Unary S}
    (hReal : IsReal S X le add mul zero one N) (hCH : StructuralCH S X N) :
    S.model.HoldsSentence (Classicism.Meta.Research.CoalescedCH.existsRealCH .e) :=
  (holds_existsRealCH_iff S hModel).mpr
    ⟨X, le, add, mul, zero, one, N, hReal, hCH⟩

theorem holds_existsRealNotCH_of (hModel : S.model.IsModel)
    {X : Unary S} {le : Binary S} {add mul : Ternary S}
    {zero one : Base S} {N : Unary S}
    (hReal : IsReal S X le add mul zero one N) (hNotCH : ¬ StructuralCH S X N) :
    S.model.HoldsSentence (Classicism.Meta.Research.CoalescedCH.existsRealNotCH .e) :=
  (holds_existsRealNotCH_iff S hModel).mpr
    ⟨X, le, add, mul, zero, one, N, hReal, hNotCH⟩

/-- The same original sentence in the literal one-world component category. -/
theorem component_hasReal_of (hModel : S.model.IsModel)
    {X : Unary S} {le : Binary S} {add mul : Ternary S}
    {zero one : Base S} {N : Unary S}
    (hReal : IsReal S X le add mul zero one N) :
    (Intensional.Coalesced.FirstOrderBridge.model S).HoldsSentence
      (Classicism.Research.Analytic.HasReal.term .e) :=
  (Intensional.Coalesced.FirstOrderBridge.holdsSentence_iff S _).mpr
    (holds_hasReal_of S hModel hReal)

theorem component_existsRealCH_of (hModel : S.model.IsModel)
    {X : Unary S} {le : Binary S} {add mul : Ternary S}
    {zero one : Base S} {N : Unary S}
    (hReal : IsReal S X le add mul zero one N) (hCH : StructuralCH S X N) :
    (Intensional.Coalesced.FirstOrderBridge.model S).HoldsSentence
      (Classicism.Meta.Research.CoalescedCH.existsRealCH .e) :=
  (Intensional.Coalesced.FirstOrderBridge.holdsSentence_iff S _).mpr
    (holds_existsRealCH_of S hModel hReal hCH)

theorem component_existsRealNotCH_of (hModel : S.model.IsModel)
    {X : Unary S} {le : Binary S} {add mul : Ternary S}
    {zero one : Base S} {N : Unary S}
    (hReal : IsReal S X le add mul zero one N) (hNotCH : ¬ StructuralCH S X N) :
    (Intensional.Coalesced.FirstOrderBridge.model S).HoldsSentence
      (Classicism.Meta.Research.CoalescedCH.existsRealNotCH .e) :=
  (Intensional.Coalesced.FirstOrderBridge.holdsSentence_iff S _).mpr
    (holds_existsRealNotCH_of S hModel hReal hNotCH)

#print axioms holds_hasReal_iff
#print axioms holds_existsRealCH_iff
#print axioms holds_existsRealNotCH_iff
#print axioms component_existsRealCH_of
#print axioms component_existsRealNotCH_of

end ClassicismZFC.TypedRealQuotation
