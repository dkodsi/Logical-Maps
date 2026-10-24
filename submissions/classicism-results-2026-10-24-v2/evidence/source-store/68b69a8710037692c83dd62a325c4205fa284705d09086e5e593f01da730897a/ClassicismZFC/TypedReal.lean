import ClassicismZFC.TypedRealVocabulary
import ClassicismZFC.SourceFieldAlgebra
import ClassicismZFC.TupleRecoding
import ClassicismZFC.LeastInductive

/-!
# Actual admitted real-structure witnesses from a source complete field

The input is satisfaction of the source's literal twenty-clause field formula
in an ordinary ZFC model. The seven typed witnesses are constructed by finite
graph recoding and the internal least-inductive-set construction. Completeness
and leastness quantify over every admitted unary relation by decoding it to
an actual internal subset. No external fullness, Real, CH correspondence, or
term-closure hypothesis is introduced.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Erdos501.FOL (L memM)
open Classicism.Meta

namespace ClassicismZFC.TypedReal

open SetLaws SourceFieldSemantics SourceFieldAlgebra

variable {M : Type} [L.Structure M]
variable (hZFC : M ⊨ Erdos501.FOL.ZFC)
variable {E Add Mul Lt zero one : M} (H : Field E Add Mul Lt zero one)

noncomputable abbrev hierarchy : ChoiceFirstOrder.Structure :=
  InternalHierarchy.typedStructure hZFC E ⟨zero, H.zero_mem⟩

noncomputable def domain : Unary (hierarchy hZFC H) :=
  TupleRecoding.unary hZFC E ⟨zero, H.zero_mem⟩ E

noncomputable def order : Binary (hierarchy hZFC H) :=
  TupleRecoding.binaryLe hZFC E ⟨zero, H.zero_mem⟩ Lt

noncomputable def addition : Ternary (hierarchy hZFC H) :=
  TupleRecoding.ternary hZFC E ⟨zero, H.zero_mem⟩ Add

noncomputable def multiplication : Ternary (hierarchy hZFC H) :=
  TupleRecoding.ternary hZFC E ⟨zero, H.zero_mem⟩ Mul

def zeroValue : Base (hierarchy hZFC H) := ⟨zero, H.zero_mem⟩
def oneValue : Base (hierarchy hZFC H) := ⟨one, H.one_mem⟩

noncomputable def naturalCode : M :=
  ClassicismZFC.LeastInductive.leastSet hZFC E zero one Add H.zero_mem

noncomputable def naturals : Unary (hierarchy hZFC H) :=
  TupleRecoding.unary hZFC E ⟨zero, H.zero_mem⟩ (naturalCode hZFC H)

theorem domain_eval (x : Base (hierarchy hZFC H)) :
    un (hierarchy hZFC H) (domain hZFC H) x :=
  (TupleRecoding.unary_eval hZFC E ⟨zero, H.zero_mem⟩ E x).mpr x.property

theorem order_eval (x y : Base (hierarchy hZFC H)) :
    bin (hierarchy hZFC H) (order hZFC H) x y ↔ le Lt x.val y.val :=
  TupleRecoding.binaryLe_eval hZFC E ⟨zero, H.zero_mem⟩ Lt x y

theorem addition_eval (x y z : Base (hierarchy hZFC H)) :
    tri (hierarchy hZFC H) (addition hZFC H) x y z ↔ app2 Add x.val y.val z.val :=
  TupleRecoding.ternary_eval hZFC E ⟨zero, H.zero_mem⟩ Add x y z

theorem multiplication_eval (x y z : Base (hierarchy hZFC H)) :
    tri (hierarchy hZFC H) (multiplication hZFC H) x y z ↔ app2 Mul x.val y.val z.val :=
  TupleRecoding.ternary_eval hZFC E ⟨zero, H.zero_mem⟩ Mul x y z

theorem naturals_eval (x : Base (hierarchy hZFC H)) :
    un (hierarchy hZFC H) (naturals hZFC H) x ↔ memM (M := M) x.val (naturalCode hZFC H) :=
  TupleRecoding.unary_eval hZFC E ⟨zero, H.zero_mem⟩ (naturalCode hZFC H) x

theorem operation_isBinaryOperation (Op : M) (hOp : IsOp2 E Op) :
    BinaryOperation (hierarchy hZFC H) (domain hZFC H)
      (TupleRecoding.ternary hZFC E ⟨zero, H.zero_mem⟩ Op) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y z _
    exact ⟨domain_eval hZFC H x, domain_eval hZFC H y, domain_eval hZFC H z⟩
  · intro x y _ _
    obtain ⟨z, hz, hxyz, _⟩ := hOp x.val x.property y.val y.property
    exact ⟨⟨z, hz⟩,
      (TupleRecoding.ternary_eval hZFC E ⟨zero, H.zero_mem⟩ Op x y ⟨z, hz⟩).mpr hxyz⟩
  · intro x y z w hz hw
    apply Subtype.ext
    exact op_output_unique (M := M) hOp x.property y.property
      ((TupleRecoding.ternary_eval hZFC E ⟨zero, H.zero_mem⟩ Op x y z).mp hz)
      ((TupleRecoding.ternary_eval hZFC E ⟨zero, H.zero_mem⟩ Op x y w).mp hw)

theorem order_isLinearOrder :
    LinearOrder (hierarchy hZFC H) (domain hZFC H) (order hZFC H) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y _
    exact ⟨domain_eval hZFC H x, domain_eval hZFC H y⟩
  · intro x _
    exact (order_eval hZFC H x x).mpr (SourceFieldAlgebra.le_refl H x.property)
  · intro x y hxy hyx
    apply Subtype.ext
    exact SourceFieldAlgebra.le_antisymm H x.property y.property
      ((order_eval hZFC H x y).mp hxy) ((order_eval hZFC H y x).mp hyx)
  · intro x y z hxy hyz
    exact (order_eval hZFC H x z).mpr
      (SourceFieldAlgebra.le_trans H x.property y.property z.property
        ((order_eval hZFC H x y).mp hxy) ((order_eval hZFC H y z).mp hyz))
  · intro x y _ _
    exact (SourceFieldAlgebra.le_total H x.property y.property).elim
      (fun h => Or.inl ((order_eval hZFC H x y).mpr h))
      (fun h => Or.inr ((order_eval hZFC H y x).mpr h))

theorem addition_laws :
    AdditiveLaws (hierarchy hZFC H) (domain hZFC H) (addition hZFC H) (zeroValue hZFC H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _
    exact (addition_eval hZFC H x (zeroValue hZFC H) x).mpr (H.ident_plus x.val x.property)
  · intro x y z h
    exact (addition_eval hZFC H y x z).mpr
      (H.comm_plus x.val x.property y.val y.property z.val ((addition_eval hZFC H x y z).mp h))
  · intro a b c u v w hab huc hbc
    exact (addition_eval hZFC H a w v).mpr
      (graph_assoc_plus H a.property b.property c.property
        ((addition_eval hZFC H a b u).mp hab)
        ((addition_eval hZFC H u c v).mp huc)
        ((addition_eval hZFC H b c w).mp hbc))
  · intro x _
    obtain ⟨y, hy, hxy⟩ := H.addInv x.val x.property
    exact ⟨⟨y, hy⟩, (addition_eval hZFC H x ⟨y, hy⟩ (zeroValue hZFC H)).mpr hxy⟩

theorem multiplication_laws :
    MultiplicativeLaws (hierarchy hZFC H) (domain hZFC H) (multiplication hZFC H)
      (zeroValue hZFC H) (oneValue hZFC H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _
    exact (multiplication_eval hZFC H x (oneValue hZFC H) x).mpr (H.ident_times x.val x.property)
  · intro x y z h
    exact (multiplication_eval hZFC H y x z).mpr
      (H.comm_times x.val x.property y.val y.property z.val
        ((multiplication_eval hZFC H x y z).mp h))
  · intro a b c u v w hab huc hbc
    exact (multiplication_eval hZFC H a w v).mpr
      (graph_assoc_times H a.property b.property c.property
        ((multiplication_eval hZFC H a b u).mp hab)
        ((multiplication_eval hZFC H u c v).mp huc)
        ((multiplication_eval hZFC H b c w).mp hbc))
  · intro x _ hx
    have hx' : x.val ≠ zero := fun h => hx (Subtype.ext h)
    obtain ⟨y, hy, hxy⟩ := H.mulInv x.val x.property hx'
    exact ⟨⟨y, hy⟩,
      (multiplication_eval hZFC H x ⟨y, hy⟩ (oneValue hZFC H)).mpr hxy⟩

theorem distributivity :
    Distributive (hierarchy hZFC H) (addition hZFC H) (multiplication hZFC H) := by
  intro a b c s t u v hbc has hab hac
  exact (addition_eval hZFC H u v t).mpr
    (graph_distrib H a.property b.property c.property
      ((addition_eval hZFC H b c s).mp hbc)
      ((multiplication_eval hZFC H a s t).mp has)
      ((multiplication_eval hZFC H a b u).mp hab)
      ((multiplication_eval hZFC H a c v).mp hac))

theorem order_compatible :
    OrderCompatible (hierarchy hZFC H) (domain hZFC H) (order hZFC H)
      (addition hZFC H) (multiplication hZFC H) (zeroValue hZFC H) := by
  constructor
  · intro a b c u v hab _ hac hbc
    exact (order_eval hZFC H u v).mpr
      (add_le_add_right H a.property b.property c.property u.property v.property
        ((order_eval hZFC H a b).mp hab)
        ((addition_eval hZFC H a c u).mp hac)
        ((addition_eval hZFC H b c v).mp hbc))
  · intro a b c h0a h0b hmul
    exact (order_eval hZFC H (zeroValue hZFC H) c).mpr
      (mul_nonneg H a.property b.property c.property
        ((order_eval hZFC H (zeroValue hZFC H) a).mp h0a)
        ((order_eval hZFC H (zeroValue hZFC H) b).mp h0b)
        ((multiplication_eval hZFC H a b c).mp hmul))

theorem orderedField :
    OrderedField (hierarchy hZFC H) (domain hZFC H) (order hZFC H)
      (addition hZFC H) (multiplication hZFC H) (zeroValue hZFC H) (oneValue hZFC H) := by
  refine ⟨domain_eval hZFC H _, domain_eval hZFC H _, ?_,
    order_isLinearOrder hZFC H,
    operation_isBinaryOperation hZFC H Add H.isOp2_plus,
    operation_isBinaryOperation hZFC H Mul H.isOp2_times,
    addition_laws hZFC H, multiplication_laws hZFC H,
    distributivity hZFC H, order_compatible hZFC H⟩
  intro h
  exact H.zero_ne_one (congrArg Subtype.val h)

theorem completeNonempty :
    CompleteNonempty (hierarchy hZFC H) (domain hZFC H) (order hZFC H) := by
  intro F hF
  obtain ⟨_, ⟨x, hx⟩, b, hb⟩ := hF
  let A := TupleRecoding.unarySubset hZFC E ⟨zero, H.zero_mem⟩ F
  have hsub : ∀ z, memM z A → memM z E :=
    TupleRecoding.unarySubset_subset hZFC E ⟨zero, H.zero_mem⟩ F
  have htest (z : Base (hierarchy hZFC H)) : memM (M := M) z.val A ↔ un (hierarchy hZFC H) F z :=
    TupleRecoding.unarySubset_eval hZFC E ⟨zero, H.zero_mem⟩ F z
  have hpower : memM A (powerM E) := (SetLaws.power_mem hZFC E A).mpr hsub
  have hne : A ≠ emptyM := by
    intro he
    have hmem := (htest x).mpr hx
    rw [he] at hmem
    exact SetLaws.empty_mem hZFC x.val hmem
  have hbound : ∃ b', memM b' E ∧ ∀ s, memM s A → le Lt s b' := by
    refine ⟨b.val, b.property, ?_⟩
    intro s hs
    let s' : Base (hierarchy hZFC H) := ⟨s, hsub s hs⟩
    exact (order_eval hZFC H s' b).mp (hb.2 s' ((htest s').mp hs))
  obtain ⟨s, hs, hub, hlub⟩ := H.complete A hpower hne hbound
  let s' : Base (hierarchy hZFC H) := ⟨s, hs⟩
  refine ⟨s', ⟨domain_eval hZFC H s', ?_⟩, ?_⟩
  · intro y hy
    exact (order_eval hZFC H y s').mpr (hub y.val ((htest y).mpr hy))
  · intro c hc
    apply (order_eval hZFC H s' c).mpr
    apply hlub c.val c.property
    intro y hy
    let y' : Base (hierarchy hZFC H) := ⟨y, hsub y hy⟩
    exact (order_eval hZFC H y' c).mp (hc.2 y' ((htest y').mp hy))

theorem naturals_inductive :
    Inductive (hierarchy hZFC H) (domain hZFC H) (addition hZFC H)
      (zeroValue hZFC H) (oneValue hZFC H) (naturals hZFC H) := by
  refine ⟨fun x _ => domain_eval hZFC H x, ?_, ?_⟩
  · apply (naturals_eval hZFC H (zeroValue hZFC H)).mpr
    exact ClassicismZFC.LeastInductive.leastSet_zero_mem hZFC E zero one Add H.zero_mem
  · intro x y hx hxy
    apply (naturals_eval hZFC H y).mpr
    exact ClassicismZFC.LeastInductive.leastSet_succ_closed hZFC E zero one Add H.zero_mem
      x.val y.val x.property y.property ((naturals_eval hZFC H x).mp hx)
      ((addition_eval hZFC H x (oneValue hZFC H) y).mp hxy)

theorem naturals_leastInductive :
    LeastInductive (hierarchy hZFC H) (domain hZFC H) (addition hZFC H)
      (zeroValue hZFC H) (oneValue hZFC H) (naturals hZFC H) := by
  refine ⟨naturals_inductive hZFC H, ?_⟩
  intro F hF x hx
  let A := TupleRecoding.unarySubset hZFC E ⟨zero, H.zero_mem⟩ F
  have hsub : ∀ z, memM z A → memM z E :=
    TupleRecoding.unarySubset_subset hZFC E ⟨zero, H.zero_mem⟩ F
  have htest (z : Base (hierarchy hZFC H)) : memM (M := M) z.val A ↔ un (hierarchy hZFC H) F z :=
    TupleRecoding.unarySubset_eval hZFC E ⟨zero, H.zero_mem⟩ F z
  have hA : ClassicismZFC.LeastInductive.IsInductive E zero one Add A := by
    refine ⟨hsub, (htest (zeroValue hZFC H)).mpr hF.2.1, ?_⟩
    intro a b ha hb haF hab
    let a' : Base (hierarchy hZFC H) := ⟨a, ha⟩
    let b' : Base (hierarchy hZFC H) := ⟨b, hb⟩
    apply (htest b').mpr
    exact hF.2.2 a' b' ((htest a').mp haF)
      ((addition_eval hZFC H a' (oneValue hZFC H) b').mpr hab)
  apply (htest x).mp
  exact ClassicismZFC.LeastInductive.leastSet_least hZFC E zero one Add H.zero_mem A hA
    x.val ((naturals_eval hZFC H x).mp hx)

/-- The constructed seven admitted objects satisfy every real-structure clause. -/
theorem isReal :
    IsReal (hierarchy hZFC H) (domain hZFC H) (order hZFC H)
      (addition hZFC H) (multiplication hZFC H) (zeroValue hZFC H) (oneValue hZFC H)
      (naturals hZFC H) :=
  ⟨orderedField hZFC H, completeNonempty hZFC H, naturals_leastInductive hZFC H⟩

/-- Input is the literal first-order field formula, not a semantic Real premise. -/
theorem exists_typedReal (h : RealFieldSentence.IsField E Add Mul Lt zero one) :
    let S := hierarchy hZFC (SourceFieldSemantics.of_isField h)
    ∃ (X : Unary S) (le' : Binary S) (add mul : Ternary S)
      (zero' one' : Base S) (N : Unary S), IsReal S X le' add mul zero' one' N := by
  let H' := SourceFieldSemantics.of_isField h
  exact ⟨domain hZFC H', order hZFC H', addition hZFC H', multiplication hZFC H',
    zeroValue hZFC H', oneValue hZFC H', naturals hZFC H', isReal hZFC H'⟩

#print axioms orderedField
#print axioms completeNonempty
#print axioms naturals_leastInductive
#print axioms isReal
#print axioms exists_typedReal

end ClassicismZFC.TypedReal
