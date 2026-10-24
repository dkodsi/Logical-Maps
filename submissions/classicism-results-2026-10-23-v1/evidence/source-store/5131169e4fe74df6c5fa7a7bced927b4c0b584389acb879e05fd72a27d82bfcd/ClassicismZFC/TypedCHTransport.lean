import ClassicismZFC.TypedRealEndpoint
import ClassicismZFC.BinaryRecoding
import ClassicismZFC.CHFieldTransport

/-!
# Exact internal-set/admitted-relation transfer of structural CH

Original formalization, misc, 23 October 2026. Both directions use the actual
finite-Separation constructions in TupleRecoding and BinaryRecoding. In
particular every admitted unary predicate and every admitted binary graph is
recoded; neither direction assumes externally full relation domains. The
source least inductive subset is identified with the typed construction's
natural-number code by internal Extensionality and mutual leastness.

Source-only development: compilation and axiom inspection remain pending.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Erdos501.FOL (L memM)
open Classicism.Meta

namespace ClassicismZFC.TypedCHTransport

open TypedReal
open CHCardinality (Subset Edge Injects Equinumerous)

variable {M : Type} [L.Structure M]
variable (hZFC : M ⊨ Erdos501.FOL.ZFC)
variable {E Add Mul Lt zero one : M}
variable (H : SourceFieldSemantics.Field E Add Mul Lt zero one)

private noncomputable abbrev S := TypedReal.hierarchy hZFC H

private noncomputable def forwardGraph (G : M) : Binary (S hZFC H) :=
  TupleRecoding.binary hZFC E ⟨zero, H.zero_mem⟩ G

private noncomputable def inverseGraph (G : Binary (S hZFC H)) : M :=
  BinaryRecoding.binaryGraph hZFC E ⟨zero, H.zero_mem⟩ G

private theorem forwardGraph_eval (G : M) (x y : Base (S hZFC H)) :
    bin (S hZFC H) (forwardGraph hZFC H G) x y ↔ Edge G x.val y.val :=
  TupleRecoding.binary_eval hZFC E ⟨zero, H.zero_mem⟩ G x y

private theorem inverseGraph_eval (G : Binary (S hZFC H))
    (x y : Base (S hZFC H)) :
    Edge (inverseGraph hZFC H G) x.val y.val ↔ bin (S hZFC H) G x y :=
  BinaryRecoding.binaryGraph_eval hZFC E ⟨zero, H.zero_mem⟩ G x y

private theorem inverseGraph_support (G : Binary (S hZFC H)) {x y : M}
    (hxy : Edge (inverseGraph hZFC H G) x y) : memM x E ∧ memM y E := by
  obtain ⟨a, b, ha, hb, heq⟩ :=
    BinaryRecoding.binaryGraph_support hZFC E ⟨zero, H.zero_mem⟩ G
      (SetLaws.pairM x y) hxy
  obtain ⟨rfl, rfl⟩ := SetLaws.pair_injective hZFC x y a b heq
  exact ⟨ha, hb⟩

/-- A normalized internal injection gives an admitted binary injection.
The endpoint predicates need only have the displayed, proved profiles. -/
theorem injection_forward {A B G : M} {Y Z : Unary (S hZFC H)}
    (hBE : Subset B E)
    (hY : ∀ x : Base (S hZFC H), un (S hZFC H) Y x ↔ memM (M := M) x.val A)
    (hZ : ∀ x : Base (S hZFC H), un (S hZFC H) Z x ↔ memM (M := M) x.val B)
    (hG : CHCardinality.Injection A B G) :
    TypedRealQuotation.Injection (S hZFC H) Y Z (forwardGraph hZFC H G) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hs := hG.1 x.val y.val ((forwardGraph_eval hZFC H G x y).mp hxy)
    exact ⟨(hY x).mpr hs.1, (hZ y).mpr hs.2⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := hG.2.1 x.val ((hY x).mp hx)
    let y' : Base (S hZFC H) := ⟨y, hBE y (hG.1 x.val y hxy).2⟩
    exact ⟨y', (forwardGraph_eval hZFC H G x y').mpr hxy⟩
  · intro x y z hxy hxz
    apply Subtype.ext
    exact hG.2.2.1 x.val y.val z.val
      ((forwardGraph_eval hZFC H G x y).mp hxy)
      ((forwardGraph_eval hZFC H G x z).mp hxz)
  · intro x y z hxz hyz
    apply Subtype.ext
    exact hG.2.2.2 x.val y.val z.val
      ((forwardGraph_eval hZFC H G x z).mp hxz)
      ((forwardGraph_eval hZFC H G y z).mp hyz)

/-- The reverse construction applies to any admitted graph, using its actual
inverse recoding and support theorem, including at untyped source arguments. -/
theorem injection_inverse {A B : M} {Y Z : Unary (S hZFC H)}
    (hAE : Subset A E)
    (hY : ∀ x : Base (S hZFC H), un (S hZFC H) Y x ↔ memM (M := M) x.val A)
    (hZ : ∀ x : Base (S hZFC H), un (S hZFC H) Z x ↔ memM (M := M) x.val B)
    {G : Binary (S hZFC H)} (hG : TypedRealQuotation.Injection (S hZFC H) Y Z G) :
    CHCardinality.Injection A B (inverseGraph hZFC H G) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hs := inverseGraph_support hZFC H G hxy
    let x' : Base (S hZFC H) := ⟨x, hs.1⟩
    let y' : Base (S hZFC H) := ⟨y, hs.2⟩
    have ht := hG.1 x' y' ((inverseGraph_eval hZFC H G x' y').mp hxy)
    exact ⟨(hY x').mp ht.1, (hZ y').mp ht.2⟩
  · intro x hx
    let x' : Base (S hZFC H) := ⟨x, hAE x hx⟩
    obtain ⟨y, hxy⟩ := hG.2.1 x' ((hY x').mpr hx)
    exact ⟨y.val, (inverseGraph_eval hZFC H G x' y).mpr hxy⟩
  · intro x y z hxy hxz
    have hxyE := inverseGraph_support hZFC H G hxy
    have hxzE := inverseGraph_support hZFC H G hxz
    let x' : Base (S hZFC H) := ⟨x, hxyE.1⟩
    let y' : Base (S hZFC H) := ⟨y, hxyE.2⟩
    let z' : Base (S hZFC H) := ⟨z, hxzE.2⟩
    exact congrArg Subtype.val (hG.2.2.1 x' y' z'
      ((inverseGraph_eval hZFC H G x' y').mp hxy)
      ((inverseGraph_eval hZFC H G x' z').mp hxz))
  · intro x y z hxz hyz
    have hxzE := inverseGraph_support hZFC H G hxz
    have hyzE := inverseGraph_support hZFC H G hyz
    let x' : Base (S hZFC H) := ⟨x, hxzE.1⟩
    let y' : Base (S hZFC H) := ⟨y, hyzE.1⟩
    let z' : Base (S hZFC H) := ⟨z, hxzE.2⟩
    exact congrArg Subtype.val (hG.2.2.2 x' y' z'
      ((inverseGraph_eval hZFC H G x' z').mp hxz)
      ((inverseGraph_eval hZFC H G y' z').mp hyz))

theorem bijection_forward {A B G : M} {Y Z : Unary (S hZFC H)}
    (hAE : Subset A E) (hBE : Subset B E)
    (hY : ∀ x : Base (S hZFC H), un (S hZFC H) Y x ↔ memM (M := M) x.val A)
    (hZ : ∀ x : Base (S hZFC H), un (S hZFC H) Z x ↔ memM (M := M) x.val B)
    (hG : CHCardinality.Bijection A B G) :
    TypedRealQuotation.Bijection (S hZFC H) Y Z (forwardGraph hZFC H G) := by
  refine ⟨injection_forward hZFC H hBE hY hZ hG.1, ?_⟩
  intro y hy
  obtain ⟨x, hxy⟩ := hG.2 y.val ((hZ y).mp hy)
  let x' : Base (S hZFC H) := ⟨x, hAE x (hG.1.1 x y.val hxy).1⟩
  exact ⟨x', (forwardGraph_eval hZFC H G x' y).mpr hxy⟩

theorem bijection_inverse {A B : M} {Y Z : Unary (S hZFC H)}
    (hAE : Subset A E) (hBE : Subset B E)
    (hY : ∀ x : Base (S hZFC H), un (S hZFC H) Y x ↔ memM (M := M) x.val A)
    (hZ : ∀ x : Base (S hZFC H), un (S hZFC H) Z x ↔ memM (M := M) x.val B)
    {G : Binary (S hZFC H)} (hG : TypedRealQuotation.Bijection (S hZFC H) Y Z G) :
    CHCardinality.Bijection A B (inverseGraph hZFC H G) := by
  refine ⟨injection_inverse hZFC H hAE hY hZ hG.1, ?_⟩
  intro y hy
  let y' : Base (S hZFC H) := ⟨y, hBE y hy⟩
  obtain ⟨x, hxy⟩ := hG.2 y' ((hZ y').mpr hy)
  exact ⟨x.val, (inverseGraph_eval hZFC H G x y').mpr hxy⟩

theorem exists_injection_iff {A B : M} {Y Z : Unary (S hZFC H)}
    (hAE : Subset A E) (hBE : Subset B E)
    (hY : ∀ x : Base (S hZFC H), un (S hZFC H) Y x ↔ memM (M := M) x.val A)
    (hZ : ∀ x : Base (S hZFC H), un (S hZFC H) Z x ↔ memM (M := M) x.val B) :
    (∃ G, TypedRealQuotation.Injection (S hZFC H) Y Z G) ↔ Injects A B := by
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨inverseGraph hZFC H G, injection_inverse hZFC H hAE hY hZ hG⟩
  · rintro ⟨G, hG⟩
    exact ⟨forwardGraph hZFC H G, injection_forward hZFC H hBE hY hZ hG⟩

theorem exists_bijection_iff {A B : M} {Y Z : Unary (S hZFC H)}
    (hAE : Subset A E) (hBE : Subset B E)
    (hY : ∀ x : Base (S hZFC H), un (S hZFC H) Y x ↔ memM (M := M) x.val A)
    (hZ : ∀ x : Base (S hZFC H), un (S hZFC H) Z x ↔ memM (M := M) x.val B) :
    (∃ G, TypedRealQuotation.Bijection (S hZFC H) Y Z G) ↔ Equinumerous A B := by
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨inverseGraph hZFC H G, bijection_inverse hZFC H hAE hBE hY hZ hG⟩
  · rintro ⟨G, hG⟩
    exact ⟨forwardGraph hZFC H G, bijection_forward hZFC H hAE hBE hY hZ hG⟩

/-- Uniqueness uses the model's internal set Extensionality, not equality of
external subsets of the carrier. -/
theorem naturalCode_eq {N : M}
    (hN : LeastInductive.LeastInductive E zero one Add N) :
    TypedReal.naturalCode hZFC H = N := by
  have hc := LeastInductive.leastSet_spec hZFC E zero one Add H.zero_mem
  apply SetLaws.ext hZFC (TypedReal.naturalCode hZFC H) N
  intro x
  exact ⟨hc.2 N hN.1 x, hN.2 _ hc.1 x⟩

/-- The natural predicate constructed by TypedReal represents this very N. -/
theorem naturals_eval_of_least {N : M}
    (hN : LeastInductive.LeastInductive E zero one Add N)
    (x : Base (S hZFC H)) :
    un (S hZFC H) (TypedReal.naturals hZFC H) x ↔ memM (M := M) x.val N := by
  rw [TypedReal.naturals_eval, naturalCode_eq hZFC H hN]

/-- Exact equivalence for the original internal-set and admitted-graph CH
statements. Every quantified unary or binary object is covered in each direction. -/
theorem structuralCH_iff {N : M}
    (hN : LeastInductive.LeastInductive E zero one Add N) :
    CHFieldTransport.StructuralCH E N ↔
      TypedRealQuotation.StructuralCH (TypedReal.hierarchy hZFC H)
        (TypedReal.domain hZFC H) (TypedReal.naturals hZFC H) := by
  have hNE : Subset N E := hN.1.1
  have hEE : Subset E E := fun _ hx => hx
  have hdom : ∀ x : Base (S hZFC H),
      un (S hZFC H) (TypedReal.domain hZFC H) x ↔ memM (M := M) x.val E :=
    fun x => ⟨fun _ => x.property, fun _ => TypedReal.domain_eval hZFC H x⟩
  have hnat := naturals_eval_of_least hZFC H hN
  constructor
  · intro hCH Y _
    let A := TupleRecoding.unarySubset hZFC E ⟨zero, H.zero_mem⟩ Y
    have hAE : Subset A E :=
      TupleRecoding.unarySubset_subset hZFC E ⟨zero, H.zero_mem⟩ Y
    have hY : ∀ x : Base (S hZFC H), un (S hZFC H) Y x ↔ memM (M := M) x.val A :=
      fun x => (TupleRecoding.unarySubset_eval hZFC E ⟨zero, H.zero_mem⟩ Y x).symm
    rcases hCH A hAE with h | h
    · exact Or.inl ((exists_injection_iff hZFC H hAE hNE hY hnat).mpr h)
    · exact Or.inr ((exists_bijection_iff hZFC H hAE hEE hY hdom).mpr h)
  · intro hCH A hAE
    let Y := TupleRecoding.unary hZFC E ⟨zero, H.zero_mem⟩ A
    have hY : ∀ x : Base (S hZFC H), un (S hZFC H) Y x ↔ memM (M := M) x.val A :=
      TupleRecoding.unary_eval hZFC E ⟨zero, H.zero_mem⟩ A
    rcases hCH Y (fun x _ => TypedReal.domain_eval hZFC H x) with h | h
    · exact Or.inl ((exists_injection_iff hZFC H hAE hNE hY hnat).mp h)
    · exact Or.inr ((exists_bijection_iff hZFC H hAE hEE hY hdom).mp h)

theorem not_structuralCH_iff {N : M}
    (hN : LeastInductive.LeastInductive E zero one Add N) :
    ¬ CHFieldTransport.StructuralCH E N ↔
      ¬ TypedRealQuotation.StructuralCH (TypedReal.hierarchy hZFC H)
        (TypedReal.domain hZFC H) (TypedReal.naturals hZFC H) :=
  not_congr (structuralCH_iff hZFC H hN)

/-- The positive internal-set witness satisfies the existing quoted target. -/
theorem component_hasRealCH {N : M}
    (hN : LeastInductive.LeastInductive E zero one Add N)
    (hCH : CHFieldTransport.StructuralCH E N) :
    (InternalHierarchy.component hZFC E ⟨zero, H.zero_mem⟩).HoldsSentence
      (Classicism.Meta.Research.CoalescedCH.existsRealCH .e) :=
  TypedReal.component_hasRealCH hZFC H ((structuralCH_iff hZFC H hN).mp hCH)

/-- The reverse implication is essential: an internal negative witness
remains negative for the actual quoted admitted-graph CH matrix. -/
theorem component_hasRealNotCH {N : M}
    (hN : LeastInductive.LeastInductive E zero one Add N)
    (hCH : ¬ CHFieldTransport.StructuralCH E N) :
    (InternalHierarchy.component hZFC E ⟨zero, H.zero_mem⟩).HoldsSentence
      (Classicism.Meta.Research.CoalescedCH.existsRealNotCH .e) :=
  TypedReal.component_hasRealNotCH hZFC H ((not_structuralCH_iff hZFC H hN).mp hCH)

#print axioms naturalCode_eq
#print axioms structuralCH_iff
#print axioms component_hasRealCH
#print axioms component_hasRealNotCH

end ClassicismZFC.TypedCHTransport
