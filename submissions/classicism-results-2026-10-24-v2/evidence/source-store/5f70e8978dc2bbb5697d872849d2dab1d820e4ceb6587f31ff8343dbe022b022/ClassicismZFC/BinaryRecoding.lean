import ClassicismZFC.TupleRecoding

/-!
# Inverse recoding of every admitted binary relation

The typed hierarchy encodes a binary tuple as `pair(x,pair(y,empty))`.
Source graphs instead use `pair(x,y)`. Separation on the internal product
of the individual domain with itself, using the explicit raw formula below,
constructs a source graph with exactly the admitted relation's profile.

This construction applies to every admitted binary relation, not just those
previously obtained by forward recoding. No arbitrary external predicate
is used as a Separation instance.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Erdos501.FOL (L memM)
open Classicism.Meta
open Classicism.Meta.CoalescedInternalHierarchy
open ClassicismZFC.SetLaws (pairM emptyM)
open ClassicismZFC.InternalHierarchy (internalUniverse)
open ClassicismZFC.TupleRecoding (Base Relation binaryTy profile)

namespace ClassicismZFC.BinaryRecoding

variable {M : Type} [L.Structure M]

/-- For the candidate graph element `z`, this says
`∃x∈E ∃y∈E, z=pair(x,y) ∧ pair(x,pair(y,empty))∈G`.
After the two binders the raw context is `[y,x,z]`. -/
def binaryGraphFormula (E G : M) : RawFormula M [.e] :=
  .ex .e (.ex .e
    (.conj (.mem (.var (.succ .zero)) (.param E))
      (.conj (.mem (.var .zero) (.param E))
        (.conj
          (.equal (.var (.succ (.succ .zero)))
            (.pair (.var (.succ .zero)) (.var .zero)))
          (.mem
            (.pair (.var (.succ .zero)) (.pair (.var .zero) (.param emptyM)))
            (.param G))))))

theorem realize_binaryGraphFormula (E G z : M) :
    (binaryGraphFormula E G).Realize memM pairM (.cons z .nil) ↔
      ∃ x y : M, memM x E ∧ memM y E ∧ z = pairM x y ∧
        memM (pairM x (pairM y emptyM)) G := by
  simp only [binaryGraphFormula, RawFormula.Realize, RawTerm.eval, IEnv.get]

/-- Every admitted binary relation has an internal source graph, supported
on the actual product and agreeing at every pair of typed individuals. -/
theorem binary_graph_exists (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) (G : Relation hZFC E hE binaryTy) :
    ∃ B : M,
      (∀ z, memM z B → ∃ x y, memM x E ∧ memM y E ∧ z = pairM x y) ∧
      ∀ x y : Base hZFC E hE,
        memM (M := M) (pairM (M := M) x.val y.val) B ↔
          profile hZFC E hE binaryTy G (x, y, PUnit.unit) := by
  obtain ⟨B, hB⟩ := (internalUniverse hZFC E hE).separation []
    (binaryGraphFormula (M := M) E G.val) IEnv.nil (Product.product (M := M) hZFC E E)
  have hB' : ∀ z : M, memM z B ↔
      memM z (Product.product hZFC E E) ∧
        ∃ x y, memM x E ∧ memM y E ∧ z = pairM x y ∧
          memM (pairM x (pairM y emptyM)) G.val := by
    intro z
    simpa only [internalUniverse, realize_binaryGraphFormula] using hB z
  refine ⟨B, ?_, ?_⟩
  · intro z hz
    exact (Product.product_mem hZFC E E z).mp ((hB' z).mp hz).1
  · intro x y
    change memM (M := M) (pairM (M := M) x.val y.val) B ↔
      memM (M := M) (pairM (M := M) x.val (pairM (M := M) y.val emptyM)) G.val
    constructor
    · intro hxy
      obtain ⟨a, b, _, _, heq, hG⟩ := ((hB' (pairM (M := M) x.val y.val)).mp hxy).2
      have hp := SetLaws.pair_injective hZFC x.val y.val a b heq
      rw [hp.1, hp.2]
      exact hG
    · intro hG
      apply (hB' (pairM (M := M) x.val y.val)).mpr
      refine ⟨?_, x.val, y.val, x.property, y.property, rfl, hG⟩
      exact (Product.product_mem hZFC E E (pairM (M := M) x.val y.val)).mpr
        ⟨x.val, y.val, x.property, y.property, rfl⟩

/-- A source graph chosen from the proved inverse-recoding theorem. -/
noncomputable def binaryGraph (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) (G : Relation hZFC E hE binaryTy) : M :=
  Classical.choose (binary_graph_exists hZFC E hE G)

theorem binaryGraph_support (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) (G : Relation hZFC E hE binaryTy) :
    ∀ z, memM z (binaryGraph hZFC E hE G) →
      ∃ x y, memM x E ∧ memM y E ∧ z = pairM x y :=
  (Classical.choose_spec (binary_graph_exists hZFC E hE G)).1

theorem binaryGraph_subset (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) (G : Relation hZFC E hE binaryTy) :
    ∀ z, memM z (binaryGraph hZFC E hE G) → memM z (Product.product hZFC E E) := by
  intro z hz
  exact (Product.product_mem hZFC E E z).mpr
    (binaryGraph_support hZFC E hE G z hz)

theorem binaryGraph_eval (hZFC : M ⊨ Erdos501.FOL.ZFC) (E : M)
    (hE : ∃ x, memM x E) (G : Relation hZFC E hE binaryTy)
    (x y : Base hZFC E hE) :
    memM (M := M) (pairM (M := M) x.val y.val) (binaryGraph hZFC E hE G) ↔
      profile hZFC E hE binaryTy G (x, y, PUnit.unit) :=
  (Classical.choose_spec (binary_graph_exists hZFC E hE G)).2 x y

#print axioms realize_binaryGraphFormula
#print axioms binary_graph_exists
#print axioms binaryGraph_support
#print axioms binaryGraph_subset
#print axioms binaryGraph_eval

end ClassicismZFC.BinaryRecoding
