import ClassicismZFC.Separation

/-!
# Internal products from actual finite-formula Collection

For fixed `a`, collection of the explicit graph `z = pair(a,b)` over `B`
constructs its row. A second finite formula defines that row by its exact
membership. Collection of rows over `A`, followed by union, constructs the
product. The pairing operation is the source theory's primitive pair symbol;
no assertion about the members of an individual pair is required.
-/

open FirstOrder FirstOrder.Language
open Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.Product

open SetLaws

universe u

variable {M : Type u} [L.Structure M]

@[simp] private theorem realize_pair_term {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a b : L.Term (Empty ⊕ Fin n)) :
    (Term.func (Func.pair : L.Functions 2) ![a, b]).realize v =
      pairM (a.realize v) (b.realize v) :=
  Term.realize_functions_apply₂

/-- The finite formula `z = pair(a,b)`, at levels `a=0, b=1, z=2`. -/
def pairImageFormula : L.BoundedFormula Empty 3 :=
  Term.bdEqual (Term.var (Sum.inr ⟨2, by omega⟩))
    (Term.func (Func.pair : L.Functions 2)
      ![Term.var (Sum.inr ⟨0, by omega⟩), Term.var (Sum.inr ⟨1, by omega⟩)])

theorem realize_pairImageFormula (a b z : M) :
    pairImageFormula.Realize default (Fin.snoc (Fin.snoc ![a] b) z) ↔
      z = pairM a b := by
  simp only [pairImageFormula, BoundedFormula.realize_bdEqual,
    realize_pair_term, Term.realize_var, Sum.elim_inr] <;>
    simp [Fin.snoc]

/-- Collection constructs the set of all pairs with first coordinate `a`
and second coordinate in `B`. -/
theorem row (hZFC : M ⊨ Erdos501.FOL.ZFC) (a B : M) :
    ∃ R : M, ∀ z, memM z R ↔ ∃ b, memM b B ∧ z = pairM a b := by
  have hserial : ∀ b : M, memM b B →
      ∃ z, pairImageFormula.Realize default (Fin.snoc (Fin.snoc ![a] b) z) := by
    intro b _
    exact ⟨pairM a b, (realize_pairImageFormula a b (pairM a b)).mpr rfl⟩
  obtain ⟨R, hforward, hback⟩ :=
    collectionWithParams hZFC 1 pairImageFormula ![a] B hserial
  refine ⟨R, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨b, hb, hpair⟩ := hback z hz
    exact ⟨b, hb, (realize_pairImageFormula a b z).mp hpair⟩
  · rintro ⟨b, hb, hz⟩
    obtain ⟨y, hy, hpair⟩ := hforward b hb
    have hy_eq : y = pairM a b := (realize_pairImageFormula a b y).mp hpair
    have hz_eq : z = y := hz.trans hy_eq.symm
    simpa only [hz_eq] using hy

/-- The finite formula `∀z, z∈R ↔ ∃b, b∈B ∧ z=pair(a,b)`.
Its initial levels are `B=0, a=1, R=2`; `z=3` and `b=4` are bound. -/
def rowFormula : L.BoundedFormula Empty 3 :=
  BoundedFormula.all <|
    (Relations.boundedFormula₂ (Rel.mem : L.Relations 2)
      (Term.var (Sum.inr ⟨3, by omega⟩))
      (Term.var (Sum.inr ⟨2, by omega⟩))).iff
      (BoundedFormula.ex <|
        (Relations.boundedFormula₂ (Rel.mem : L.Relations 2)
          (Term.var (Sum.inr ⟨4, by omega⟩))
          (Term.var (Sum.inr ⟨0, by omega⟩))) ⊓
        Term.bdEqual (Term.var (Sum.inr ⟨3, by omega⟩))
          (Term.func (Func.pair : L.Functions 2)
            ![Term.var (Sum.inr ⟨1, by omega⟩),
              Term.var (Sum.inr ⟨4, by omega⟩)]))

theorem realize_rowFormula (B a R : M) :
    rowFormula.Realize default (Fin.snoc (Fin.snoc ![B] a) R) ↔
      ∀ z, memM z R ↔ ∃ b, memM b B ∧ z = pairM a b := by
  simp only [rowFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂,
    BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual,
    realize_pair_term, Term.realize_var, Sum.elim_inr] <;>
    simp [memM, Fin.snoc]

/-- Two instances of the actual finite Collection scheme and union give
the internal Cartesian product for the source theory's pair operation. -/
theorem product_exists (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B : M) :
    ∃ P : M, ∀ z, memM z P ↔
      ∃ x y, memM x A ∧ memM y B ∧ z = pairM x y := by
  have hserial : ∀ a : M, memM a A →
      ∃ R, rowFormula.Realize default (Fin.snoc (Fin.snoc ![B] a) R) := by
    intro a _
    obtain ⟨R, hR⟩ := row hZFC a B
    exact ⟨R, (realize_rowFormula B a R).mpr hR⟩
  obtain ⟨C, hforward, hback⟩ :=
    collectionWithParams hZFC 1 rowFormula ![B] A hserial
  refine ⟨unionM C, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨R, hRC, hzR⟩ := (union_mem hZFC C z).mp hz
    obtain ⟨a, haA, haR⟩ := hback R hRC
    obtain ⟨b, hbB, hzab⟩ := ((realize_rowFormula B a R).mp haR z).mp hzR
    exact ⟨a, b, haA, hbB, hzab⟩
  · rintro ⟨a, b, haA, hbB, hzab⟩
    obtain ⟨R, hRC, haR⟩ := hforward a haA
    apply (union_mem hZFC C z).mpr
    exact ⟨R, hRC, ((realize_rowFormula B a R).mp haR z).mpr ⟨b, hbB, hzab⟩⟩

/-- The product is chosen from the proved existence theorem. -/
noncomputable def product (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B : M) : M :=
  Classical.choose (product_exists hZFC A B)

theorem product_mem (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B z : M) :
    memM z (product hZFC A B) ↔
      ∃ x y, memM x A ∧ memM y B ∧ z = pairM x y :=
  Classical.choose_spec (product_exists hZFC A B) z

#print axioms realize_pairImageFormula
#print axioms row
#print axioms realize_rowFormula
#print axioms product_exists
#print axioms product_mem

end ClassicismZFC.Product
