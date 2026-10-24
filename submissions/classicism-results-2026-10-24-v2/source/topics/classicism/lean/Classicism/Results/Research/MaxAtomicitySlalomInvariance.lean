import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Finset.Card

/-!
# Boolean names and automorphism invariance of the slalom value

Direct source: the bounded-name/slalom argument of Jech--Shelah,
Journal of Algebra 182 (1996), pp. 752–754. The explicit Boolean-value
definitions and their Lean proofs below are original transcription (misc).

The arities N and bounds P are arbitrary natural-number sequences. Thus the
growthN/growthP sequences of MaxAtomicityJechShelahTrees can be substituted
without importing that tree construction here. A name is an actual array of
pairwise-disjoint Boolean values whose rows have supremum top. Slaloms have
actual finite rows and the stipulated cardinality bounds.

The proof transports names through an actual Boolean order isomorphism and
reindexes the supremum over names. Equivariance is a conclusion, not a premise.
This file does NOT prove fusion, identify these invariant values with cylinders,
prove rigidity, or supply the final C non-theorem certificate.
No compiler was run by the author; the designated serial checker owns checking.
-/

namespace Classicism.Meta.Research.MaxAtomicitySlalomInvariance

universe u v

/-- A Boolean name for a sequence whose kth value is below N k. Empty entries
are allowed, but each row is a disjoint partition of top. -/
structure BoundedName (N : ℕ → ℕ) (B : Type u) [CompleteBooleanAlgebra B] where
  entry : ∀ k, Fin (N k) → B
  row_disjoint : ∀ k i j, i ≠ j → entry k i ⊓ entry k j = ⊥
  row_cover : ∀ k, (⨆ i : Fin (N k), entry k i) = ⊤

/-- A ground-model slalom, with no Boolean-valued or generic entries. -/
structure Slalom (N P : ℕ → ℕ) where
  entries : ∀ k, Finset (Fin (N k))
  card_le : ∀ k, (entries k).card ≤ P k

variable {N P : ℕ → ℕ}
variable {B : Type u} {C : Type v}
variable [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

theorem BoundedName.ext {x y : BoundedName N B}
    (h : ∀ k i, x.entry k i = y.entry k i) : x = y := by
  cases x with
  | mk xv xd xc =>
    cases y with
    | mk yv yd yc =>
      have hv : xv = yv := funext fun k => funext fun i => h k i
      cases hv
      rfl

/-- Complement preservation follows from uniqueness of Boolean complements. -/
theorem map_compl (e : B ≃o C) (b : B) : e bᶜ = (e b)ᶜ := by
  have h : IsCompl (e b) (e bᶜ) :=
    e.isCompl (isCompl_compl : IsCompl b bᶜ)
  exact h.compl_eq.symm

/-- Applying an order isomorphism to every name value preserves both partition
conditions. In particular no assumption of preserved names is needed. -/
def mapName (e : B ≃o C) (x : BoundedName N B) : BoundedName N C where
  entry k i := e (x.entry k i)
  row_disjoint k i j hij := by
    rw [← e.map_inf, x.row_disjoint k i j hij, e.map_bot]
  row_cover k := by
    calc
      (⨆ i : Fin (N k), e (x.entry k i)) =
          e (⨆ i : Fin (N k), x.entry k i) := (e.map_iSup _).symm
      _ = e ⊤ := congrArg e (x.row_cover k)
      _ = ⊤ := e.map_top

@[simp] theorem mapName_entry (e : B ≃o C) (x : BoundedName N B)
    (k : ℕ) (i : Fin (N k)) :
    (mapName e x).entry k i = e (x.entry k i) := rfl

/-- The actual bijection of names used to reindex the invariant. -/
def mapNameEquiv (e : B ≃o C) : BoundedName N B ≃ BoundedName N C where
  toFun := mapName e
  invFun := mapName e.symm
  left_inv x := by
    apply BoundedName.ext
    intro k i
    exact e.symm_apply_apply (x.entry k i)
  right_inv x := by
    apply BoundedName.ext
    intro k i
    exact e.apply_symm_apply (x.entry k i)

/-- The Boolean value that a fixed slalom captures every coordinate in A. -/
def capture (A : Set ℕ) (x : BoundedName N B) (s : Slalom N P) : B :=
  ⨅ k ∈ A, ⨆ i ∈ s.entries k, x.entry k i

/-- The Boolean value that some ground-model slalom captures the name on A. -/
def cover (P : ℕ → ℕ) (A : Set ℕ) (x : BoundedName N B) : B :=
  ⨆ s : Slalom N P, capture A x s

/-- The supremum, over all bounded names, of failure of slalom coverage. -/
def invariant (N P : ℕ → ℕ) (A : Set ℕ) (B : Type u)
    [CompleteBooleanAlgebra B] : B :=
  ⨆ x : BoundedName N B, (cover P A x)ᶜ

theorem map_capture (e : B ≃o C) (A : Set ℕ)
    (x : BoundedName N B) (s : Slalom N P) :
    e (capture A x s) = capture A (mapName e x) s := by
  simp only [capture, OrderIso.map_iInf, OrderIso.map_iSup, mapName_entry]

theorem map_cover (e : B ≃o C) (P : ℕ → ℕ) (A : Set ℕ)
    (x : BoundedName N B) :
    e (cover P A x) = cover P A (mapName e x) := by
  simp only [cover, OrderIso.map_iSup, map_capture]

/-- This is proved for isomorphisms between different complete Boolean algebras,
not only automorphisms of one algebra. The reindexing step uses the proved
bijection of partition-valued names. -/
theorem map_invariant (e : B ≃o C) (N P : ℕ → ℕ) (A : Set ℕ) :
    e (invariant N P A B) = invariant N P A C := by
  calc
    e (invariant N P A B) =
        ⨆ x : BoundedName N B, (cover P A (mapName e x))ᶜ := by
      simp only [invariant, OrderIso.map_iSup, map_compl, map_cover]
    _ = ⨆ y : BoundedName N C, (cover P A y)ᶜ := by
      apply le_antisymm
      · apply iSup_le
        intro x
        exact le_iSup (fun y : BoundedName N C => (cover P A y)ᶜ) (mapName e x)
      · apply iSup_le
        intro y
        obtain ⟨x, hx⟩ := (mapNameEquiv (N := N) e).surjective y
        have hx' : mapName e x = y := hx
        rw [← hx']
        exact le_iSup (fun z : BoundedName N B => (cover P A (mapName e z))ᶜ) x
    _ = invariant N P A C := rfl

/-- Every actual Boolean order automorphism fixes the slalom invariant. -/
theorem automorphism_fixes_invariant (e : B ≃o B)
    (N P : ℕ → ℕ) (A : Set ℕ) :
    e (invariant N P A B) = invariant N P A B :=
  map_invariant e N P A

end Classicism.Meta.Research.MaxAtomicitySlalomInvariance

#print axioms Classicism.Meta.Research.MaxAtomicitySlalomInvariance.map_compl
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomInvariance.mapNameEquiv
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomInvariance.map_capture
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomInvariance.map_cover
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomInvariance.map_invariant
#print axioms Classicism.Meta.Research.MaxAtomicitySlalomInvariance.automorphism_fixes_invariant
