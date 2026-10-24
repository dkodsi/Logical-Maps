import Erdos501.FOL.Collection

/-!
# Primitive set laws of an actual first-order ZFC model

Every law below is extracted from satisfaction of the corresponding sentence
of `Erdos501.FOL.ZFC`. The only model premise is that actual theory
satisfaction. The carrier may be nonstandard or externally ill founded.

The pair symbol is the source theory's primitive injective pairing operation.
No assertion about its members, and no identification with Kuratowski pairing,
is used. Collection is restricted to actual finite first-order formulas in
the expanded language, with their finite parameter tuples made explicit.
It is not closure under arbitrary externally specified predicates.

The semantic collection equivalence is the imported theorem
`Erdos501.FOL.realize_collectionAxiom`, attributed to Elliot Glazer in the
pinned external source. This module specializes it to actual ZFC models.
-/

open FirstOrder FirstOrder.Language
open Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.SetLaws

universe u

variable {M : Type u} [L.Structure M]

/-- The interpretation of the empty-set symbol. -/
def emptyM : M := Structure.funMap (L := L) Func.emptyset Fin.elim0

/-- The interpretation of the ordered-pair symbol. -/
def pairM (a b : M) : M := Structure.funMap (L := L) Func.pair ![a, b]

/-- The interpretation of the powerset symbol. -/
def powerM (a : M) : M := Structure.funMap (L := L) Func.powerset ![a]

/-- The interpretation of the union symbol. -/
def unionM (a : M) : M := Structure.funMap (L := L) Func.union ![a]

/-- The interpretation of the omega symbol. -/
def omegaM : M := Structure.funMap (L := L) Func.omega Fin.elim0

@[simp] theorem realize_empT {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (empT n).realize v = emptyM := by
  exact congrArg (Structure.funMap (L := L) (M := M) Func.emptyset)
    (Subsingleton.elim _ _)

@[simp] theorem realize_omT {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (omT n).realize v = omegaM := by
  exact congrArg (Structure.funMap (L := L) (M := M) Func.omega)
    (Subsingleton.elim _ _)

@[simp] theorem realize_pairT {n : ℕ} (v : Empty ⊕ Fin n → M) (a b : Tm) :
    (pairT a b n).realize v = pairM ((a n).realize v) ((b n).realize v) :=
  Term.realize_functions_apply₂

@[simp] theorem realize_powT {n : ℕ} (v : Empty ⊕ Fin n → M) (a : Tm) :
    (powT a n).realize v = powerM ((a n).realize v) :=
  Term.realize_functions_apply₁

@[simp] theorem realize_unionT {n : ℕ} (v : Empty ⊕ Fin n → M) (a : Tm) :
    (unionT a n).realize v = unionM ((a n).realize v) :=
  Term.realize_functions_apply₁

/-- The empty-set sentence gives the actual semantic empty set. -/
theorem empty_mem (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    ∀ x : M, ¬ memM x emptyM := by
  have h := hZFC.realize_of_mem axiomOfEmptyset (by simp [Erdos501.FOL.ZFC])
  simpa [axiomOfEmptyset, toSentence, allF, notF, memF, varT,
    Sentence.Realize, Formula.Realize, memM, Fin.snoc] using h

/-- The source's pairing axiom gives exactly ordered-pair injectivity. -/
theorem pair_eq_iff (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    ∀ a b c d : M, pairM a b = pairM c d ↔ a = c ∧ b = d := by
  have h := hZFC.realize_of_mem axiomOfOrderedPairs (by simp [Erdos501.FOL.ZFC])
  simpa [axiomOfOrderedPairs, toSentence, allF, iffF, andF, eqF, varT,
    Sentence.Realize, Formula.Realize, Fin.snoc] using h

theorem pair_injective (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (a b c d : M) (h : pairM a b = pairM c d) : a = c ∧ b = d :=
  (pair_eq_iff hZFC a b c d).mp h

/-- Extensionality applies to all elements of the internal membership universe. -/
theorem ext (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    ∀ x y : M, (∀ z, memM z x ↔ memM z y) → x = y := by
  have h := hZFC.realize_of_mem axiomOfExtensionality (by simp [Erdos501.FOL.ZFC])
  simpa [axiomOfExtensionality, toSentence, allF, impF, iffF, eqF, memF, varT,
    Sentence.Realize, Formula.Realize, memM, Fin.snoc] using h

/-- The interpretation of union has precisely the membership stated by ZFC. -/
theorem union_mem (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    ∀ A x : M, memM x (unionM A) ↔ ∃ y, memM y A ∧ memM x y := by
  have h := hZFC.realize_of_mem axiomOfUnion (by simp [Erdos501.FOL.ZFC])
  simpa [axiomOfUnion, toSentence, allF, exF, iffF, andF, memF, varT,
    Sentence.Realize, Formula.Realize, memM, Fin.snoc] using h

/-- Internal powerset membership; this quantifies over the model's elements. -/
theorem power_mem (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    ∀ A X : M, memM X (powerM A) ↔ ∀ x, memM x X → memM x A := by
  have h := hZFC.realize_of_mem axiomOfPowerset (by simp [Erdos501.FOL.ZFC])
  simpa [axiomOfPowerset, toSentence, allF, iffF, impF, memF, varT,
    Sentence.Realize, Formula.Realize, memM, Fin.snoc] using h

/-- The first conjunct of the actual infinity axiom puts empty inside omega. -/
theorem empty_mem_omega (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    memM (emptyM : M) omegaM := by
  have h := hZFC.realize_of_mem axiomOfInfinity (by simp [Erdos501.FOL.ZFC])
  simp only [axiomOfInfinity, toSentence, andF, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_inf] at h
  simpa [memF, memM] using h.1.1.1

theorem omega_nonempty (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    ∃ x : M, memM x omegaM :=
  ⟨emptyM, empty_mem_omega hZFC⟩

/-- A singleton for coding the empty tuple, constructed as `P(empty)`. -/
def unitSet : M := powerM emptyM

theorem unit_mem (hZFC : M ⊨ Erdos501.FOL.ZFC) (x : M) :
    memM x unitSet ↔ x = emptyM := by
  change memM x (powerM emptyM) ↔ x = emptyM
  rw [power_mem hZFC]
  constructor
  · intro hx
    apply ext hZFC x emptyM
    intro z
    exact ⟨hx z, fun hz => False.elim (empty_mem hZFC z hz)⟩
  · intro hx
    subst x
    exact fun _ hz => hz

/-- The finite collection scheme, in the exact context form of the source
semantic theorem. The last entry of `xs` is the collecting domain. -/
theorem collection (hZFC : M ⊨ Erdos501.FOL.ZFC) (n : ℕ)
    (ψ : L.BoundedFormula Empty (n + 2)) (xs : Fin (n + 1) → M)
    (hserial : ∀ x, memM x (xs (Fin.last n)) →
      ∃ y, ψ.Realize default (Fin.snoc (Fin.snoc (Fin.init xs) x) y)) :
    ∃ v, (∀ x, memM x (xs (Fin.last n)) →
            ∃ y, memM y v ∧
              ψ.Realize default (Fin.snoc (Fin.snoc (Fin.init xs) x) y)) ∧
         (∀ y, memM y v →
            ∃ x, memM x (xs (Fin.last n)) ∧
              ψ.Realize default (Fin.snoc (Fin.snoc (Fin.init xs) x) y)) := by
  have hmem : collectionAxiom n ψ ∈ Erdos501.FOL.ZFC := by
    exact Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨n, Set.mem_range.mpr ⟨ψ, rfl⟩⟩)
  have h := hZFC.realize_of_mem (collectionAxiom n ψ) hmem
  exact (realize_collectionAxiom n ψ).mp h xs hserial

/-- The same finite collection law with parameters and collecting domain
separated, ready for a concrete translated first-order formula. -/
theorem collectionWithParams (hZFC : M ⊨ Erdos501.FOL.ZFC) (n : ℕ)
    (ψ : L.BoundedFormula Empty (n + 2)) (p : Fin n → M) (A : M)
    (hserial : ∀ x, memM x A →
      ∃ y, ψ.Realize default (Fin.snoc (Fin.snoc p x) y)) :
    ∃ B, (∀ x, memM x A →
            ∃ y, memM y B ∧ ψ.Realize default (Fin.snoc (Fin.snoc p x) y)) ∧
         (∀ y, memM y B →
            ∃ x, memM x A ∧ ψ.Realize default (Fin.snoc (Fin.snoc p x) y)) := by
  let xs : Fin (n + 1) → M := Fin.snoc (α := fun _ => M) p A
  have hlast : xs (Fin.last n) = A := by
    simpa only [xs] using
      (Fin.snoc_last (α := fun _ => M) (p := p) (x := A))
  have hinit : Fin.init xs = p := by
    simpa only [xs] using
      (Fin.init_snoc (α := fun _ => M) (p := p) (x := A))
  have hs : ∀ x : M, memM x (xs (Fin.last n)) →
      ∃ y : M, ψ.Realize default (Fin.snoc (Fin.snoc (Fin.init xs) x) y) := by
    simpa only [hlast, hinit] using hserial
  simpa only [hlast, hinit] using collection hZFC n ψ xs hs

#print axioms empty_mem
#print axioms pair_eq_iff
#print axioms pair_injective
#print axioms ext
#print axioms union_mem
#print axioms power_mem
#print axioms empty_mem_omega
#print axioms omega_nonempty
#print axioms unit_mem
#print axioms collection
#print axioms collectionWithParams

end ClassicismZFC.SetLaws
