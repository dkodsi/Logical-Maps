import Classicism.Semantics.FullExtensionalProperties
import Classicism.Models.SinglePredicateFull
import Lean.Elab.Tactic.Omega

/-!
# Infinity in the concrete one-world models

The first obstruction is the n=3 sentence of the actual Infinity schema. The
second interprets the actual generated quantified Frege Infinity sentences,
including their impredicative FiniteCardinality predicate. Thus finite domains
are not connected to C merely by assuming an external Fintype bridge.

Source: central-questions-audit.md, "Other verified properties" and rows under
C5+Atomicity and Extensionalism (original research, unpaginated, misc).
All induction and arithmetic below are ordinary external metatheory.
-/

namespace Classicism.Meta.FullExtensional
noncomputable section
open SinglePredicateFull

def countThree {Sig : Signature} (σ : Ty) : Sentence Sig :=
  Term.existsBlock (List.replicate 3 σ) (Term.distinct 3 (Terms.vars _ []))

theorem countThree_mem {Sig : Signature} (σ : Ty) :
    AxiomSet.infinitySchema Sig σ (countThree σ) := ⟨3, by omega, rfl⟩

theorem countThree_iff {Sig : Signature} (I : Interp Sig) (σ : Ty) :
    (countThree σ).holds I ↔ ∃ x y z : σ.denote I.D, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  change (∃ x y z : σ.denote I.D,
    (x ≠ y ∧ (x ≠ z ∧ ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q))) ∧
    ((y ≠ z ∧ ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q)) ∧
      (((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q) ∧
       ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q)))) ↔ _
  simp only [top_eq, and_true, and_assoc]

theorem bool_not_countThree_e : ¬ (countThree Ty.e).holds boolModel := by
  rw [countThree_iff]
  rintro ⟨x, y, z, hxy, hxz, hyz⟩
  cases x <;> cases y <;> cases z <;> simp_all

theorem prop_two_values (p : Prop) : p = True ∨ p = False :=
  (Classical.em p).elim
    (fun h => Or.inl (propext ⟨fun _ => True.intro, fun _ => h⟩))
    (fun h => Or.inr (propext ⟨h, False.elim⟩))

theorem not_countThree_t {Sig : Signature} (I : Interp Sig) :
    ¬ (countThree Ty.t).holds I := by
  rw [countThree_iff]
  rintro ⟨p, q, r, hpq, hpr, hqr⟩
  rcases prop_two_values p with rfl | rfl <;>
    rcases prop_two_values q with rfl | rfl <;>
    rcases prop_two_values r with rfl | rfl <;> simp_all

theorem bool_not_infinitySchema_e : ¬ (AxiomSet.infinityE signature).holds boolModel :=
  fun h => bool_not_countThree_e (h _ (countThree_mem Ty.e))

theorem not_infinitySchema_t {Sig : Signature} (I : Interp Sig) :
    ¬ (AxiomSet.infinityT Sig).holds I :=
  fun h => not_countThree_t I (h _ (countThree_mem Ty.t))

def Zero (A : Type) : (A → Prop) → Prop := fun X => ∀ x, ¬ X x
def Succ {A : Type} (Z : (A → Prop) → Prop) : (A → Prop) → Prop :=
  fun X => ∃ y, X y ∧ Z (fun x => X x ∧ x ≠ y)
def FiniteCard {A : Type} (Z : (A → Prop) → Prop) : Prop :=
  ∀ W : ((A → Prop) → Prop) → Prop, (W (Zero A) ∧ ∀ Y, W Y → W (Succ Y)) → W Z

theorem finite_zero (A : Type) : FiniteCard (Zero A) := fun _ h => h.1
theorem finite_succ {A : Type} {Z : (A → Prop) → Prop} (hZ : FiniteCard Z) :
    FiniteCard (Succ Z) := fun W h => h.2 Z (hZ W h)

theorem two_counts_cover {A : Type} (a b : A) (hba : b ≠ a)
    (hcover : ∀ x : A, x = a ∨ x = b) : Succ (Succ (Zero A)) (fun _ => True) := by
  refine ⟨a, True.intro, b, ⟨True.intro, hba⟩, ?_⟩
  intro x hx
  exact (hcover x).elim (fun he => hx.1.2 he) (fun he => hx.2 he)

/-- Direct interpretation of the generated quantified sentence, including its
impredicative finite-cardinality clause. -/
theorem infinityE_iff {Sig : Signature} (I : Interp Sig) :
    Sentence.holds I (Term.ofPure P.AxiomOfInfinityE.quoted) ↔
      ¬ ∃ Z : (I.D → Prop) → Prop, FiniteCard Z ∧ Z (fun _ => True) := by
  simp only [P.AxiomOfInfinityE.quoted, Term.ofPure, Sentence.holds, Term.denote,
    Var.denote, imp_eq, top_eq, FiniteCard, Zero, Succ]

theorem infinityT_iff {Sig : Signature} (I : Interp Sig) :
    Sentence.holds I (Term.ofPure P.AxiomOfInfinityT.quoted) ↔
      ¬ ∃ Z : (Prop → Prop) → Prop, FiniteCard Z ∧ Z (fun _ => True) := by
  simp only [P.AxiomOfInfinityT.quoted, Term.ofPure, Sentence.holds, Term.denote,
    Var.denote, imp_eq, top_eq, FiniteCard, Zero, Succ]

theorem bool_not_quantifiedInfinity_e :
    ¬ Sentence.holds boolModel (Term.ofPure P.AxiomOfInfinityE.quoted) := by
  rw [infinityE_iff]
  intro h
  apply h
  refine ⟨Succ (Succ (Zero Bool)), finite_succ (finite_succ (finite_zero Bool)), ?_⟩
  apply two_counts_cover false true (by intro h; cases h)
  intro x
  cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem not_quantifiedInfinity_t {Sig : Signature} (I : Interp Sig) :
    ¬ Sentence.holds I (Term.ofPure P.AxiomOfInfinityT.quoted) := by
  rw [infinityT_iff]
  intro h
  apply h
  refine ⟨Succ (Succ (Zero Prop)), finite_succ (finite_succ (finite_zero Prop)), ?_⟩
  exact two_counts_cover True False (fun he => Eq.mpr he True.intro) prop_two_values

/-- Every interpreted finite cardinality counts only bounded subsets of Nat. -/
theorem finite_nat_bounded {Z : (Nat → Prop) → Prop} (hZ : FiniteCard Z) :
    ∀ X, Z X → ∃ N, ∀ x, X x → x < N := by
  classical
  apply hZ (fun Y => ∀ X, Y X → ∃ N, ∀ x, X x → x < N)
  constructor
  · intro X hX
    exact ⟨0, fun x hx => (hX x hx).elim⟩
  · intro Y hY X hX
    obtain ⟨y, hy, hrest⟩ := hX
    obtain ⟨N, hN⟩ := hY (fun x => X x ∧ x ≠ y) hrest
    refine ⟨N + y + 1, ?_⟩
    intro x hx
    by_cases he : x = y
    · omega
    · have hb := hN x ⟨hx, he⟩
      omega

theorem nat_quantifiedInfinity_e :
    Sentence.holds natModel (Term.ofPure P.AxiomOfInfinityE.quoted) := by
  rw [infinityE_iff]
  rintro ⟨Z, hZ, htop⟩
  obtain ⟨N, hN⟩ := finite_nat_bounded hZ (fun _ => True) htop
  exact Nat.lt_irrefl N (hN N True.intro)

end
end Classicism.Meta.FullExtensional
