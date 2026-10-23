import Classicism.Results.Research.MaxAtomicityHCodeExistence
import Classicism.Results.Research.MaxAtomicitySetFormulaTools

/-!
# Every successful universe code has the same interpretation

Direct source: the original HCode argument, section 3 of
`max-atomicity-inconsistency-proof.md` (misc, unpaginated).

The map to the hereditary universe is the actual Mostowski collapse. Small
rows and filling prove its range is precisely the already-constructed universe
set. This gives an actual equivalence with the fixed presentation on B → B,
preserving membership in both directions. Structural induction then proves
invariance of every finite membership formula under that equivalence.

No formula-adequacy axiom, assumed collapse or assumed uniqueness of good codes
is introduced. Concrete definitions of the intended JS algebra in this language
are still needed. Source awaits the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityHCodeCharacterization

open BooleanValued MaxAtomicitySyntax MaxAtomicitySetSyntax MaxAtomicitySetSemantics
open MaxAtomicityHCodeSemantics MaxAtomicityHereditaryUniverse

noncomputable section

variable {B : Type} [CompleteBooleanAlgebra B] [Nontrivial B] [Infinite B]

private theorem good_rows (R : (B → B) → (B → B) → Prop) (h : GoodRelation (B := B) R) :
    MaxAtomicityHereditaryCover.RowsSmall B R :=
  fun x => (small_iff_embedding (fun y => R y x)).1 (h.2 x)

private theorem good_fills (R : (B → B) → (B → B) → Prop) (h : GoodRelation (B := B) R) :
    MaxAtomicityHereditaryCover.FillsSmall B R := by
  intro X hX
  exact h.1.2.2 X ((small_iff_embedding X).2 hX)

/-- The target of every successful collapse is literally the same set. -/
theorem good_collapseRange (R : (B → B) → (B → B) → Prop)
    (h : GoodRelation (B := B) R) :
    MaxAtomicityMostowski.collapseRange h.1.2.1 = universeSet B := by
  apply ZFSet.ext
  intro z
  rw [MaxAtomicityHereditaryCover.mem_range_iff_hereditarilySmall B h.1.2.1
      h.1.1 (good_rows R h) (good_fills R h), mem_universeSet]

def collapseIntoUniverse (R : (B → B) → (B → B) → Prop)
    (h : GoodRelation (B := B) R) (x : B → B) : (universeSet B : Set ZFSet.{0}) :=
  ⟨MaxAtomicityMostowski.collapse h.1.2.1 x, by
    rw [← good_collapseRange R h]
    exact (MaxAtomicityMostowski.mem_collapseRange h.1.2.1 _).2 ⟨x, rfl⟩⟩

theorem collapseIntoUniverse_bijective (R : (B → B) → (B → B) → Prop)
    (h : GoodRelation (B := B) R) : Function.Bijective (collapseIntoUniverse R h) := by
  constructor
  · intro x y hxy
    exact MaxAtomicityMostowski.collapse_injective h.1.2.1 h.1.1 (congrArg Subtype.val hxy)
  · intro z
    have hz : z.1 ∈ MaxAtomicityMostowski.collapseRange h.1.2.1 := by
      rw [good_collapseRange R h]
      exact z.2
    obtain ⟨x, hx⟩ := (MaxAtomicityMostowski.mem_collapseRange h.1.2.1 z.1).1 hz
    exact ⟨x, Subtype.ext hx⟩

def collapseEquiv (R : (B → B) → (B → B) → Prop)
    (h : GoodRelation (B := B) R) : (B → B) ≃ (universeSet B : Set ZFSet.{0}) :=
  Equiv.ofBijective (collapseIntoUniverse R h) (collapseIntoUniverse_bijective R h)

/-- Change from any successful code to the concrete canonical presentation. -/
def canonicalChange (R : (B → B) → (B → B) → Prop)
    (h : GoodRelation (B := B) R) : (B → B) ≃ (B → B) :=
  (collapseEquiv R h).trans (presentationEquiv B).symm

theorem present_canonicalChange (R : (B → B) → (B → B) → Prop)
    (h : GoodRelation (B := B) R) (x : B → B) :
    present B (canonicalChange R h x) = MaxAtomicityMostowski.collapse h.1.2.1 x :=
  congrArg Subtype.val ((presentationEquiv B).apply_symm_apply (collapseEquiv R h x))

theorem canonicalChange_membership (R : (B → B) → (B → B) → Prop)
    (h : GoodRelation (B := B) R) (x y : B → B) :
    R x y ↔ codeRelation B (canonicalChange R h x) (canonicalChange R h y) := by
  change R x y ↔ present B (canonicalChange R h x) ∈ present B (canonicalChange R h y)
  rw [present_canonicalChange, present_canonicalChange]
  exact (MaxAtomicityMostowski.collapse_mem_iff h.1.2.1 h.1.1 x y).symm

private theorem map_cases {D D' : Type} (e : D ≃ D') {n : Nat}
    (ρ : Fin n → D) (x : D) :
    (fun i => e (Fin.cases x ρ i)) = Fin.cases (e x) (fun i => e (ρ i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- The proof is induction on the actual finite syntax, with surjectivity
explicitly used at both quantifiers. -/
theorem satisfies_equiv {D D' : Type} (R : D → D → Prop) (R' : D' → D' → Prop)
    (e : D ≃ D') (he : ∀ x y, R x y ↔ R' (e x) (e y)) {n : Nat}
    (φ : SetFormula n) : ∀ ρ : Fin n → D,
      satisfies φ R ρ ↔ satisfies φ R' (fun i => e (ρ i)) := by
  induction φ with
  | bot => intro ρ; rfl
  | top => intro ρ; rfl
  | eq i j => intro ρ; exact e.injective.eq_iff.symm
  | mem i j => intro ρ; exact he (ρ i) (ρ j)
  | neg p ih => intro ρ; exact not_congr (ih ρ)
  | conj p q ihp ihq => intro ρ; exact and_congr (ihp ρ) (ihq ρ)
  | disj p q ihp ihq => intro ρ; exact or_congr (ihp ρ) (ihq ρ)
  | imp p q ihp ihq => intro ρ; exact imp_congr (ihp ρ) (ihq ρ)
  | iff p q ihp ihq => intro ρ; exact iff_congr (ihp ρ) (ihq ρ)
  | all p ih =>
    intro ρ
    change (∀ x : D, satisfies p R (Fin.cases x ρ)) ↔
      ∀ y : D', satisfies p R' (Fin.cases y (fun i => e (ρ i)))
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := e.surjective y
      simpa only [map_cases] using (ih (Fin.cases x ρ)).1 (h x)
    · intro h x
      apply (ih (Fin.cases x ρ)).2
      simpa only [map_cases] using h (e x)
  | ex p ih =>
    intro ρ
    change (∃ x : D, satisfies p R (Fin.cases x ρ)) ↔
      ∃ y : D', satisfies p R' (Fin.cases y (fun i => e (ρ i)))
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨e x, by simpa only [map_cases] using (ih (Fin.cases x ρ)).1 hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨x, (ih (Fin.cases x ρ)).2 (by simpa only [map_cases] using hy)⟩

theorem satisfies_canonicalChange (R : (B → B) → (B → B) → Prop)
    (h : GoodRelation (B := B) R) {n : Nat} (φ : SetFormula n) (ρ : Fin n → (B → B)) :
    satisfies φ R ρ ↔
      satisfies φ (codeRelation B) (fun i => canonicalChange R h (ρ i)) :=
  satisfies_equiv R (codeRelation B) (canonicalChange R h) (canonicalChange_membership R h) φ ρ

/-- Exact semantics of every translated membership formula under a good code,
now evaluated in the one fixed canonical presentation. -/
theorem eval_translate_canonical (I : Interpretation Signature.pure B)
    {Γ : Ctx} (E : PT Γ ER) (env : IEnv (Dom I.E B) Γ)
    (R : (B → B) → (B → B) → Prop) (h : GoodRelation (B := B) R)
    (hE : ∀ x y, eval I E env x y = truth (R x y))
    {n : Nat} (φ : SetFormula n) (ρ : Fin n → PT Γ U) :
    eval I (translate φ E ρ) env =
      truth (satisfies φ (codeRelation B)
        (fun i => canonicalChange R h (eval I (ρ i) env))) := by
  rw [eval_translate I φ R E ρ env hE]
  exact congrArg (fun P : Prop => (truth P : B))
    (propext (satisfies_canonicalChange R h φ (fun i => eval I (ρ i) env)))

end

end Classicism.Meta.Research.MaxAtomicityHCodeCharacterization

#print axioms Classicism.Meta.Research.MaxAtomicityHCodeCharacterization.good_collapseRange
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeCharacterization.collapseIntoUniverse_bijective
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeCharacterization.canonicalChange_membership
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeCharacterization.satisfies_equiv
#print axioms Classicism.Meta.Research.MaxAtomicityHCodeCharacterization.eval_translate_canonical
