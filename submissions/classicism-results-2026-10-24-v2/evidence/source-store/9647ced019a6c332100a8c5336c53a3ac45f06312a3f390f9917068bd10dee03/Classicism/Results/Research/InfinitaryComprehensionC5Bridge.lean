import Classicism.Semantics.IntensionalTheory
import Classicism.Results.Research.InfinitaryComprehensionC5Certificates

/-!
# The actual C5 premise in intensional action models

Source: `research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md`,
section 4 (misc, 23 October 2026, unpaginated). This bridge applies the existing
object-language C5 derivations and their intensional soundness theorem. It does
not assume constant domains, full supports, or a canonical representation.

The finite schema ranges over CLOSED object types. `Ty.var` is an auxiliary
metavariable code and is not silently added to that schema. The semantic
Barcan lemmas below are usable at an arbitrary type if its actual BF sentence
is supplied; the C5 corollaries explicitly retain the closed-type proviso.

Source development only: compilation is held at the user's request.
-/

namespace Classicism.Meta.Research.InfinitaryComprehensionC5Bridge

open CategoryTheory Intensional

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C) (M : A.IsModel)

/-- The database's actual C5 schema, read in the model's signature. -/
def C5 : Prop :=
  A.HoldsAx (AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

theorem c5_box_nd (hC5 : C5 A) (σ : Ty) (hσ : σ.Closed) :
    A.HoldsSentence (Term.box (Sentence.nd σ)) := by
  have h := hC5 _
    ⟨Classicism.P.NecNecessityOfDistinctness.quoted σ, ⟨σ, hσ, rfl⟩, rfl⟩
  change A.HoldsSentence (Term.box (Sentence.nd σ)) at h
  exact h

-- The following semantic consequences use the already stated model laws.
include M

theorem c5_nd (hC5 : C5 A) (σ : Ty) (hσ : σ.Closed) :
    A.HoldsSentence (Sentence.nd σ) :=
  A.holdsSentence_of_box M (c5_box_nd A hC5 σ hσ)

theorem c5_bf (hC5 : C5 A) (σ : Ty) (hσ : σ.Closed) :
    A.HoldsSentence (Sentence.bf σ) := by
  have hPure : A.reduct.HoldsAx Classicism.P.NecNecessityOfDistinctness.schema :=
    (A.holdsAx_ofPure _).1 hC5
  have hBF := A.reduct.entails_holds (A.reduct_isModel M)
    Classicism.Proofs.necessary_nd_implies_bf.entails hPure
  have h := (A.holdsSentence_ofPure (Classicism.P.Barcan.quoted σ)).2
    (hBF _ ⟨σ, hσ, rfl⟩)
  change A.HoldsSentence (Sentence.bf σ) at h
  exact h

theorem c5_box_bf (hC5 : C5 A) (σ : Ty) (hσ : σ.Closed) :
    A.HoldsSentence (Term.box (Sentence.bf σ)) := by
  have hPure : A.reduct.HoldsAx Classicism.P.NecNecessityOfDistinctness.schema :=
    (A.holdsAx_ofPure _).1 hC5
  have hBF := A.reduct.entails_holds (A.reduct_isModel M)
    Classicism.Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r.entails
    hPure
  have h := (A.holdsSentence_ofPure (Classicism.P.NecBarcan.quoted σ)).2
    (hBF _ ⟨σ, hσ, rfl⟩)
  change A.HoldsSentence (Term.box (Sentence.bf σ)) at h
  exact h

/-- Boxed ND supplies injectivity at every reachable object, not just the root. -/
theorem c5_map_injective (hC5 : C5 A) (σ : Ty) (hσ : σ.Closed)
    {W V : C} (h : A.W₀ ⟶ W) (k : W ⟶ V) :
    Function.Injective ((A.inner σ).map k) := by
  have hn := (A.holds_box M (𝟙 A.W₀) (Sentence.nd σ) .nil).1
    (c5_box_nd A hC5 σ hσ) h
  rw [Category.id_comp, IEnv.nil_eq (A.push h IEnv.nil)] at hn
  exact (A.holds_nd_iff M σ h).1 hn k

theorem c5_bf_at (hC5 : C5 A) (σ : Ty) (hσ : σ.Closed)
    {W : C} (h : A.W₀ ⟶ W) : A.Holds h (Sentence.bf σ) .nil := by
  have hb := (A.holds_box M (𝟙 A.W₀) (Sentence.bf σ) .nil).1
    (c5_box_bf A M hC5 σ hσ) h
  rw [Category.id_comp, IEnv.nil_eq (A.push h IEnv.nil)] at hb
  exact hb

/-- The concrete BF reading for an admitted predicate. This uses the actual
finite sentence and the existing semantic quantifier and box clauses. -/
theorem barcan_profile {σ : Ty} {W : C} (h : A.W₀ ⟶ W)
    (hBF : A.Holds h (Sentence.bf σ) .nil)
    (X : A.Dom W (.rel (σ ⇒ RTy.t)))
    (hall : ∀ (y : A.Dom W σ) {V : C} (k : W ⟶ V),
      (⟨V, ((A.inner σ).map k y, PUnit.unit), k⟩ :
        Tuple A.inner (σ ⇒ RTy.t) W) ∈ A.incl _ W X)
    {V : C} (k : W ⟶ V) (x : A.Dom V σ) :
    (⟨V, (x, PUnit.unit), k⟩ : Tuple A.inner (σ ⇒ RTy.t) W) ∈
      A.incl _ W X := by
  classical
  by_contra hn
  exact A.not_holds_bf_of M h X hall k x hn hBF

/-- Once the named-range matrix has an admitted representative, BF forces
every future object into that range. The infinitary syntax construction
supplies the representative separately; this lemma does not assume fullness. -/
theorem map_surjective_of_represented_range {σ : Ty} {W : C}
    (h : A.W₀ ⟶ W) (hBF : A.Holds h (Sentence.bf σ) .nil)
    (X : A.Dom W (.rel (σ ⇒ RTy.t)))
    (hX : ∀ {V : C} (k : W ⟶ V) (x : A.Dom V σ),
      ((⟨V, (x, PUnit.unit), k⟩ : Tuple A.inner (σ ⇒ RTy.t) W) ∈
        A.incl _ W X) ↔ ∃ y : A.Dom W σ, (A.inner σ).map k y = x)
    {V : C} (k : W ⟶ V) : Function.Surjective ((A.inner σ).map k) := by
  intro x
  exact (hX k x).1 (barcan_profile A M h hBF X
    (fun y _ l => (hX l _).2 ⟨y, rfl⟩) k x)

theorem c5_map_bijective_of_represented_range (hC5 : C5 A)
    (σ : Ty) (hσ : σ.Closed) {W : C} (h : A.W₀ ⟶ W)
    (X : A.Dom W (.rel (σ ⇒ RTy.t)))
    (hX : ∀ {V : C} (k : W ⟶ V) (x : A.Dom V σ),
      ((⟨V, (x, PUnit.unit), k⟩ : Tuple A.inner (σ ⇒ RTy.t) W) ∈
        A.incl _ W X) ↔ ∃ y : A.Dom W σ, (A.inner σ).map k y = x)
    {V : C} (k : W ⟶ V) : Function.Bijective ((A.inner σ).map k) :=
  ⟨c5_map_injective A M hC5 σ hσ h k,
    map_surjective_of_represented_range A M h (c5_bf_at A M hC5 σ hσ h) X hX k⟩

end Classicism.Meta.Research.InfinitaryComprehensionC5Bridge
