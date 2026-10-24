import Classicism.Models.BooleanGroundChecks

/-!
# Ground coverage from binary table distributivity

Original formalization (misc), 23 October 2026. Source: section 5 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
These transfer lemmas prove how coverage passes through products and
predicate spaces. The only algebraic premise in the predicate step is the
explicit binary table equation, to be supplied by the concrete column
distributivity theorem at the protected cardinal sizes. There is no
assumed model, comprehension, or separating verdict.
-/

namespace Classicism.Meta.ChoiceBoolean.GroundChecks

variable {K B : Type} [CompleteBooleanAlgebra B] {a : BooleanAction K B}

noncomputable section

open scoped Classical

variable {X Y : ActionSpace a} {G H : Type}

def Covers (c : GroundMap X G) : Prop :=
  ∀ x, (⨆ z : G, X.space.eqv x (c.check z)) = ⊤

theorem crisp_covers (a : BooleanAction K B) (G : Type) : Covers (crisp a G) := by
  intro x
  change G at x
  apply top_le_iff.mp
  apply le_iSup_of_le x
  change ⊤ ≤ (ActionSpace.crisp a G).space.eqv x x
  exact ((ActionSpace.crisp a G).space.refl x).ge

theorem product_covers (c : GroundMap X G) (d : GroundMap Y H)
    (hc : Covers c) (hd : Covers d) : Covers (product c d) := by
  intro x
  apply top_le_iff.mp
  calc
    ⊤ = (⨆ z : G, X.space.eqv x.1 (c.check z)) ⊓
        (⨆ w : H, Y.space.eqv x.2 (d.check w)) := by rw [hc, hd, top_inf_eq]
    _ = ⨆ z : G, ⨆ w : H,
        X.space.eqv x.1 (c.check z) ⊓ Y.space.eqv x.2 (d.check w) := by
      rw [iSup_inf_eq]
      apply iSup_congr
      intro z
      rw [inf_iSup_eq]
    _ ≤ ⨆ p : G × H,
        (ActionSpace.product X Y).space.eqv x ((product c d).check p) := by
      apply iSup_le
      intro z
      apply iSup_le
      intro w
      exact le_iSup_of_le (z, w) le_rfl

/-- Under input coverage, agreement at every checked argument determines
the Boolean equality of arbitrary coherent predicates. -/
theorem predicate_eqv_from_checks (c : GroundMap X G) (hc : Covers c)
    (F H : Predicate X.space) :
    (⨅ z : G, iffValue (F (c.check z)) (H (c.check z))) ≤
      (predicateSpace X.space).eqv F H := by
  let m := ⨅ z : G, iffValue (F (c.check z)) (H (c.check z))
  change m ≤ ⨅ x, iffValue (F x) (H x)
  apply le_iInf
  intro x
  have hz : ∀ z : G, m ⊓ X.space.eqv x (c.check z) ≤ iffValue (F x) (H x) := by
    intro z
    have h₁ : m ⊓ X.space.eqv x (c.check z) ≤ iffValue (F x) (F (c.check z)) :=
      inf_le_right.trans (F.congr x (c.check z))
    have h₂ : m ⊓ X.space.eqv x (c.check z) ≤
        iffValue (F (c.check z)) (H (c.check z)) := inf_le_left.trans (iInf_le _ z)
    have h₃ : m ⊓ X.space.eqv x (c.check z) ≤ iffValue (H (c.check z)) (H x) := by
      rw [X.space.symm x (c.check z)]
      exact inf_le_right.trans (H.congr (c.check z) x)
    exact (le_inf ((le_inf h₁ h₂).trans (iffValue_trans _ _ _)) h₃).trans
      (iffValue_trans _ _ _)
  calc
    m = m ⊓ (⨆ z : G, X.space.eqv x (c.check z)) := by rw [hc, inf_top_eq]
    _ = ⨆ z : G, m ⊓ X.space.eqv x (c.check z) :=
      inf_iSup_eq m (fun z : G => X.space.eqv x (c.check z))
    _ ≤ iffValue (F x) (H x) := iSup_le hz

/-- The explicit small-table distributivity property at a ground index set. -/
def BinaryTables (B G : Type) [CompleteBooleanAlgebra B] : Prop :=
  ∀ f : G → B, (⨆ η : G → Bool, ⨅ z : G, if η z then f z else (f z)ᶜ) = ⊤

theorem predicate_covers (c : GroundMap X G) (hc : Covers c)
    (ht : BinaryTables B G) : Covers (predicate c) := by
  intro F
  apply top_le_iff.mp
  rw [← ht (fun z => Predicate.toFun (X := X.space) F.val (c.check z))]
  apply iSup_le
  intro η
  let g : Set G := {z | η z = true}
  apply le_iSup_of_le g
  change (⨅ z : G, if η z then Predicate.toFun (X := X.space) F.val (c.check z)
      else (Predicate.toFun (X := X.space) F.val (c.check z))ᶜ) ≤
    (predicateSpace X.space).eqv F.val (checkedPredicate c g)
  apply le_trans ?_ (predicate_eqv_from_checks c hc F.val (checkedPredicate c g))
  apply le_iInf
  intro z
  apply (iInf_le _ z).trans
  rw [checkedPredicate_apply_check]
  cases hη : η z <;> simp [g, hη, iffValue]

end

end Classicism.Meta.ChoiceBoolean.GroundChecks
