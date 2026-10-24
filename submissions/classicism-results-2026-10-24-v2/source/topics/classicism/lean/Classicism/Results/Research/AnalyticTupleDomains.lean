import Classicism.Comprehension

/-!
# Adding one coordinate to an internal tuple domain

Supporting C-minus proof for the represented-powers construction in Zachary
Goodsell / Claude Fable 5.1 (Anthropic), 23 October 2026,
`c5-and-necessary-rigid-comprehension-imply-second-order-analytic-necessitism`,
"Represented powers" (unpaginated). The finite-arity recursion is metalinguistic
and lives in the companion Meta module; no tuple object or type quantifier is
introduced into C.
-/

namespace Classicism.Research.Analytic

variable {σ : Type} [Ty σ] {ρ : Type} [Rel ρ] [Pointwise ρ]

/-- Add an outer coordinate to the curried relation `D`. -/
def AppendCoordinate (X : σ → Prop) (D : ρ) : σ → ρ :=
  fun x => Rel.and D (constP (X x))

theorem append_coordinate_weakly_persistent (X : σ → Prop) (D : ρ)
    (hX : WeaklyPersistent X) (hD : WeaklyPersistent D) :
    WeaklyPersistent (AppendCoordinate X D) := by
  intro x
  apply (em (X x)).elim
  · intro hx
    have he : Rel.and D (constP (X x)) = D :=
      (congrArg (fun p : Prop => Rel.and D (constP p)) (hX x hx)).trans
        (Rel.and_constP_true D)
    exact Eq.mpr (congrArg (fun Y : ρ => WeaklyPersistent Y) he) hD
  · intro hn
    exact incl_trans (Rel.and D (constP (X x))) (constP (X x))
      (boxAt (Rel.and D (constP (X x)))) (incl_and_right D (constP (X x)))
      (incl_of_constP _ _ hn)

/-- Persistence is preserved on appending a coordinate; only C-minus is used. -/
theorem append_coordinate_persistent (X : σ → Prop) (D : ρ)
    (hX : Persistent X) (hD : Persistent D) :
    Persistent (AppendCoordinate X D) :=
  modal_K _ _ (modal_K _ _ (nec% (append_coordinate_weakly_persistent X D)) hX) hD

/-- The empty tuple's domain is the true proposition. -/
theorem empty_domain_persistent : Persistent True :=
  nec% (fun (_ : True) => (show □ True from box_true))

end Classicism.Research.Analytic
