import Classicism.Models.NominalOrbitShift
import Mathlib.Data.Finite.Defs

/-!
# Finite fixed-support strata preclude supported Dedekind operations

This is the converse proof's iterate argument, for the actual supported function
domain. The finiteness of each fixed-support stratum is an EXPLICIT premise;
the separate Sym(A) orbit-finiteness theorem needed to establish it remains an
obligation. This module does not label that missing orbit theorem proved.

Source: nominal-choice-classification-20261022.md §6, original local research,
unpaginated, misc. Ordinary metatheory; uncompiled candidate.
-/

namespace Classicism.Meta.Nominal
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}

def iterateFrom {E : Type} (f : E → E) (r : E) : Nat → E
  | 0 => r
  | n + 1 => f (iterateFrom f r n)

theorem iterateFrom_injective {E : Type} (f : E → E) (hf : Function.Injective f)
    (r : E) (hr : ∀ x, f x ≠ r) : Function.Injective (iterateFrom f r) := by
  intro n
  induction n with
  | zero =>
    intro m he
    cases m with
    | zero => rfl
    | succ m => exact False.elim (hr _ he.symm)
  | succ n ih =>
    intro m he
    cases m with
    | zero => exact False.elim (hr _ he)
    | succ m => exact congrArg Nat.succ (ih (hf he))

theorem iterate_supported (X : Nom A I) {S : Set A} (f : exponential X X)
    (hf : Supports A (exponential X X).obj S f) (r : X) (hr : Supports A X.obj S r) :
    ∀ n, Supports A X.obj S (iterateFrom f.val r n)
  | 0 => hr
  | n + 1 => by
    intro g hg
    have he := exponential_covariance X X hf g hg (iterateFrom f.val r n)
    rw [iterate_supported X f hf r hr n g hg] at he
    exact he.symm

theorem no_dedekind_of_finite_strata (X : Nom A I)
    (hfinite : ∀ S : Set A, I.Small S → Finite {x : X // Supports A X.obj S x}) :
    ¬∃ f : exponential X X, Function.Injective f.val ∧ ∃ r : X, ∀ x, f.val x ≠ r := by
  rintro ⟨f, hf, r, hr⟩
  obtain ⟨S, hS, hs⟩ := (exponential X X).supported f
  obtain ⟨T, hT, ht⟩ := X.supported r
  have hfs : Supports A (exponential X X).obj (S ∪ T) f :=
    supports_mono A _ (fun _ h => Or.inl h) hs
  have hrs : Supports A X.obj (S ∪ T) r :=
    supports_mono A _ (fun _ h => Or.inr h) ht
  let j : Nat → {x : X // Supports A X.obj (S ∪ T) x} :=
    fun n => ⟨iterateFrom f.val r n, iterate_supported X f hfs r hrs n⟩
  have hj : Function.Injective j := fun _ _ h =>
    iterateFrom_injective f.val hf r hr (congrArg Subtype.val h)
  letI : Finite {x : X // Supports A X.obj (S ∪ T) x} := hfinite _ (I.union hS hT)
  haveI : Finite Nat := Finite.of_injective j hj
  exact not_finite Nat

theorem Hierarchy.not_dedInfT_of_finite_strata (W : Nom A I)
    (hfinite : ∀ S : Set A, I.Small S →
      Finite {p : propositions W // Supports A (propositions W).obj S p}) (w : W) :
    ¬Hierarchy.Holds W (Hierarchy.pureConstants W) () w Hierarchy.dedInfT := by
  rw [Hierarchy.dedInfT_iff]
  exact no_dedekind_of_finite_strata (propositions W) hfinite

end
end Classicism.Meta.Nominal
