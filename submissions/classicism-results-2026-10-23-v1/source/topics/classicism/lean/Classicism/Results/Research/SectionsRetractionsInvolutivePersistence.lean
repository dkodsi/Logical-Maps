import Classicism.Results.Research.SectionsRetractionsRelationalMasks

/-!
# Persistence of involutivity characterizes relational Barcan

Direct source: `research/2026-10-22/notes/reversible-comprehension-and-algebraic-laws.md`,
§2 (misc; original research, 22 October 2026; unpaginated).
The mask is currently the identity. Necessary involutivity makes it necessarily
surjective, which is the already verified mask obstruction to failure of BF.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def InvolutiveOperation {A : Type} [Rel A] (f : A → A) : Prop := ∀ x, f (f x) = x
def InvolutivityPersists (A : Type) [Rel A] : Prop :=
  ∀ f : A → A, InvolutiveOperation f → □ (InvolutiveOperation f)

theorem involution_surjective {A : Type} [Rel A] (f : A → A) :
    InvolutiveOperation f → Surjective f := fun hi y => ⟨f y, hi y⟩

theorem relational_barcan_involutivity {A : Type} [Rel A] :
    BarcanRelational A → InvolutivityPersists A :=
  fun bf f hi => bf (fun x => f (f x) = x)
    (fun x => necessity_of_identity _ _ (hi x))

theorem involutivity_relational_barcan {ν : Type} [Ty ν] :
    Existence ν → InvolutivityPersists (Prop → ν → Prop) →
      BarcanRelational (ν → Prop) := by
  intro hex ip P hp
  obtain ⟨u, _⟩ := hex
  have hi : InvolutiveOperation (mask P) := fun H =>
    (mask_identity P hp (mask P H)).trans (mask_identity P hp H)
  have hs : □ (Surjective (mask P)) :=
    modal_K _ _ (nec% (involution_surjective (mask P))) (ip (mask P) hi)
  exact modal_K _ _ (nec% (mask_surjective_all u P)) hs

end Classicism.Research.Splitting
