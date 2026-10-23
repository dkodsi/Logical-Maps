import Classicism.Results.Research.SectionsRetractionsInvolutions
import Classicism.Results.Research.SectionsRetractionsRelationalMasks

/-!
# Persistence of idempotence characterizes relational Barcan

Direct source: `research/2026-10-22/notes/reversible-comprehension-and-algebraic-laws.md`,
§2 (misc; original research, 22 October 2026; unpaginated).
The toggle is always an involution and is currently the identity under the BF
antecedent. Persistent idempotence then forces its future identity equation.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def IdempotentOperation {A : Type} [Rel A] (f : A → A) : Prop := ∀ x, f (f x) = f x
def IdempotencePersists (A : Type) [Rel A] : Prop :=
  ∀ f : A → A, IdempotentOperation f → □ (IdempotentOperation f)

def toggleMask {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (H : Prop → ν → Prop) (r : Prop) : ν → Prop :=
  xorOutput (H r) (fun _ => r = True ∧ ¬ P (H False))

theorem toggleMask_false {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (H : Prop → ν → Prop) : toggleMask P H False = H False :=
  funext fun u => propext
    ⟨fun h => h.elim And.left (fun h => (Eq.mpr h.2.1 trivial).elim),
     fun h => Or.inl ⟨h, fun h' => Eq.mpr h'.1 trivial⟩⟩

theorem toggleMask_twice {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (H : Prop → ν → Prop) : toggleMask P (toggleMask P H) = H := by
  apply funext
  intro r
  change xorOutput (toggleMask P H r)
    (fun _ => r = True ∧ ¬ P (toggleMask P H False)) = H r
  rw [toggleMask_false]
  exact xorOutput_twice (H r) (fun _ => r = True ∧ ¬ P (H False))

theorem toggleMask_coext {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (H : Prop → ν → Prop) : P (H False) → toggleMask P H ≡ H :=
  fun hp r u =>
    ⟨fun h => h.elim And.left (fun h => (h.2.2 hp).elim),
     fun h => Or.inl ⟨h, fun h' => h'.2 hp⟩⟩

theorem toggleMask_identity {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (hp : ∀ q, □ (P q)) (H : Prop → ν → Prop) : toggleMask P H = H :=
  intensionality _ _ (modal_K _ _ (nec% (toggleMask_coext P H)) (hp (H False)))

theorem toggleMask_slots_top {ν : Type} [Ty ν] (P : (ν → Prop) → Prop)
    (q : ν → Prop) : toggleMask P (slots q (fun _ => False)) True = (fun _ => ¬ P q) := by
  change xorOutput (slots q (fun _ => False) True)
    (fun _ => True = True ∧ ¬ P (slots q (fun _ => False) False)) = (fun _ => ¬ P q)
  rw [slots_true, slots_false, xorOutput_zero]
  exact funext fun _ => propext ⟨And.right, fun h => ⟨rfl, h⟩⟩

theorem toggleMask_idempotent_all {ν : Type} [Ty ν] (u : ν)
    (P : (ν → Prop) → Prop) : IdempotentOperation (toggleMask P) → ∀ q, P q := by
  intro hi q
  let H := slots q (fun _ => False)
  have he : toggleMask P H = H := (hi H).symm.trans (toggleMask_twice P H)
  have ht : (fun _ : ν => ¬ P q) = (fun _ => False) :=
    (toggleMask_slots_top P q).symm.trans
      ((congrFun he True).trans (slots_true q (fun _ => False)))
  have hn : (¬ P q) = False := congrFun ht u
  exact (em (P q)).elim id (fun h => (Eq.mp hn h).elim)

theorem relational_barcan_idempotence {A : Type} [Rel A] :
    BarcanRelational A → IdempotencePersists A :=
  fun bf f hi => bf (fun x => f (f x) = f x)
    (fun x => necessity_of_identity _ _ (hi x))

theorem idempotence_relational_barcan {ν : Type} [Ty ν] :
    Existence ν → IdempotencePersists (Prop → ν → Prop) →
      BarcanRelational (ν → Prop) := by
  intro hex ip P hp
  obtain ⟨u, _⟩ := hex
  have hi : IdempotentOperation (toggleMask P) := fun H =>
    toggleMask_identity P hp (toggleMask P H)
  exact modal_K _ _ (nec% (toggleMask_idempotent_all u P)) (ip (toggleMask P) hi)

end Classicism.Research.Splitting
