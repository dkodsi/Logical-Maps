import Classicism.Semantics.Research.CentralSupportedProductNegative

/-!
# Complete-entity gluing in the countably supported product

Source: new research `followup/central-map.md`, §2. The entire transported
intension equals the selected witness, including its values on future arrows
and arbitrary argument tuples. No syntactic or model-existence assumption is
used. Countability is a condition on the indexing alphabet, not on domains.
Uncompiled author draft, 22 October 2026.
-/

namespace Classicism.Meta.Intensional.Central.Product
open CategoryTheory

variable (L : Type)

theorem last_letter_unique {u v : Word L} {a b : L}
    (h : u * Word.of a = v * Word.of b) : a = b := by
  have e := congrArg (fun w : Word L => (Word.toList w).reverse.head?) h
  simpa using e

def glueRaw {ρ : RTy} (j : Set Nat)
    (F : L → (domain (Set Nat) L (.rel ρ)).obj (star (Set Nat) L)) :
    raw (Set Nat) L ρ (star (Set Nat) L) :=
  {z | ∃ (a : L) (u : Word L), z.2.2 j = u * Word.of a ∧ z ∈ (F a).1}

theorem glueRaw_supported {ρ : RTy} (j : Set Nat)
    (F : L → (domain (Set Nat) L (.rel ρ)).obj (star (Set Nat) L))
    (S : L → Set (Set Nat)) (hS : ∀ a, ProfileSupport (Set Nat) L (S a) (F a).1)
    {T : Set (Set Nat)} (hT : T.Countable) (hST : ∀ a, S a ⊆ T) :
    Supported (control (Set Nat) L) (intensionAction (arguments (Set Nat) L ρ))
      (glueRaw L j F) := by
  apply supported_of_profile (Set Nat) L (hT.insert j)
  intro V x h k hk
  have hj : h j = k j := hk j (Set.mem_insert j T)
  have hf (a : L) := hS a V x h k (fun i hi => hk i (Or.inr (hST a hi)))
  constructor <;> rintro ⟨a, u, hu, hFa⟩ <;> refine ⟨a, u, ?_, ?_⟩
  · exact hj.symm.trans hu
  · exact (hf a).1 hFa
  · exact hj.trans hu
  · exact (hf a).2 hFa

theorem glueRaw_map {ρ : RTy} (j : Set Nat)
    (F : L → (domain (Set Nat) L (.rel ρ)).obj (star (Set Nat) L))
    (S : L → Set (Set Nat)) (hS : ∀ a, ProfileSupport (Set Nat) L (S a) (F a).1)
    (hj : ∀ a, j ∉ S a) (a : L) :
    (intensionAction (arguments (Set Nat) L ρ)).map (spike (Set Nat) L j a)
      (glueRaw L j F) = (F a).1 := by
  ext ⟨V, x, k⟩
  have hf : ((⟨V, x, ((spike (Set Nat) L j a : (star (Set Nat) L) ⟶ (star (Set Nat) L)) ≫ k)⟩ :
      Σ U, (arguments (Set Nat) L ρ).obj U × ((star (Set Nat) L) ⟶ U)) ∈ (F a).1 ↔
      (⟨V, x, k⟩ : Σ U, (arguments (Set Nat) L ρ).obj U ×
        ((star (Set Nat) L) ⟶ U)) ∈ (F a).1) := by
    apply hS a V x
    intro i hi
    change k i * spike (Set Nat) L j a i = k i
    rw [spike_away _ _ _ _ _ (fun e => hj a (e ▸ hi)), mul_one]
  change (∃ (b : L) (u : Word L),
    k j * spike (Set Nat) L j a j = u * Word.of b ∧
    (⟨V, x, ((spike (Set Nat) L j a : (star (Set Nat) L) ⟶ (star (Set Nat) L)) ≫ k)⟩ :
      Σ U, (arguments (Set Nat) L ρ).obj U × ((star (Set Nat) L) ⟶ U)) ∈ (F b).1) ↔ _
  rw [spike_at]
  constructor
  · rintro ⟨b, u, he, hb⟩
    have hab := last_letter_unique L he
    subst b
    exact hf.1 hb
  · intro hFa
    exact ⟨a, k j, rfl, hf.2 hFa⟩

/-- Countably many arbitrary complete entities have a common predecessor.
The translating arrows use one coordinate fresh for the entire family. -/
theorem simultaneous_predecessor [Countable L] (ρ : RTy)
    (F : L → (domain (Set Nat) L (.rel ρ)).obj (star (Set Nat) L)) :
    ∃ (G : (domain (Set Nat) L (.rel ρ)).obj (star (Set Nat) L))
      (j : Set Nat), ∀ a : L,
      (domain (Set Nat) L (.rel ρ)).map (spike (Set Nat) L j a) G = F a := by
  classical
  choose S hSc hS using fun a => profile_support (Set Nat) L (F a)
  let T : Set (Set Nat) := ⋃ a, S a
  have hT : T.Countable := Set.countable_iUnion hSc
  have hST : ∀ a, S a ⊆ T := fun a _ hi => Set.mem_iUnion.2 ⟨a, hi⟩
  obtain ⟨j, hj⟩ := fresh_coordinate T hT
  refine ⟨⟨glueRaw L j F, glueRaw_supported L j F S hS hT hST⟩, j, fun a => ?_⟩
  apply Subtype.ext
  exact glueRaw_map L j F S hS (fun b hb => hj (hST b hb)) a

end Classicism.Meta.Intensional.Central.Product
