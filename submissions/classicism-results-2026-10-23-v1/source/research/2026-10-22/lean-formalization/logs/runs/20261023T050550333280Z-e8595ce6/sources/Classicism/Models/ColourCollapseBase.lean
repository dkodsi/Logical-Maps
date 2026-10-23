import Classicism.Models.SymBase
import Mathlib.Data.Nat.ModEq

/-!
# The actual three-object colour-collapse category

Original construction/formalization (misc), 22 October 2026. Source:
research/2026-10-22/notes/colour-collapse-entrance.md, sections 1–2
(unpaginated). A,B,C have Nat individuals; B's coloured set is the evens,
C's is {0,1}. Arrows are precisely the forward surjections preserving
colour. At A this imposes no colour restriction.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

inductive Stage | A | B | C deriving DecidableEq

def rank : Stage → Nat | .A => 0 | .B => 1 | .C => 2

def colored : Stage → Nat → Prop
  | .A, _ => False
  | .B, n => n % 2 = 0
  | .C, n => n < 2

def Arr {W V : Stage} (f : Nat → Nat) : Prop :=
  rank W ≤ rank V ∧ Function.Surjective f ∧ ∀ n, colored W n → colored V (f n)

abbrev cat : FunCat where
  Obj := Stage
  X _ := Nat
  Arr := fun {W V} f => Arr (W := W) (V := V) f
  arr_id _ := ⟨Nat.le_refl _, Function.surjective_id, fun _ h => h⟩
  arr_comp hf hg := ⟨Nat.le_trans hf.1 hg.1, hg.2.1.comp hf.2.1,
    fun n hn => hg.2.2 _ (hf.2.2 n hn)⟩

abbrev A : cat.Ob := Stage.A
abbrev B : cat.Ob := Stage.B
abbrev C : cat.Ob := Stage.C

def syms (W : cat.Ob) : Set (W ⟶ W) :=
  {g | Function.Bijective (FunCat.fn g) ∧ ∀ n, colored W (FunCat.fn g n) ↔ colored W n}

theorem syms_inv : SymGroup syms := by
  intro W g hg
  let e := Equiv.ofBijective (FunCat.fn g) hg.1
  have hp : ∀ n, colored W (e.symm n) ↔ colored W n := by
    intro n
    have h := hg.2 (e.symm n)
    change colored W (e (e.symm n)) ↔ colored W (e.symm n) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  let gi : W ⟶ W := FunCat.arr e.symm
    ⟨Nat.le_refl _, e.symm.surjective, fun n hn => (hp n).2 hn⟩
  refine ⟨gi, ⟨e.symm.bijective, hp⟩, ?_, ?_⟩
  · exact FunCat.hom_ext (funext e.symm_apply_apply)
  · exact FunCat.hom_ext (funext e.apply_symm_apply)

abbrev base (W : cat.Ob) : SymBase where
  F := cat
  G := syms
  G_id _ := ⟨Function.bijective_id, fun _ => Iff.rfl⟩
  G_comp hg hs := ⟨hs.1.comp hg.1, fun n => (hs.2 _).trans (hg.2 n)⟩
  G_inv := syms_inv
  W₀ := W
  ne _ := ⟨0⟩
  J := PinIdeal.fin _
  J_base _ h := h

abbrev model : Premodel Signature.pure cat.Ob := (base A).model

theorem isModel : model.IsModel := (base A).model_isModel

theorem transport_surjective {W V : cat.Ob} (k : W ⟶ V) (σ : Ty) :
    Function.Surjective ((model.inner σ).map k) :=
  SymBase.map_surjective_of (S := base W) (fun _ _ h => h) k k.2.2.1 σ

theorem bf_at (σ : Ty) {W : cat.Ob} (h : A ⟶ W) :
    model.Holds h (P.Barcan.quoted σ) .nil := by
  change model.Holds h (Sentence.bf σ) .nil
  exact model.holds_bf_of_surjective isModel σ h (fun k => transport_surjective k σ)

theorem boxed_bf (σ : Ty) : model.HoldsSentence (P.NecBarcan.quoted σ) := by
  change model.Holds (𝟙 A) (Term.box (P.Barcan.quoted σ)) .nil
  rw [model.holds_box isModel]
  intro W h
  simpa only [Category.id_comp, IEnv.nil_eq] using bf_at σ h

def entrance : A ⟶ B := FunCat.arr id
  ⟨by decide, Function.surjective_id, fun _ h => h.elim⟩

def collapseFn (n : Nat) : Nat := if n % 2 = 0 then 0 else n / 2

theorem collapse_surjective : Function.Surjective collapseFn := by
  intro n
  refine ⟨2 * n + 1, ?_⟩
  have hm : (2 * n + 1) % 2 ≠ 0 := by omega
  simp only [collapseFn, if_neg hm]
  omega

def collapse : B ⟶ C := FunCat.arr collapseFn
  ⟨by decide, collapse_surjective, fun n hn => by
    change (if n % 2 = 0 then 0 else n / 2) < 2
    rw [if_pos hn]
    decide⟩

def merge : C ⟶ C := FunCat.arr (fun n => n / 2)
  ⟨Nat.le_refl _, fun n => ⟨2 * n, by omega⟩, fun n hn => by
    change n < 2 at hn
    change n / 2 < 2
    omega⟩

theorem merge_zero : FunCat.fn merge 0 = 0 := rfl
theorem merge_one : FunCat.fn merge 1 = 0 := rfl

private def tail (W : Stage) (N n : Nat) : Nat :=
  match W with
  | .A => n - N
  | .B => if n % 2 = 0 then 0 else n / 2 - N
  | .C => if n < 2 then 0 else n - N

/-- Every finite colour-compatible prescription extends to an actual allowed
surjection. The unused uncoloured tail explicitly covers every target value. -/
theorem extend_finite {W V : cat.Ob} (hWV : rank W ≤ rank V)
    {D : Set Nat} (hD : D.Finite) (f : Nat → Nat)
    (hc : ∀ n ∈ D, colored W n → colored V (f n)) :
    ∃ h : W ⟶ V, ∀ n ∈ D, FunCat.fn h n = f n := by
  classical
  obtain ⟨b, hb⟩ := hD.bddAbove
  let N := b + 2
  have hN : 2 ≤ N := by omega
  have hbound : ∀ n ∈ D, n < N := fun n hn => by have := hb hn; omega
  let q : Nat → Nat := fun n => if n ∈ D then f n else tail W N n
  have hsurj : Function.Surjective q := by
    intro y
    cases W
    · refine ⟨y + N, ?_⟩
      have hn : y + N ∉ D := fun h => by have := hbound _ h; omega
      simp [q, hn, tail]
    · refine ⟨2 * (y + N) + 1, ?_⟩
      have hn : 2 * (y + N) + 1 ∉ D := fun h => by have := hbound _ h; omega
      have hm : (2 * (y + N) + 1) % 2 ≠ 0 := by omega
      simp only [q, if_neg hn, tail, if_neg hm]
      omega
    · refine ⟨y + N, ?_⟩
      have hn : y + N ∉ D := fun h => by have := hbound _ h; omega
      have hm : ¬ y + N < 2 := by omega
      simp [q, hn, tail, hm]
  have hcolor : ∀ n, colored W n → colored V (q n) := by
    intro n hn
    by_cases hd : n ∈ D
    · simpa only [q, if_pos hd] using hc n hd hn
    · simp only [q, if_neg hd]
      cases W <;> cases V <;> simp_all [rank, colored, tail]
  exact ⟨FunCat.arr q ⟨hWV, hsurj, hcolor⟩, fun n hn => by simp [q, hn]⟩

/-- The finite factorization used at the entrance, constructed from an
actual surjection and the finite-extension theorem above. -/
theorem root_factor {V : cat.Ob} (h h' : A ⟶ V) {S M : Set Nat}
    (hS : S.Finite) (hM : M.Finite) (hag : AgreeOn cat.De S h h') :
    ∃ u : A ⟶ A, (∀ x ∈ S, FunCat.fn u x = x) ∧
      AgreeOn cat.De M (u ≫ h) h' := by
  classical
  let q : Nat → Nat := fun x => if x ∈ S then x else Classical.choose (h.2.2.1 (FunCat.fn h' x))
  obtain ⟨u, hu⟩ := extend_finite (W := A) (V := A) (Nat.le_refl _) (hS.union hM) q
    (fun _ _ hc => hc.elim)
  refine ⟨u, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hu x (Or.inl hx)]
    simp [q, hx]
  · change FunCat.fn h (FunCat.fn u x) = FunCat.fn h' x
    rw [hu x (Or.inr hx)]
    by_cases hs : x ∈ S
    · simpa [q, hs] using hag x hs
    · simp only [q, if_neg hs]
      exact Classical.choose_spec (h.2.2.1 (FunCat.fn h' x))

end
end Classicism.Meta.Intensional.ColourCollapse
