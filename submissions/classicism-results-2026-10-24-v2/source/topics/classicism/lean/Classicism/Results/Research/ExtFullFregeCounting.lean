import Mathlib.Data.Set.Finite.Basic

/-!
# Frege finiteness with extensionally full tests on cardinalities

Original semantic proof, 23 October 2026 (misc), unpaginated; supporting the
actual-extension argument in finite-type-propagation.md, sections 8 and 9.
The hypotheses below are the displayed semantic clauses for zero, successor,
property deletion and impredicative numberhood. They do not assume that
internal numbers are standard, or that internal finiteness is external
finiteness: those are the conclusions proved here. Application to a particular
intensional model still requires verification of these semantic clauses.
-/

namespace Classicism.Meta.Research.ExtFullFregeCounting

variable {α : Type}

/-- A finite size expressed by repeated deletion, without presupposing finiteness. -/
def HasSize : Nat → Set α → Prop
  | 0, s => s = ∅
  | n + 1, s => ∃ x ∈ s, HasSize n (s \ {x})

theorem finite_of_hasSize {n : Nat} {s : Set α} (h : HasSize n s) : s.Finite := by
  induction n generalizing s with
  | zero =>
      have hs : s = ∅ := h
      rw [hs]
      exact Set.finite_empty
  | succ n ih =>
      obtain ⟨x, hx, hn⟩ := h
      have he : insert x (s \ {x}) = s := by
        ext y
        simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨hy, _⟩)
          · exact hx
          · exact hy
        · intro hy
          by_cases hxy : y = x
          · exact Or.inl hxy
          · exact Or.inr ⟨hy, hxy⟩
      rw [← he]
      exact (ih hn).insert x

theorem hasSize_of_finite {s : Set α} (hs : s.Finite) : ∃ n, HasSize n s := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, rfl⟩
  | @insert x s hx hs ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, x, Set.mem_insert x s, ?_⟩
      have he : insert x s \ {x} = s := by
        ext y
        simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | hy, hne⟩
          · exact False.elim (hne rfl)
          · exact hy
        · intro hy
          exact ⟨Or.inr hy, fun h => hx (h ▸ hy)⟩
      rw [he]
      exact hn

theorem finite_iff_hasSize (s : Set α) : s.Finite ↔ ∃ n, HasSize n s :=
  ⟨hasSize_of_finite, fun ⟨_, hn⟩ => finite_of_hasSize hn⟩

/-- The local semantic data supplied by an extensionally full intensional model. -/
structure Frame (Object Cardinal Property Test : Type) where
  extension : Property → Set Object
  tests : Test → Set Cardinal
  tests_full : Function.Surjective tests
  zero : Cardinal
  successor : Cardinal → Cardinal
  realizes : Cardinal → Property → Prop
  remove : Property → Object → Property
  remove_extension : ∀ P x, extension (remove P x) = extension P \ {x}
  zero_realizes : ∀ P, realizes zero P ↔ extension P = ∅
  successor_realizes : ∀ n P,
    realizes (successor n) P ↔ ∃ x ∈ extension P, realizes n (remove P x)

namespace Frame

variable {Object Cardinal Property Test : Type}
variable (F : Frame Object Cardinal Property Test)

def numeral : Nat → Cardinal
  | 0 => F.zero
  | n + 1 => F.successor (numeral n)

def IsNumber (n : Cardinal) : Prop :=
  ∀ Q : Test, F.zero ∈ F.tests Q →
    (∀ m, m ∈ F.tests Q → F.successor m ∈ F.tests Q) → n ∈ F.tests Q

def InternallyFinite (P : Property) : Prop := ∃ n, F.IsNumber n ∧ F.realizes n P

theorem numeral_isNumber (n : Nat) : F.IsNumber (F.numeral n) := by
  intro Q hz hs
  induction n with
  | zero => exact hz
  | succ n ih => exact hs _ ih

/-- Full tests isolate the standard successor orbit; no injectivity is needed. -/
theorem isNumber_iff_numeral (n : Cardinal) :
    F.IsNumber n ↔ ∃ k : Nat, F.numeral k = n := by
  constructor
  · intro hn
    obtain ⟨Q, hQ⟩ := F.tests_full (Set.range F.numeral)
    have hz : F.zero ∈ F.tests Q := by
      rw [hQ]
      exact ⟨0, rfl⟩
    have hs : ∀ m, m ∈ F.tests Q → F.successor m ∈ F.tests Q := by
      intro m hm
      rw [hQ] at hm ⊢
      obtain ⟨k, rfl⟩ := hm
      exact ⟨k + 1, rfl⟩
    have hmem := hn Q hz hs
    rw [hQ] at hmem
    exact hmem
  · rintro ⟨k, rfl⟩
    exact F.numeral_isNumber k

theorem numeral_realizes (k : Nat) (P : Property) :
    F.realizes (F.numeral k) P ↔ HasSize k (F.extension P) := by
  induction k generalizing P with
  | zero => exact F.zero_realizes P
  | succ k ih =>
      change F.realizes (F.successor (F.numeral k)) P ↔ _
      rw [F.successor_realizes]
      apply exists_congr
      intro x
      rw [ih, F.remove_extension]

/-- Internal Frege finiteness is exactly finite actual extension in this frame. -/
theorem internallyFinite_iff (P : Property) :
    F.InternallyFinite P ↔ (F.extension P).Finite := by
  constructor
  · rintro ⟨n, hn, hP⟩
    obtain ⟨k, rfl⟩ := (F.isNumber_iff_numeral n).1 hn
    exact finite_of_hasSize ((F.numeral_realizes k P).1 hP)
  · intro hP
    obtain ⟨k, hk⟩ := hasSize_of_finite hP
    exact ⟨F.numeral k, F.numeral_isNumber k, (F.numeral_realizes k P).2 hk⟩

theorem universe_iff (P : Property) (hP : F.extension P = Set.univ) :
    F.InternallyFinite P ↔ Finite Object := by
  rw [F.internallyFinite_iff, hP]
  exact Set.finite_univ_iff

end Frame
end Classicism.Meta.Research.ExtFullFregeCounting

#print axioms Classicism.Meta.Research.ExtFullFregeCounting.Frame.isNumber_iff_numeral
#print axioms Classicism.Meta.Research.ExtFullFregeCounting.Frame.internallyFinite_iff
#print axioms Classicism.Meta.Research.ExtFullFregeCounting.Frame.universe_iff
