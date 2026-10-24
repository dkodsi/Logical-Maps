import Init.Data.List.Perm
import Classicism.Results.Research.AtomicProbabilityFiniteConstructive

/-!
# Scalar and finite-sum lemmas for the probability research

Ordinary Lean, conditional algebra; NOT a theorem of object-language C.
The scalar laws below are explicit structure parameters, not new axioms.
No instance at the internal reals, or even at an external real type, is supplied.
`Nat` and `List` are Lean's external inductive types.

Source: research/2026-10-22/proof-refinements/canonical-atomic-probability.md,
sections 1-3 (unpaginated); mathematical argument by OpenAI Codex, 22 Oct 2026.
The compilation and axiom reports are owned by the serial integration task.
-/

namespace Classicism.Research.Probability

universe u v

/-- The ordered additive scalar laws used by the envelope argument. -/
structure MassScalar (R : Type u) where
  zero : R
  add : R → R → R
  sub : R → R → R
  le : R → R → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  zero_add : ∀ x, add zero x = x
  add_comm : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_mono : ∀ {x y z w}, le x y → le z w → le (add x z) (add y w)
  add_le_iff_le_sub : ∀ x y z, le (add x y) z ↔ le x (sub z y)
  sub_self : ∀ x, sub x x = zero
  sub_add_sub : ∀ x y z w,
    sub (add x y) (add z w) = add (sub x z) (sub y w)

namespace MassScalar

variable {R : Type u} (s : MassScalar R)

theorem add_zero (x : R) : s.add x s.zero = x := by
  rw [s.add_comm, s.zero_add]

theorem add_left_comm (x y z : R) :
    s.add x (s.add y z) = s.add y (s.add x z) := by
  rw [← s.add_assoc, s.add_comm x y, s.add_assoc]

def Nonnegative (x : R) : Prop := s.le s.zero x

def Positive (x : R) : Prop := s.Nonnegative x ∧ x ≠ s.zero

theorem add_nonnegative {x y : R} (hx : s.Nonnegative x)
    (hy : s.Nonnegative y) : s.Nonnegative (s.add x y) := by
  have h := s.add_mono hx hy
  rw [s.zero_add] at h
  exact h

theorem le_add_of_nonnegative_right (x : R) {y : R}
    (hy : s.Nonnegative y) : s.le x (s.add x y) := by
  have h := s.add_mono (s.le_refl x) hy
  rw [s.add_zero] at h
  exact h

theorem le_add_of_nonnegative_left {x : R} (hx : s.Nonnegative x)
    (y : R) : s.le y (s.add x y) := by
  rw [s.add_comm]
  exact s.le_add_of_nonnegative_right y hx

theorem positive_of_positive_le {x y : R} (hx : s.Positive x)
    (hxy : s.le x y) : s.Positive y := by
  refine ⟨s.le_trans hx.1 hxy, ?_⟩
  intro hy
  have hx0 : s.le x s.zero := hy ▸ hxy
  exact hx.2 (s.le_antisymm hx0 hx.1)

theorem sub_nonnegative {x y : R} (hyx : s.le y x) :
    s.Nonnegative (s.sub x y) := by
  apply (s.add_le_iff_le_sub s.zero y x).mp
  rw [s.zero_add]
  exact hyx

/-- A finite sum; this is not an internally coded C sequence. -/
def sum {A : Type v} (f : A → R) : List A → R
  | [] => s.zero
  | a :: xs => s.add (f a) (sum f xs)

theorem sum_nil {A : Type v} (f : A → R) : s.sum f [] = s.zero := rfl

theorem sum_cons {A : Type v} (f : A → R) (a : A) (xs : List A) :
    s.sum f (a :: xs) = s.add (f a) (s.sum f xs) := rfl

theorem sum_congr {A : Type v} {f g : A → R} (xs : List A)
    (h : ∀ a, a ∈ xs → f a = g a) : s.sum f xs = s.sum g xs := by
  revert h
  induction xs with
  | nil => intro h; rfl
  | cons a xs ih =>
    intro h
    change s.add (f a) (s.sum f xs) = s.add (g a) (s.sum g xs)
    rw [h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem sum_nonnegative {A : Type v} (f : A → R) (xs : List A)
    (h : ∀ a, a ∈ xs → s.Nonnegative (f a)) :
    s.Nonnegative (s.sum f xs) := by
  revert h
  induction xs with
  | nil => intro h; exact s.le_refl s.zero
  | cons a xs ih =>
    intro h
    exact s.add_nonnegative (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem sum_mono {A : Type v} (f g : A → R) (xs : List A)
    (h : ∀ a, a ∈ xs → s.le (f a) (g a)) :
    s.le (s.sum f xs) (s.sum g xs) := by
  revert h
  induction xs with
  | nil => intro h; exact s.le_refl s.zero
  | cons a xs ih =>
    intro h
    exact s.add_mono (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem sum_append {A : Type v} (f : A → R) (xs ys : List A) :
    s.sum f (xs ++ ys) = s.add (s.sum f xs) (s.sum f ys) := by
  induction xs with
  | nil => exact (s.zero_add _).symm
  | cons a xs ih =>
    change s.add (f a) (s.sum f (xs ++ ys)) =
      s.add (s.add (f a) (s.sum f xs)) (s.sum f ys)
    rw [ih, s.add_assoc]

theorem sum_perm {A : Type v} (f : A → R) {xs ys : List A}
    (h : xs.Perm ys) : s.sum f xs = s.sum f ys := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (s.add (f a)) ih
  | swap a b xs => exact s.add_left_comm (f b) (f a) (s.sum f xs)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem member_le_sum {A : Type v} (f : A → R) (xs : List A)
    (hn : ∀ a, a ∈ xs → s.Nonnegative (f a)) {a : A} (ha : a ∈ xs) :
    s.le (f a) (s.sum f xs) := by
  revert hn ha
  induction xs with
  | nil => intro hn ha; cases ha
  | cons b xs ih =>
    intro hn ha
    have htail := fun c hc => hn c (List.mem_cons_of_mem b hc)
    cases List.mem_cons.mp ha with
    | inl hab =>
      subst a
      exact s.le_add_of_nonnegative_right (f b) (s.sum_nonnegative f xs htail)
    | inr hat =>
      exact s.le_trans (ih htail hat)
        (s.le_add_of_nonnegative_left (hn b List.mem_cons_self) (s.sum f xs))

theorem sum_positive_of_member {A : Type v} (f : A → R) (xs : List A)
    (hn : ∀ a, a ∈ xs → s.Nonnegative (f a)) {a : A} (ha : a ∈ xs)
    (hp : s.Positive (f a)) : s.Positive (s.sum f xs) :=
  s.positive_of_positive_le hp (s.member_le_sum f xs hn ha)

def nsmul (x : R) : Nat → R
  | 0 => s.zero
  | n + 1 => s.add x (nsmul x n)

theorem sum_const {A : Type v} (x : R) (xs : List A) :
    s.sum (fun _ : A => x) xs = s.nsmul x xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change s.add x (s.sum (fun _ : A => x) xs) = s.add x (s.nsmul x xs.length)
    exact congrArg (s.add x) ih

theorem nsmul_nonnegative {x : R} (hx : s.Nonnegative x) (n : Nat) :
    s.Nonnegative (s.nsmul x n) := by
  induction n with
  | zero => exact s.le_refl s.zero
  | succ n ih => exact s.add_nonnegative hx ih

theorem nsmul_mono_index {x : R} (hx : s.Nonnegative x) {m n : Nat}
    (h : m ≤ n) : s.le (s.nsmul x m) (s.nsmul x n) := by
  induction h with
  | refl => exact s.le_refl _
  | step _ ih =>
    exact s.le_trans ih (s.le_add_of_nonnegative_left hx _)

end MassScalar

/-- Division by a positive finite cardinal; only the stated scalar laws are assumed. -/
structure FiniteDivision {R : Type u} (s : MassScalar R) where
  divide : R → Nat → R
  divide_zero : ∀ n, divide s.zero n = s.zero
  nsmul_divide : ∀ x n, n ≠ 0 → s.nsmul (divide x n) n = x
  divide_nsmul : ∀ x n, n ≠ 0 → divide (s.nsmul x n) n = x
  divide_nonnegative : ∀ {x} n, s.Nonnegative x → s.Nonnegative (divide x n)
  divide_positive : ∀ {x} n, n ≠ 0 → s.Positive x → s.Positive (divide x n)

/-- Constructive finite-data permutation; the legacy instance parameter is retained. -/
theorem enumeration_perm {A : Type u} [DecidableEq A] {xs ys : List A}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (h : ∀ a, a ∈ xs ↔ a ∈ ys) : xs.Perm ys :=
  ProbabilityFinite.enumeration_perm hx hy h

end Classicism.Research.Probability
