import Init

/-!
# Fresh-column amalgamation and the finite-support selection obstruction

Ordinary external metatheory, not a shallow C proof or a C-model certificate.
The first part constructs a common extension of a partial column assignment
and its fresh-column transposition. It applies to arbitrary column/row/value
types; cardinal bounds on forcing conditions are a separate obligation.
The second part proves that no selector on predicates on Nat has finite
transposition support. Only a cofinite predicate is used in the contradiction.

Source: research/2026-10-22/followup/finite-functional-choice.md section 2
(unpaginated). These are original proof submissions (misc). No forcing,
symmetric-extension, soundness, or finite-fragment separation axiom is used.
In particular, this file does not mistake name permutations for automorphisms
of a transitive symmetric extension. Connecting it to that extension requires
the forcing symmetry lemma and the hereditary-symmetry construction.
-/

namespace Classicism.Meta.ChoiceFreshColumns

def swap {A : Type u} [DecidableEq A] (i j x : A) : A :=
  if x = i then j else if x = j then i else x

@[simp] theorem swap_left {A : Type u} [DecidableEq A] (i j : A) :
    swap i j i = j := by simp [swap]

@[simp] theorem swap_right {A : Type u} [DecidableEq A] (i j : A) :
    swap i j j = i := by
  by_cases h : j = i
  · subst j; simp [swap]
  · simp [swap, h]

theorem swap_other {A : Type u} [DecidableEq A] (i j x : A)
    (hi : x ≠ i) (hj : x ≠ j) : swap i j x = x := by
  simp [swap, hi, hj]

theorem swap_involutive {A : Type u} [DecidableEq A] (i j x : A) :
    swap i j (swap i j x) = x := by
  by_cases hi : x = i
  · subst x; simp
  · by_cases hj : x = j
    · subst x; simp
    · rw [swap_other i j x hi hj, swap_other i j x hi hj]

abbrev Assignment (Column : Type u) (Row : Type v) (Value : Type w) :=
  Column × Row → Option Value

def Extends {C : Type u} {R : Type v} {V : Type w}
    (q p : Assignment C R V) : Prop :=
  ∀ a b, p a = some b → q a = some b

def Compatible {C : Type u} {R : Type v} {V : Type w}
    (p q : Assignment C R V) : Prop :=
  ∀ a b c, p a = some b → q a = some c → b = c

def transpose {C : Type u} {R : Type v} {V : Type w} [DecidableEq C]
    (i j : C) (p : Assignment C R V) : Assignment C R V :=
  fun a => p (swap i j a.1, a.2)

def merge {C : Type u} {R : Type v} {V : Type w}
    (p q : Assignment C R V) : Assignment C R V :=
  fun a => match p a with
    | some b => some b
    | none => q a

theorem merge_extends_left {C : Type u} {R : Type v} {V : Type w}
    (p q : Assignment C R V) : Extends (merge p q) p := by
  intro a b h
  simp [merge, h]

theorem merge_extends_right {C : Type u} {R : Type v} {V : Type w}
    (p q : Assignment C R V) (h : Compatible p q) :
    Extends (merge p q) q := by
  intro a c hc
  cases hp : p a with
  | none => simpa [merge, hp] using hc
  | some b =>
    have e : b = c := h a b c hp hc
    simp [merge, hp, e]

/-- If column j is unused, transposing i and j creates no conflicting entry. -/
theorem fresh_compatible {C : Type u} {R : Type v} {V : Type w} [DecidableEq C]
    (p : Assignment C R V) (i j : C) (fresh : ∀ r, p (j, r) = none) :
    Compatible p (transpose i j p) := by
  intro a b c hb hc
  rcases a with ⟨k, r⟩
  by_cases hi : k = i
  · subst k
    have hnone : transpose i j p (i, r) = none := by
      simpa [transpose] using fresh r
    rw [hnone] at hc
    cases hc
  · by_cases hj : k = j
    · subst k
      rw [fresh r] at hb
      cases hb
    · have he : transpose i j p (k, r) = p (k, r) := by
        simp [transpose, swap_other i j k hi hj]
      rw [he] at hc
      exact Option.some.inj (hb.symm.trans hc)

/-- The common extension is an explicit merge, not an assumed compatibility. -/
theorem fresh_amalgam {C : Type u} {R : Type v} {V : Type w} [DecidableEq C]
    (p : Assignment C R V) (i j : C) (fresh : ∀ r, p (j, r) = none) :
    ∃ q, Extends q p ∧ Extends q (transpose i j p) :=
  ⟨merge p (transpose i j p), merge_extends_left _ _,
    merge_extends_right _ _ (fresh_compatible p i j fresh)⟩

/-- The merge has precisely the union of the two domains. Cardinal-size
closure of the intended forcing therefore reduces to binary union. -/
theorem merge_domain {C : Type u} {R : Type v} {V : Type w}
    (p q : Assignment C R V) (a : C × R) :
    (∃ b, merge p q a = some b) ↔ (∃ b, p a = some b) ∨ (∃ b, q a = some b) := by
  cases hp : p a with
  | none => simp [merge, hp]
  | some b => simp [merge, hp]

/-- An explicit fresh natural number; no choice operation is needed. -/
def bound : List Nat → Nat
  | [] => 0
  | a :: rest => max (a + 1) (bound rest)

theorem lt_bound_of_mem : ∀ (S : List Nat) (k : Nat), k ∈ S → k < bound S
  | [], _, h => False.elim (List.not_mem_nil h)
  | a :: rest, k, h => by
    rcases List.mem_cons.mp h with he | hm
    · subst k
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (lt_bound_of_mem rest k hm) (Nat.le_max_right _ _)

theorem bound_not_mem (S : List Nat) : bound S ∉ S :=
  fun h => Nat.lt_irrefl _ (lt_bound_of_mem S (bound S) h)

def Selects (c : (Nat → Prop) → Nat) : Prop :=
  ∀ X : Nat → Prop, (∃ k, X k) → X (c X)

/-- Transposition equivariance away from a specified finite support. This is
only a property of ordinary functions; no internal-model interpretation is asserted. -/
def SupportedBy (S : List Nat) (c : (Nat → Prop) → Nat) : Prop :=
  ∀ i j, i ∉ S → j ∉ S → ∀ X : Nat → Prop,
    c (fun k => X (swap i j k)) = swap i j (c X)

theorem cofinite_invariant (S : List Nat) (i j : Nat) (hi : i ∉ S) (hj : j ∉ S) :
    (fun k => swap i j k ∉ S) = (fun k => k ∉ S) := by
  funext k
  apply propext
  by_cases hki : k = i
  · subst k; simp [hi, hj]
  · by_cases hkj : k = j
    · subst k; simp [hi, hj]
    · rw [swap_other i j k hki hkj]

theorem no_supported_selector (S : List Nat) (c : (Nat → Prop) → Nat)
    (hc : Selects c) : ¬ SupportedBy S c := by
  intro hs
  let X : Nat → Prop := fun k => k ∉ S
  let i := c X
  have hi : i ∉ S := hc X ⟨bound S, bound_not_mem S⟩
  let j := bound (i :: S)
  have hfresh : j ∉ i :: S := bound_not_mem (i :: S)
  have hj : j ∉ S := fun h => hfresh (List.mem_cons.mpr (Or.inr h))
  have hji : j ≠ i := fun h => hfresh (List.mem_cons.mpr (Or.inl h))
  have hX : (fun k => X (swap i j k)) = X := cofinite_invariant S i j hi hj
  have he := hs i j hi hj X
  rw [hX] at he
  change i = swap i j i at he
  rw [swap_left] at he
  exact hji he.symm

/-- Unconditional metatheorem. It uses neither a separation-model assumption
nor a symmetric-extension existence assumption. It is not the hierarchy theorem. -/
theorem no_finitely_supported_selector :
    ¬ ∃ c : (Nat → Prop) → Nat, Selects c ∧ ∃ S, SupportedBy S c := by
  rintro ⟨c, hc, S, hs⟩
  exact no_supported_selector S c hc hs

end Classicism.Meta.ChoiceFreshColumns
