import Init.Data.List.Basic
import Init.Data.Nat.Basic

/-!
# Finite enumeration lemmas directly from inductive constructors

The first integration report found Classical.choice in the standard-library
dependency closures of the enumeration lemmas used by the probability batch.
This fresh module replaces those two primitives, without decidable equality,
classical cases, standard-library counting/erase results or extensionality.
It is ordinary external finite mathematics, not a C-language certificate.

The scalar and finite-fibre primitive wrappers now use this module. Ownership
returned to the probability author on 23 October 2026. Actual dependency
reports, not the constructor-based proof style alone, determine axiom status.
-/

namespace Classicism.Research.ProbabilityFinite

universe u
variable {A : Type u}

theorem mem_cons_cases {a b : A} {xs : List A} (h : a ∈ b :: xs) :
    a = b ∨ a ∈ xs := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ ht => exact Or.inr ht

theorem nodup_cons_parts {a : A} {xs : List A} (h : (a :: xs).Nodup) :
    (∀ b, b ∈ xs → a ≠ b) ∧ xs.Nodup := by
  cases h with
  | cons hh ht => exact ⟨hh, ht⟩

theorem perm_refl (xs : List A) : xs.Perm xs := by
  induction xs with
  | nil => exact List.Perm.nil
  | cons a xs ih => exact List.Perm.cons a ih

theorem perm_symm {xs ys : List A} (h : xs.Perm ys) : ys.Perm xs := by
  induction h with
  | nil => exact List.Perm.nil
  | cons a _ ih => exact List.Perm.cons a ih
  | swap a b xs => exact List.Perm.swap b a xs
  | trans _ _ ih₁ ih₂ => exact List.Perm.trans ih₂ ih₁

theorem perm_length {xs ys : List A} (h : xs.Perm ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg Nat.succ ih
  | swap a b xs => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Removing one *witnessed* occurrence. All output data is existential in Prop. -/
theorem remove_one (a : A) (ys : List A) (ha : a ∈ ys) :
    ∃ zs : List A, ys.Perm (a :: zs) ∧
      (∀ b, b ∈ zs → b ∈ ys) ∧
      (∀ b, b ∈ ys → b ≠ a → b ∈ zs) ∧
      (ys.Nodup → zs.Nodup ∧ ¬ a ∈ zs) := by
  revert ha
  induction ys with
  | nil => intro ha; cases ha
  | cons b ys ih =>
    intro ha
    cases mem_cons_cases ha with
    | inl hab =>
      subst b
      refine ⟨ys, perm_refl (a :: ys), ?_, ?_, ?_⟩
      · intro c hc
        exact List.Mem.tail a hc
      · intro c hc hca
        cases mem_cons_cases hc with
        | inl h => exact False.elim (hca h)
        | inr h => exact h
      · intro hn
        have hp := nodup_cons_parts hn
        exact ⟨hp.2, fun h => hp.1 a h rfl⟩
    | inr hay =>
      obtain ⟨zs, hp, horigin, hsurvive, hnodup⟩ := ih hay
      refine ⟨b :: zs,
        List.Perm.trans (List.Perm.cons b hp) (List.Perm.swap a b zs), ?_, ?_, ?_⟩
      · intro c hc
        cases mem_cons_cases hc with
        | inl hcb =>
          subst c
          exact List.Mem.head ys
        | inr hcz => exact List.Mem.tail b (horigin c hcz)
      · intro c hc hca
        cases mem_cons_cases hc with
        | inl hcb =>
          subst c
          exact List.Mem.head zs
        | inr hcy => exact List.Mem.tail b (hsurvive c hcy hca)
      · intro hn
        have hh := nodup_cons_parts hn
        have hz := hnodup hh.2
        refine ⟨List.Pairwise.cons (fun c hc => hh.1 c (horigin c hc)) hz.1, ?_⟩
        intro haz
        cases mem_cons_cases haz with
        | inl hab => exact hh.1 a hay hab.symm
        | inr h => exact hz.2 h

/-- Same finite set, duplicate-free on both sides: a constructive permutation. -/
theorem enumeration_perm {xs ys : List A} (hx : xs.Nodup) (hy : ys.Nodup)
    (he : ∀ a, a ∈ xs ↔ a ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.nil
    | cons b ys =>
      have hb : b ∈ ([] : List A) := (he b).2 (List.Mem.head ys)
      cases hb
  | cons a xs ih =>
    have hh := nodup_cons_parts hx
    have hay : a ∈ ys := (he a).1 (List.Mem.head xs)
    obtain ⟨zs, hp, horigin, hsurvive, hnodup⟩ := remove_one a ys hay
    have hz := hnodup hy
    have htail : ∀ b, b ∈ xs ↔ b ∈ zs := by
      intro b
      constructor
      · intro hb
        exact hsurvive b ((he b).1 (List.Mem.tail a hb))
          (fun hba => hh.1 b hb hba.symm)
      · intro hb
        have hbx : b ∈ a :: xs := (he b).2 (horigin b hb)
        cases mem_cons_cases hbx with
        | inl hba => exact False.elim (hz.2 (hba ▸ hb))
        | inr h => exact h
    exact List.Perm.trans (List.Perm.cons a (ih hh.2 hz.1 htail)) (perm_symm hp)

/-- A duplicate-free subcollection cannot be longer, even if the upper list repeats. -/
theorem enumeration_subset_length {xs ys : List A} (hx : xs.Nodup)
    (hsub : ∀ a, a ∈ xs → a ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    have hh := nodup_cons_parts hx
    have hay := hsub a (List.Mem.head xs)
    obtain ⟨zs, hp, horigin, hsurvive, hnodup⟩ := remove_one a ys hay
    have htail : ∀ b, b ∈ xs → b ∈ zs := by
      intro b hb
      exact hsurvive b (hsub b (List.Mem.tail a hb))
        (fun hba => hh.1 b hb hba.symm)
    have hi := Nat.succ_le_succ (ih hh.2 htail)
    have he := perm_length hp
    rw [he]
    exact hi

end Classicism.Research.ProbabilityFinite

#print axioms Classicism.Research.ProbabilityFinite.remove_one
#print axioms Classicism.Research.ProbabilityFinite.perm_length
#print axioms Classicism.Research.ProbabilityFinite.enumeration_perm
#print axioms Classicism.Research.ProbabilityFinite.enumeration_subset_length
