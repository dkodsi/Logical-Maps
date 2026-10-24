import Classicism.Models.BooleanFirstOrderSemantics
import Mathlib.ModelTheory.Encoding
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Monotone.Basic

/-!
# A concrete countable Boolean decision and witness chain

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-model-extraction.md`, sections 2--4
(unpaginated). Obligations contain actual Mathlib bounded formulas and
natural-number indices into a growing finite tuple of names. A separate
counterwitness obligation handles the primitive universal quantifier.

Every finite stage has a nonzero condition. Earlier names are preserved,
every finite parameter tuple eventually becomes ready, and the explicit
pairing schedule revisits each obligation arbitrarily late. The resulting
secured Boolean values form a proper upward-closed, finite-meet-closed
collection, decide every formula over the constructed names, and provide
counterinstances whenever the complement of a universal is secured.

No ordinary model, quotient truth lemma, theory verdict, maximum principle,
or extraction property is a field. The quotient and its truth lemma are
separate downstream obligations. External noncomputable selection is used.
-/

noncomputable section

namespace Classicism.Meta.ChoiceBoolean.WitnessChain

universe u v uL vL

open FirstOrder
open FirstOrderSemantics

variable {B : Type u} [CompleteBooleanAlgebra B]
variable {X : EqualitySpace.{u, v} B}
variable {L : FirstOrder.Language.{uL, vL}} [L.IsRelational]

private theorem le_compl_of_meet_zero {p b : B} (h : p ⊓ b = ⊥) : p ≤ bᶜ := by
  rw [← himp_bot b, le_himp_iff]
  exact h.le

/-- A nonzero meet with the complement of an infimum has a positive
counterinstance. No one component need attain the whole supremum. -/
theorem exists_positive_counter {D : Type v} (f : D → B) {p : B}
    (h : p ⊓ (⨅ x, f x)ᶜ ≠ ⊥) : ∃ x, p ⊓ (f x)ᶜ ≠ ⊥ := by
  classical
  by_contra hn
  have hz : ∀ x, p ⊓ (f x)ᶜ = ⊥ := by
    intro x
    by_contra hx
    exact hn ⟨x, hx⟩
  apply h
  rw [compl_iInf, inf_iSup_eq]
  simp only [hz, iSup_bot]

/-- The actual output of one refinement, including a name to append. -/
structure Outcome (X : EqualitySpace.{u, v} B) (p : B) where
  condition : B
  nonzero : condition ≠ ⊥
  below : condition ≤ p
  newName : X.Carrier

variable (M : FirstOrderSemantics.Structure X L)

def defaultName : X.Carrier := Classical.choice M.nonempty

def decisionOutcome (p : B) (hp : p ≠ ⊥) (b : B) : Outcome X p := by
  classical
  exact if h : p ⊓ b = ⊥ then
    ⟨p, hp, le_rfl, defaultName M⟩
  else
    ⟨p ⊓ b, h, inf_le_left, defaultName M⟩

theorem decisionOutcome_decides (p : B) (hp : p ≠ ⊥) (b : B) :
    (decisionOutcome M p hp b).condition ≤ b ∨
      (decisionOutcome M p hp b).condition ≤ bᶜ := by
  classical
  unfold decisionOutcome
  split
  · exact Or.inr (le_compl_of_meet_zero ‹p ⊓ b = ⊥›)
  · exact Or.inl inf_le_right

def counterOutcome (p : B) (hp : p ≠ ⊥) (f : X.Carrier → B) : Outcome X p := by
  classical
  exact if h : p ⊓ (⨅ x, f x)ᶜ = ⊥ then
    ⟨p, hp, le_rfl, defaultName M⟩
  else
    let hw := exists_positive_counter f h
    let x := Classical.choose hw
    ⟨p ⊓ (f x)ᶜ, Classical.choose_spec hw, inf_le_left, x⟩

theorem counterOutcome_spec (p : B) (hp : p ≠ ⊥) (f : X.Carrier → B) :
    (counterOutcome M p hp f).condition ≤ (⨅ x, f x) ∨
      (counterOutcome M p hp f).condition ≤
        (f (counterOutcome M p hp f).newName)ᶜ := by
  classical
  unfold counterOutcome
  split
  · exact Or.inl (by simpa only [compl_compl] using
      le_compl_of_meet_zero ‹p ⊓ (⨅ x, f x)ᶜ = ⊥›)
  · exact Or.inr inf_le_right

abbrev Decision (L : FirstOrder.Language.{uL, vL}) :=
  Σ n : Nat, L.BoundedFormula Empty n × (Fin n → Nat)

abbrev Counter (L : FirstOrder.Language.{uL, vL}) :=
  Σ n : Nat, L.BoundedFormula Empty (n + 1) × (Fin n → Nat)

abbrev Obligation (L : FirstOrder.Language.{uL, vL}) := Decision L ⊕ Counter L

namespace Obligation

def arity : Obligation L → Nat
  | .inl ⟨n, _⟩ => n
  | .inr ⟨n, _⟩ => n

def indices : (o : Obligation L) → Fin o.arity → Nat
  | .inl ⟨_, _, i⟩ => i
  | .inr ⟨_, _, i⟩ => i

def Ready (o : Obligation L) (stage : Nat) : Prop :=
  ∀ i, o.indices i < stage + 1

def height (o : Obligation L) : Nat := Finset.univ.sup o.indices

theorem ready_of_height_le (o : Obligation L) {n : Nat} (h : o.height ≤ n) :
    o.Ready n := by
  intro i
  exact Nat.lt_succ_of_le ((Finset.le_sup (Finset.mem_univ i)).trans h)

instance : Nonempty (Obligation L) :=
  ⟨.inl ⟨0, .falsum, Fin.elim0⟩⟩

instance boundedFormulaCountable [Countable L.Symbols] (n : Nat) :
    Countable (L.BoundedFormula Empty n) :=
  (Function.Injective.countable
    (f := fun φ => (⟨n, φ⟩ : Σ m, L.BoundedFormula Empty m))) sigma_mk_injective

instance [Countable L.Symbols] : Countable (Obligation L) := by
  infer_instance

def enumeration [Countable L.Symbols] : Nat → Obligation L :=
  Classical.choose (exists_surjective_nat (Obligation L))

theorem enumeration_surjective [Countable L.Symbols] :
    Function.Surjective (enumeration (L := L)) :=
  Classical.choose_spec (exists_surjective_nat (Obligation L))

/-- Every enumeration index recurs beyond every finite stage. -/
def scheduled [Countable L.Symbols] (n : Nat) : Obligation L :=
  enumeration (Nat.unpair n).1

theorem scheduled_fair [Countable L.Symbols] (o : Obligation L) (N : Nat) :
    ∃ n, N ≤ n ∧ scheduled n = o := by
  obtain ⟨j, hj⟩ := enumeration_surjective o
  refine ⟨Nat.pair j N, Nat.right_le_pair j N, ?_⟩
  simpa only [scheduled, Nat.unpair_pair] using hj

theorem exists_ready_stage [Countable L.Symbols] (o : Obligation L) (N : Nat) :
    ∃ n, N ≤ n ∧ scheduled n = o ∧ o.Ready n := by
  obtain ⟨n, hn, ho⟩ := scheduled_fair o (max N o.height)
  exact ⟨n, (le_max_left _ _).trans hn, ho,
    o.ready_of_height_le ((le_max_right _ _).trans hn)⟩

end Obligation

/-- At stage n exactly n+1 names have been introduced, allowing repetitions. -/
structure Stage (X : EqualitySpace.{u, v} B) (n : Nat) where
  names : Fin (n + 1) → X.Carrier
  condition : B
  nonzero : condition ≠ ⊥

def arguments {n : Nat} (s : Stage X n) (o : Obligation L) (h : o.Ready n) :
    Fin o.arity → X.Carrier := fun i => s.names ⟨o.indices i, h i⟩

def process : (o : Obligation L) → (Fin o.arity → X.Carrier) →
    (p : B) → p ≠ ⊥ → Outcome X p
  | .inl ⟨_, φ, _⟩, xs, p, hp =>
      decisionOutcome M p hp (value M φ Empty.elim xs)
  | .inr ⟨_, φ, _⟩, xs, p, hp =>
      counterOutcome M p hp (fun x => value M φ Empty.elim (Fin.snoc xs x))

def advance {n : Nat} (s : Stage X n) (o : Obligation L) : Stage X (n + 1) := by
  classical
  exact if h : o.Ready n then
    let r := process M o (arguments s o h) s.condition s.nonzero
    ⟨Fin.snoc s.names r.newName, r.condition, r.nonzero⟩
  else
    ⟨Fin.snoc s.names (defaultName M), s.condition, s.nonzero⟩

theorem advance_below {n : Nat} (s : Stage X n) (o : Obligation L) :
    (advance M s o).condition ≤ s.condition := by
  classical
  unfold advance
  split
  · exact (process M o (arguments s o ‹o.Ready n›) s.condition s.nonzero).below
  · exact le_rfl

theorem advance_preserves_names {n : Nat} (s : Stage X n) (o : Obligation L)
    (i : Fin (n + 1)) : (advance M s o).names i.castSucc = s.names i := by
  classical
  unfold advance
  split <;> simp only [Fin.snoc_castSucc]

theorem advance_decision {n k : Nat} (s : Stage X n)
    (φ : L.BoundedFormula Empty k) (indices : Fin k → Nat)
    (h : Obligation.Ready (.inl ⟨k, φ, indices⟩) n) :
    let o : Obligation L := .inl ⟨k, φ, indices⟩
    let b := value M φ Empty.elim (arguments s o h)
    (advance M s o).condition ≤ b ∨ (advance M s o).condition ≤ bᶜ := by
  classical
  dsimp only
  rw [advance, dif_pos h]
  exact decisionOutcome_decides M s.condition s.nonzero _

theorem advance_counter {n k : Nat} (s : Stage X n)
    (φ : L.BoundedFormula Empty (k + 1)) (indices : Fin k → Nat)
    (h : Obligation.Ready (.inr ⟨k, φ, indices⟩) n) :
    let o : Obligation L := .inr ⟨k, φ, indices⟩
    let xs := arguments s o h
    (advance M s o).condition ≤ value M (.all φ) Empty.elim xs ∨
      (advance M s o).condition ≤
        (value M φ Empty.elim
          (Fin.snoc xs ((advance M s o).names (Fin.last (n + 1)))))ᶜ := by
  classical
  let xs : Fin k → X.Carrier := fun i => s.names ⟨indices i, h i⟩
  let r : Outcome X s.condition := counterOutcome M s.condition s.nonzero
    (fun x => value M φ Empty.elim (Fin.snoc xs x))
  have ha : advance M s (.inr ⟨k, φ, indices⟩) =
      (⟨Fin.snoc s.names r.newName, r.condition, r.nonzero⟩ : Stage X (n + 1)) := by
    rw [advance, dif_pos h] <;> rfl
  change (advance M s (.inr ⟨k, φ, indices⟩)).condition ≤
      (⨅ x : X.Carrier, value M φ Empty.elim (Fin.snoc xs x)) ∨
    (advance M s (.inr ⟨k, φ, indices⟩)).condition ≤
      (value M φ Empty.elim
        (Fin.snoc xs ((advance M s (.inr ⟨k, φ, indices⟩)).names (Fin.last (n + 1)))))ᶜ
  rw [ha]
  simpa only [Fin.snoc_last] using
    counterOutcome_spec M s.condition s.nonzero
      (fun x => value M φ Empty.elim (Fin.snoc xs x))

section Chain

variable [Countable L.Symbols] (p₀ : B) (hp₀ : p₀ ≠ ⊥)

def stage : (n : Nat) → Stage X n
  | 0 => ⟨fun _ => defaultName M, p₀, hp₀⟩
  | n + 1 => advance M (stage n) (Obligation.scheduled n)

def name (n : Nat) : X.Carrier := (stage M p₀ hp₀ n).names (Fin.last n)

theorem stage_condition_antitone :
    Antitone (fun n => (stage M p₀ hp₀ n).condition) :=
  antitone_nat_of_succ_le (fun n =>
    advance_below M (stage M p₀ hp₀ n) (Obligation.scheduled n))

/-- Every previously introduced entry equals its permanent name. -/
theorem stage_name_eq : ∀ n (i : Fin (n + 1)),
    (stage M p₀ hp₀ n).names i = name M p₀ hp₀ i.val := by
  intro n
  induction n with
  | zero =>
      intro i
      have hi : i = Fin.last 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
      subst i
      rfl
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · change (advance M (stage M p₀ hp₀ n) (Obligation.scheduled n)).names
          j.castSucc = name M p₀ hp₀ j.val
        rw [advance_preserves_names]
        exact ih j

theorem arguments_eq_names {n : Nat} (o : Obligation L) (h : o.Ready n) :
    arguments (stage M p₀ hp₀ n) o h = fun i => name M p₀ hp₀ (o.indices i) := by
  funext i
  exact stage_name_eq M p₀ hp₀ n ⟨o.indices i, h i⟩

/-- Values secured by some finite nonzero condition of the actual chain. -/
def Secured (b : B) : Prop := ∃ n, (stage M p₀ hp₀ n).condition ≤ b

theorem secured_initial : Secured M p₀ hp₀ p₀ := ⟨0, le_rfl⟩

theorem secured_top : Secured M p₀ hp₀ ⊤ := ⟨0, le_top⟩

theorem not_secured_bot : ¬ Secured M p₀ hp₀ ⊥ := by
  rintro ⟨n, hn⟩
  exact (stage M p₀ hp₀ n).nonzero (bot_unique hn)

theorem secured_mono {b c : B} (h : Secured M p₀ hp₀ b) (hbc : b ≤ c) :
    Secured M p₀ hp₀ c := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.trans hbc⟩

theorem secured_inf {b c : B} (hb : Secured M p₀ hp₀ b)
    (hc : Secured M p₀ hp₀ c) : Secured M p₀ hp₀ (b ⊓ c) := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨m, hm⟩ := hc
  exact ⟨max n m, le_inf
    ((stage_condition_antitone M p₀ hp₀ (le_max_left n m)).trans hn)
    ((stage_condition_antitone M p₀ hp₀ (le_max_right n m)).trans hm)⟩

theorem secured_not_both {b : B} (hb : Secured M p₀ hp₀ b)
    (hc : Secured M p₀ hp₀ bᶜ) : False := by
  have h := secured_inf M p₀ hp₀ hb hc
  rw [inf_compl_eq_bot'] at h
  exact not_secured_bot M p₀ hp₀ h

/-- Every bounded formula with any finite tuple of permanent name indices
is decided. The tuple need not have existed when the chain began. -/
theorem eventual_decision {k : Nat} (φ : L.BoundedFormula Empty k)
    (indices : Fin k → Nat) :
    Secured M p₀ hp₀ (value M φ Empty.elim (fun i => name M p₀ hp₀ (indices i))) ∨
    Secured M p₀ hp₀ (value M φ Empty.elim (fun i => name M p₀ hp₀ (indices i)))ᶜ := by
  let o : Obligation L := .inl ⟨k, φ, indices⟩
  obtain ⟨n, _, ho, hr⟩ := Obligation.exists_ready_stage o 0
  have hs : stage M p₀ hp₀ (n + 1) = advance M (stage M p₀ hp₀ n) o := by
    rw [stage, ho]
  have hd := advance_decision M (stage M p₀ hp₀ n) φ indices hr
  change (advance M (stage M p₀ hp₀ n) o).condition ≤
      value M φ Empty.elim (arguments (stage M p₀ hp₀ n) o hr) ∨
    (advance M (stage M p₀ hp₀ n) o).condition ≤
      (value M φ Empty.elim (arguments (stage M p₀ hp₀ n) o hr))ᶜ at hd
  rw [← hs, arguments_eq_names] at hd
  exact hd.elim (fun h => Or.inl ⟨n + 1, h⟩) (fun h => Or.inr ⟨n + 1, h⟩)

/-- The primitive universal formula is eventually secured, or an actual
introduced name supplies a secured counterinstance. -/
theorem eventual_counter {k : Nat} (φ : L.BoundedFormula Empty (k + 1))
    (indices : Fin k → Nat) :
    Secured M p₀ hp₀ (value M (.all φ) Empty.elim
      (fun i => name M p₀ hp₀ (indices i))) ∨
    ∃ j, Secured M p₀ hp₀ (value M φ Empty.elim
      (Fin.snoc (fun i => name M p₀ hp₀ (indices i)) (name M p₀ hp₀ j)))ᶜ := by
  let o : Obligation L := .inr ⟨k, φ, indices⟩
  obtain ⟨n, _, ho, hr⟩ := Obligation.exists_ready_stage o 0
  have hs : stage M p₀ hp₀ (n + 1) = advance M (stage M p₀ hp₀ n) o := by
    rw [stage, ho]
  have hd := advance_counter M (stage M p₀ hp₀ n) φ indices hr
  change (advance M (stage M p₀ hp₀ n) o).condition ≤
      value M (.all φ) Empty.elim (arguments (stage M p₀ hp₀ n) o hr) ∨
    (advance M (stage M p₀ hp₀ n) o).condition ≤
      (value M φ Empty.elim (Fin.snoc (arguments (stage M p₀ hp₀ n) o hr)
        ((advance M (stage M p₀ hp₀ n) o).names (Fin.last (n + 1)))))ᶜ at hd
  rw [← hs, arguments_eq_names, stage_name_eq] at hd
  exact hd.elim (fun h => Or.inl ⟨n + 1, h⟩)
    (fun h => Or.inr ⟨n + 1, n + 1, h⟩)

/-- The exact counterwitness interface required by a quotient truth lemma. -/
theorem secured_not_all_witness {k : Nat} (φ : L.BoundedFormula Empty (k + 1))
    (indices : Fin k → Nat)
    (h : Secured M p₀ hp₀ (value M (.all φ) Empty.elim
      (fun i => name M p₀ hp₀ (indices i)))ᶜ) :
    ∃ j, Secured M p₀ hp₀ (value M φ Empty.elim
      (Fin.snoc (fun i => name M p₀ hp₀ (indices i)) (name M p₀ hp₀ j)))ᶜ := by
  rcases eventual_counter M p₀ hp₀ φ indices with hall | hcounter
  · exact False.elim (secured_not_both M p₀ hp₀ hall h)
  · exact hcounter

end Chain

end Classicism.Meta.ChoiceBoolean.WitnessChain
