import Classicism.Syntax.StrongPossibility

/-!
# A genuinely enlarged numerical fragment: countable disjunction inside lambda

Source: notes/infinitary-standard-numerals-20261022.md §§2–3,
principles.24 in the coverage audit (session deduction, source id misc).

THIS IS NOT THE FINITARY C SYNTAX. The numerical carrier represents a chosen
Frege sort nu_sigma; its available unary predicates are a separate sort.
`InfFormula.countableOr` is a new constructor, with an external Nat-indexed
family and the ordinary pointwise existential truth condition. `Comprehension`
gives actual predicates for lambda bodies in this enlarged fragment and an
explicit beta law. No modification is made to C's `Term` or reference theory.

The number predicate is DEFINED by impredicative zero/successor induction over
the available predicates. The proof derives numeral exhaustion by constructing
the particular infinitary lambda body. Under the displayed Peano conditions,
it also proves unique standard-numeral names. It assumes neither exhaustion
nor a standard-arithmetic isomorphism.

Remaining bridge for the whole original-Max incompatibility: extract these
frames from the action-model interpretation of the actual Frege definitions;
prove Sum/Prod correctness on standard numerals; implement the two independent
finitary arithmetic branches using the stated incompleteness input. This file
does NOT assert Con/NotCon of finitary C, Max, or SP.
-/

namespace ClassicismResearch.StrongPossibilityConsequences.InfinitaryNumerals

universe u v

/-- A local numerical carrier and its admitted unary predicate domain. The
predicate domain need not contain every external subset of the carrier. -/
structure Frame where
  Carrier : Type u
  Predicate : Type v
  zero : Carrier
  succ : Carrier → Carrier
  holds : Predicate → Carrier → Prop

namespace Frame

def numeral (M : Frame) : Nat → M.Carrier
  | 0 => M.zero
  | n + 1 => M.succ (numeral M n)

/-- Exactly the local impredicative induction clause for Frege numberhood. -/
def Number (M : Frame) (x : M.Carrier) : Prop :=
  ∀ p : M.Predicate,
    (M.holds p M.zero ∧ ∀ y, M.holds p y → M.holds p (M.succ y)) → M.holds p x

theorem number_zero (M : Frame) : M.Number M.zero := fun _ hp => hp.1

theorem number_succ (M : Frame) {x : M.Carrier} (hx : M.Number x) :
    M.Number (M.succ x) := fun p hp => hp.2 x (hx p hp)

theorem number_numeral (M : Frame) : ∀ n, M.Number (M.numeral n)
  | 0 => M.number_zero
  | n + 1 => M.number_succ (M.number_numeral n)

end Frame

/-- Terms in the selected numerical sort. Context sizes are metalogical. -/
inductive NumTerm (k : Nat) where
  | var : Fin k → NumTerm k
  | zero : NumTerm k
  | succ : NumTerm k → NumTerm k

def NumTerm.numeral {k : Nat} : Nat → NumTerm k
  | 0 => .zero
  | n + 1 => .succ (numeral n)

def NumTerm.eval {k : Nat} (M : Frame) (env : Fin k → M.Carrier) : NumTerm k → M.Carrier
  | .var i => env i
  | .zero => M.zero
  | .succ t => M.succ (t.eval M env)

theorem NumTerm.eval_numeral {k : Nat} (M : Frame) (env : Fin k → M.Carrier) :
    ∀ n, (NumTerm.numeral n : NumTerm k).eval M env = M.numeral n
  | 0 => rfl
  | n + 1 => congrArg M.succ (eval_numeral M env n)

/-- An explicit well-founded infinitary syntax. In particular countableOr
is inside formulas with free variables, so it may occur inside lambda bodies. -/
inductive InfFormula : Nat → Type where
  | eq {k : Nat} : NumTerm k → NumTerm k → InfFormula k
  | neg {k : Nat} : InfFormula k → InfFormula k
  | conj {k : Nat} : InfFormula k → InfFormula k → InfFormula k
  | all {k : Nat} : InfFormula (k + 1) → InfFormula k
  | countableOr {k : Nat} : (Nat → InfFormula k) → InfFormula k

def InfFormula.eval (M : Frame) : {k : Nat} → InfFormula k → (Fin k → M.Carrier) → Prop
  | _, .eq s t, env => s.eval M env = t.eval M env
  | _, .neg p, env => ¬ p.eval M env
  | _, .conj p q, env => p.eval M env ∧ q.eval M env
  | _, .all p, env => ∀ x, p.eval M (Fin.cases x env)
  | _, .countableOr f, env => ∃ n : Nat, (f n).eval M env

/-- Lambda comprehension for this expressly enlarged fragment. The result
must be in the existing predicate domain; pointwise truth alone is insufficient. -/
structure Comprehension (M : Frame) where
  abstract : InfFormula 1 → M.Predicate
  beta : ∀ p x, M.holds (abstract p) x ↔ p.eval M (fun _ => x)

/-- The new open formula bigvee_n (v0 = numeral n). -/
def standardRange : InfFormula 1 :=
  .countableOr (fun n => .eq (.var 0) (NumTerm.numeral n))

theorem standardRange_eval (M : Frame) (x : M.Carrier) :
    standardRange.eval M (fun _ => x) ↔ ∃ n, x = M.numeral n := by
  change (∃ n, x = (NumTerm.numeral n).eval M (fun _ : Fin 1 => x)) ↔ _
  simp only [NumTerm.eval_numeral]

/-- The infinitary formula yields an admitted predicate with exactly the
external standard numeral range. This is where the enlarged resource is used. -/
theorem range_predicate (M : Frame) (hcomp : Comprehension M) :
    ∃ p : M.Predicate, ∀ x, M.holds p x ↔ ∃ n, x = M.numeral n :=
  ⟨hcomp.abstract standardRange,
    fun x => (hcomp.beta standardRange x).trans (standardRange_eval M x)⟩

/-- At any world admitting the enlarged lambda body, no impredicative
number can be omitted by the external standard-numeral sequence. -/
theorem number_iff_numeral (M : Frame) (hcomp : Comprehension M) (x : M.Carrier) :
    M.Number x ↔ ∃ n, x = M.numeral n := by
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := range_predicate M hcomp
    apply (hp x).mp
    apply hx p
    constructor
    · exact (hp M.zero).mpr ⟨0, rfl⟩
    · intro y hy
      obtain ⟨n, hn⟩ := (hp y).mp hy
      exact (hp (M.succ y)).mpr ⟨n + 1, congrArg M.succ hn⟩
  · rintro ⟨n, rfl⟩
    exact M.number_numeral n

/-- The two Peano separation properties are independent of comprehension. -/
structure PeanoOnNumbers (M : Frame) : Prop where
  zero_ne_succ : ∀ x, M.Number x → M.zero ≠ M.succ x
  succ_injective : ∀ x y, M.Number x → M.Number y → M.succ x = M.succ y → x = y

theorem numeral_injective (M : Frame) (hP : PeanoOnNumbers M) :
    ∀ m n, M.numeral m = M.numeral n → m = n := by
  intro m
  induction m with
  | zero =>
    intro n h
    cases n with
    | zero => rfl
    | succ n => exact False.elim (hP.zero_ne_succ _ (M.number_numeral n) h)
  | succ m ih =>
    intro n h
    cases n with
    | zero => exact False.elim (hP.zero_ne_succ _ (M.number_numeral m) h.symm)
    | succ n =>
      exact congrArg Nat.succ (ih n (hP.succ_injective _ _
        (M.number_numeral m) (M.number_numeral n) h))

theorem unique_number_name (M : Frame) (hcomp : Comprehension M)
    (hP : PeanoOnNumbers M) (x : M.Carrier) (hx : M.Number x) :
    ∃ n : Nat, x = M.numeral n ∧ ∀ m, x = M.numeral m → m = n := by
  obtain ⟨n, hn⟩ := (number_iff_numeral M hcomp x).mp hx
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact numeral_injective M hP m n (hm.symm.trans hn)

/-- A nonstandard numerical point cannot realize this infinitary
comprehension resource. The conclusion is about the resource at that point. -/
theorem unnamed_number_excludes_comprehension (M : Frame) (x : M.Carrier)
    (hx : M.Number x) (hunnamed : ∀ n, x ≠ M.numeral n) : ¬ Nonempty (Comprehension M) := by
  rintro ⟨hcomp⟩
  obtain ⟨n, hn⟩ := (number_iff_numeral M hcomp x).mp hx
  exact hunnamed n hn

#print axioms number_iff_numeral
#print axioms unique_number_name
#print axioms unnamed_number_excludes_comprehension

end ClassicismResearch.StrongPossibilityConsequences.InfinitaryNumerals
