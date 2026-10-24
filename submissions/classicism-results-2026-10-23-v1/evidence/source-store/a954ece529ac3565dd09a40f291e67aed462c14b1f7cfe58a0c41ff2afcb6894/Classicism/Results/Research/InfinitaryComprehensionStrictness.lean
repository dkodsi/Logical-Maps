import Classicism.Models.ChoiceFirstOrderFull
import Classicism.Models.ChoiceFirstOrderMathlib
import Classicism.Results.Research.InfinitaryComprehensionFull
import Mathlib.ModelTheory.Skolem

/-!
# The countable elementary reduct and its omitted unary support

Original metatheoretic formalization (misc, 23 October 2026) of
`research/2026-10-23/infinitary-comprehension/infinitary-comprehension.md`,
Theorem 5.1 (unpaginated).

The elementary substructure below is obtained from Mathlib's downward
Löwenheim--Skolem theorem, applied to the existing, countable, explicitly
relational first-order presentation of the full one-world hierarchy on Nat.
Every natural individual is retained. Countability and a diagonal argument
produce a unary support which no retained unary property represents. Neither
the substructure nor the missing support is assumed.

Every original C theorem, translated by the existing satisfaction bridge,
is true in this elementary substructure. The named missing support is also
given by an actual countable-disjunction matrix of the new infinitary syntax.

Scope: this is the actual elementary-reduct/omission construction, not yet
the complete same-expanded-language countermodel certificate. It does not
assemble the reduct into `InfinitaryComprehension.Henkin.Model`, prove that
that interpretation has exactly two propositions, or transfer C5 and
Atomicity to the reconstructed typed model. Those remain explicit interface
obligations; no conclusion below is called the whole strictness theorem.
Compilation is intentionally held pending the shared dispatcher.
-/

namespace Classicism.Research.InfinitaryComprehension.Strictness

open Classicism.Meta
open Classicism.Meta.ChoiceFirstOrder
open Classicism.Meta.ChoiceFirstOrder.MathlibBridge

abbrev ambient : Structure := Full.fullStructure Nat inferInstance
abbrev Ambient : Type := Carrier ambient
abbrev ElementaryReduct := language.ElementarySubstructure Ambient

/-- The original individual n, with its actual type tag. -/
def natural (n : Nat) : Ambient := ⟨.e, n⟩

theorem natural_injective : Function.Injective natural := by
  intro m n h
  exact _root_.sigma_mk_injective h

instance ambientInfinite : Infinite Ambient :=
  Infinite.of_injective natural natural_injective

/-- Actual existence of a countable elementary substructure containing all
individuals, without a model-existence or satisfaction hypothesis. -/
theorem exists_countable_elementary_reduct :
    ∃ S : ElementaryReduct, Countable S ∧ ∀ n, natural n ∈ S := by
  classical
  let named : Set Ambient := Set.range natural
  have hnamed : Cardinal.mk named ≤ Cardinal.aleph0 :=
    (Set.countable_range natural).le_aleph0
  have hlanguage : language.card ≤ Cardinal.aleph0 := by
    letI : Countable language.Symbols := language_countable
    exact Cardinal.mk_le_aleph0
  obtain ⟨S, hS, hcard⟩ :=
    language.exists_elementarySubstructure_card_eq named (Cardinal.aleph0 : Cardinal.{0}) le_rfl
      (by simpa only [Cardinal.lift_id] using hnamed)
      (by simpa only [Cardinal.lift_id] using hlanguage)
      (by simpa only [Cardinal.lift_id] using Cardinal.aleph0_le_mk Ambient)
  have hcard' : Cardinal.mk S = Cardinal.aleph0 := by
    simpa only [Cardinal.lift_id] using hcard
  refine ⟨S, Cardinal.mk_le_aleph0_iff.mp hcard'.le, ?_⟩
  intro n
  exact hS ⟨n, rfl⟩

/-- Literal retained unary properties of the full hierarchy. -/
abbrev Unary (S : ElementaryReduct) :=
  {P : Full.Dom Nat (.e ⇒ RTy.t) // (⟨.e ⇒ RTy.t, P⟩ : Ambient) ∈ S}

def unaryInclusion (S : ElementaryReduct) (P : Unary S) : S :=
  ⟨⟨.e ⇒ RTy.t, P.val⟩, P.property⟩

theorem unaryInclusion_injective (S : ElementaryReduct) :
    Function.Injective (unaryInclusion S) := by
  intro P Q h
  apply Subtype.ext
  exact _root_.sigma_mk_injective (congrArg Subtype.val h)

instance unaryCountable (S : ElementaryReduct) [Countable S] : Countable (Unary S) :=
  Function.Injective.countable (unaryInclusion_injective S)

/-- A retained property evaluated at its retained natural individual. -/
def unaryHolds {S : ElementaryReduct} (P : Unary S) (n : Nat) : Prop :=
  (n, PUnit.unit) ∈ P.val

/-- Countability produces an actual omitted subset by diagonalization.
The set is constructed from an injection of retained properties into Nat. -/
theorem omitted_unary_support (S : ElementaryReduct) [Countable S] :
    ∃ U : Set Nat, ¬ ∃ P : Unary S, ∀ n, unaryHolds P n ↔ n ∈ U := by
  classical
  obtain ⟨code⟩ := nonempty_embedding_nat (Unary S)
  let U : Set Nat := {n | ∀ P : Unary S, code P = n → ¬ unaryHolds P n}
  refine ⟨U, ?_⟩
  rintro ⟨P, hP⟩
  have hnot : ¬ unaryHolds P (code P) := by
    intro hp
    exact ((hP (code P)).1 hp) P rfl hp
  have hin : code P ∈ U := by
    intro Q hQ
    have hQP : Q = P := code.injective hQ
    subst Q
    exact hnot
  exact hnot ((hP (code P)).2 hin)

/-- All original C theorems survive in this actual first-order reduct.
This uses both the established sentence translation and elementarity. -/
theorem c_theorems_survive (S : ElementaryReduct)
    {p : Sentence Signature.pure} (hp : C.Theorem p) :
    FirstOrder.Language.Sentence.Realize S (sentence p) := by
  apply (S.realize_sentence (sentence p)).2
  apply (sentence_correct ambient p).2
  exact ambient.model.theorem_holds (Full.isModel Nat inferInstance) hp

/-- The combined model-theory endpoint: an existing elementary reduct
contains every natural individual, validates every translated C theorem,
and omits a specified unary support. -/
theorem exists_elementary_reduct_with_omitted_support :
    ∃ S : ElementaryReduct, Countable S ∧ (∀ n, natural n ∈ S) ∧
      (∀ (p : Sentence Signature.pure), C.Theorem p →
        FirstOrder.Language.Sentence.Realize S (sentence p)) ∧
      ∃ U : Set Nat, ¬ ∃ P : Unary S, ∀ n, unaryHolds P n ↔ n ∈ U := by
  obtain ⟨S, hcount, hnames⟩ := exists_countable_elementary_reduct
  letI : Countable S := hcount
  exact ⟨S, hcount, hnames, fun _ hp => c_theorems_survive S hp,
    omitted_unary_support S⟩

/-- The omitted subset has an honest countable-disjunction formula. Its
parameters are individual names; the branch set is a subtype of Nat. -/
def namedSubset (U : Set Nat) : Formula (fun _ => Nat) [.e] :=
  .iOr {n : Nat // n ∈ U} (fun n => .eq (.var .zero) (.param n.val))

/-- The same formula is interpreted in the full hierarchy. Assignments to
unused parameter sorts are harmless; only the individual names occur. -/
theorem eval_namedSubset (U : Set Nat)
    (η : Assignment (fun _ => Nat) Nat PUnit)
    (hη : ∀ n, η (σ := .e) n = n) (n : Nat) (w : PUnit) :
    Term.eval η (namedSubset U) (Env.cons n Env.nil) w ↔ n ∈ U := by
  change (∃ m : {n : Nat // n ∈ U}, n = η (σ := .e) m.val) ↔ n ∈ U
  constructor
  · rintro ⟨m, hm⟩
    rw [hη] at hm
    exact hm.symm ▸ m.property
  · intro hn
    exact ⟨⟨n, hn⟩, (hη n).symm⟩

#print axioms exists_countable_elementary_reduct
#print axioms omitted_unary_support
#print axioms c_theorems_survive
#print axioms exists_elementary_reduct_with_omitted_support
#print axioms eval_namedSubset

end Classicism.Research.InfinitaryComprehension.Strictness
