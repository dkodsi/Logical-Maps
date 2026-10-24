import ClassicismZFC.CHOrdinalDirection
import Flypitch4.ForcingCH

/-!
# A selected countable-initial-segment ordinal in the collapse model

The witness is the actual checked ground-model omega-one. Its ordinal status
and the countability of every member are the pinned Flypitch theorems
`check_Ord` and `injects_into_omega_of_mem_aleph_one_check`. The collapse
comparison is `aleph_one_not_lt_powerset_omega`, with its double complement
removed. These are source theorems, not additional model-interface fields.

One finite sentence retains the selected ordinal and all three properties.
The continuum comparison remains the source's partial-surjection predicate:
`atMostF Pomega A`. Conversion to an injection is performed only in the
ordinary ZFC model by the separately proved internal choice theorem.

Source: Flypitch Project, Apache 2.0, pinned at
218d1c1e46f77d4db80e566d1721782e85b94a17; AlephOne.lean:1842,
BvmExtras.lean:5175, ForcingCH.lean:1315. The finite-sentence adapter is
original work, 23 October 2026. No compiler has been run.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder Fol Flypitch

namespace ClassicismZFC.CountableOrdinalForcing

/-- An ordinal covering the continuum, all of whose members inject into omega.
Every quantifier is an ordinary first-order quantifier over internal codes. -/
def Criterion : L.Sentence := toSentence <|
  exF fun A => andF (ordF A)
    (andF
      (allIn (varT A) fun a => CHFieldTransport.injectsF (varT a) omT)
      (CHTranslation.atMostF (powT omT) (varT A)))

/-- The literal same finite sentence in the pinned Flypitch syntax. -/
def Criterion_f : Fol.sentence L_ZFC :=
  Fol.bd_ex (Fol.bd_and Ord_f
    (Fol.bd_and
      (Fol.bd_all (Fol.bd_imp
        (mem' (Fol.bd_var ⟨0, by omega⟩) (Fol.bd_var ⟨1, by omega⟩))
        ((Fol.subst0_bounded_formula injects_into_f ω').cast (by omega))))
      (Fol.subst0_bounded_formula at_most_f (Powerset omega'))))

/-- Syntax equality, not a postulated interpretation theorem. -/
theorem tr_Criterion : tr Criterion = Criterion_f := rfl

section Ordinary

open SetLaws CHCardinality
universe u
variable {M : Type u} [L.Structure M]

/-- Direct evaluation retains the unnormalized injection graphs and the
literal partial-surjection template before applying any choice theorem. -/
theorem realize_Criterion_raw :
    (M ⊨ Criterion) ↔
      ∃ A : M, CHOrdinalDirection.IsOrdinal A ∧
        (∀ a, memM a A → ∃ G, CHFieldTransport.RawInjection a omegaM G) ∧
        RawAtMost (powerM omegaM) A := by
  simp [Criterion, CHOrdinalDirection.IsOrdinal,
    CHFieldTransport.injectsF, CHFieldTransport.injectiveGraphF,
    CHTranslation.atMostF, CHTranslation.functionalGraphF,
    CHTranslation.totalGraphF, CHFieldTransport.RawInjection,
    RawAtMost, CHCardinality.Subset, Edge, ordF, subsetF,
    toSentence, allIn, allF, exF, andF, orF, impF, notF, eqF, memF,
    varT, Sentence.Realize, Formula.Realize, memM, Fin.snoc]

/-- Exact ordinary interpretation, with all maps internally represented. -/
theorem realize_Criterion (hZFC : M ⊨ Erdos501.FOL.ZFC) :
    (M ⊨ Criterion) ↔
      ∃ A : M, CHOrdinalDirection.IsOrdinal A ∧
        (∀ a, memM a A → Injects a omegaM) ∧ AtMost (powerM omegaM) A := by
  rw [realize_Criterion_raw]
  constructor
  · rintro ⟨A, hA, hc, hp⟩
    refine ⟨A, hA, ?_, (rawAtMost_iff (powerM omegaM) A).mp hp⟩
    intro a ha
    obtain ⟨G, hG⟩ := hc a ha
    exact CHFieldTransport.normalize_raw hZFC hG
  · rintro ⟨A, hA, hc, hp⟩
    refine ⟨A, hA, ?_, (rawAtMost_iff (powerM omegaM) A).mpr hp⟩
    intro a ha
    obtain ⟨G, hG⟩ := hc a ha
    exact ⟨G, CHFieldTransport.raw_of_injection hG⟩

theorem criterion_witnesses (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (h : M ⊨ Criterion) :
    ∃ A : M, CHOrdinalDirection.IsOrdinal A ∧
      (∀ a, memM a A → Injects a omegaM) ∧ AtMost (powerM omegaM) A :=
  (realize_Criterion hZFC).mp h

end Ordinary

section Boolean

open Fol bSet Lattice
variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

/-- The bounded universal property used by the finite sentence. -/
def countableInitialSegments (A : bSet β) : β :=
  ⨅ a : bSet β, _root_.imp (a ∈ᴮ A) (injects_into a bSet.omega)

/-- Boolean evaluation of the actual translated sentence. The order of
`larger_than A Pomega` is the order of `atMostF Pomega A`. -/
theorem boolean_realize_Criterion :
    ⟦tr Criterion⟧[V β] =
      ⨆ A : bSet β, Ord A ⊓
        (countableInitialSegments A ⊓ larger_than A (bv_powerset bSet.omega)) := by
  have hcount : ∀ A a : V β,
      boolean_realize_bounded_formula (DVec.cons a (DVec.cons A DVec.nil))
        ((subst0_bounded_formula injects_into_f ω').cast (by omega)) DVec.nil =
        injects_into a bSet.omega := by
    intro A a
    calc
      _ = boolean_realize_bounded_formula
          (DVec.cons (bSet.omega : V β) (DVec.cons a DVec.nil))
          injects_into_f DVec.nil := rfl
      _ = injects_into a bSet.omega := realize_injects_into
  have hcover : ∀ A : V β,
      boolean_realize_bounded_formula (DVec.cons A DVec.nil)
        (subst0_bounded_formula at_most_f (Powerset omega')) DVec.nil =
        larger_than A (bv_powerset bSet.omega) := by
    intro A
    calc
      _ = boolean_realize_bounded_formula
          (DVec.cons (bv_powerset (bSet.omega : V β)) (DVec.cons A DVec.nil))
          at_most_f DVec.nil := rfl
      _ = larger_than A (bv_powerset bSet.omega) := realize_at_most_f
  rw [tr_Criterion]
  simp only [Criterion_f, boolean_realize_sentence,
    boolean_realize_bounded_formula, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term, DVec.nth, V_exists, V_forall,
    Ord_f_is_Ord, hcount, hcover, countableInitialSegments] <;> rfl

/-- The actual chosen ordinal in the collapse algebra. -/
noncomputable def collapseOrdinal : bSet collapse_algebra.𝔹_collapse :=
  check PSet.aleph_one

theorem collapseOrdinal_ordinal {Γ : collapse_algebra.𝔹_collapse} :
    Γ ≤ Ord collapseOrdinal := check_Ord PSet.aleph_one_Ord

theorem collapseOrdinal_member_countable {Γ : collapse_algebra.𝔹_collapse}
    {a : bSet collapse_algebra.𝔹_collapse} (ha : Γ ≤ a ∈ᴮ collapseOrdinal) :
    Γ ≤ injects_into a bSet.omega :=
  injects_into_omega_of_mem_aleph_one_check ha

theorem collapseOrdinal_countableInitialSegments {Γ : collapse_algebra.𝔹_collapse} :
    Γ ≤ countableInitialSegments collapseOrdinal := by
  apply le_iInf
  intro a
  rw [← _root_.deduction]
  exact collapseOrdinal_member_countable inf_le_right

/-- A subset of the checked omega-one surjects onto the internal continuum.
This statement deliberately does not claim a Boolean injection theorem. -/
theorem collapseOrdinal_continuum_atMost {Γ : collapse_algebra.𝔹_collapse} :
    Γ ≤ larger_than collapseOrdinal (bv_powerset bSet.omega) := by
  change Γ ≤ larger_than (check PSet.aleph_one) (bv_powerset bSet.omega)
  simpa only [compl_compl, PSet.aleph_one, pSet_aleph1] using
    (collapse_algebra.aleph_one_not_lt_powerset_omega (Γ := Γ))

theorem collapseOrdinal_spec {Γ : collapse_algebra.𝔹_collapse} :
    Γ ≤ Ord collapseOrdinal ⊓
      (countableInitialSegments collapseOrdinal ⊓
        larger_than collapseOrdinal (bv_powerset bSet.omega)) :=
  le_inf collapseOrdinal_ordinal
    (le_inf collapseOrdinal_countableInitialSegments collapseOrdinal_continuum_atMost)

/-- The selected actual witness forces the entire finite criterion. -/
theorem collapse_forced :
    ⊤ ⊩[V collapse_algebra.𝔹_collapse] tr Criterion := by
  change (⊤ : collapse_algebra.𝔹_collapse) ≤
    ⟦tr Criterion⟧[V collapse_algebra.𝔹_collapse]
  rw [boolean_realize_Criterion]
  exact le_iSup_of_le collapseOrdinal collapseOrdinal_spec

end Boolean

#print axioms tr_Criterion
#print axioms realize_Criterion_raw
#print axioms realize_Criterion
#print axioms criterion_witnesses
#print axioms boolean_realize_Criterion
#print axioms collapseOrdinal_spec
#print axioms collapse_forced

end ClassicismZFC.CountableOrdinalForcing
