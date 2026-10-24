import ClassicismZFC.RealFieldForcing
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Internally coded injections between the chosen real fields and P(omega)

The random-model injection uses a genuine measurable injection of Cantor space
into the reals, the proved Borel reading of every internal subset of omega,
and the actual `functionMk'` graph construction. Equality of readings is
computed as a Boolean value, so the construction descends to names.

The collapse-model reverse injection first uses the existing proved
`continuum_le_continuum_check`, then encodes ground-model subsets of omega by
their characteristic sequences. Its graph is again `functionMk'`.

The field-to-powerset direction is literal inclusion in both constructions:
the checked rational cuts encode rationals by natural numbers, and random
real names already are subsets of omega. All outputs are Boolean-valued
statements about internal graph codes, not external carrier injections.

Source: the pinned Flypitch Project (Apache 2.0), `BvmExtras` functionMk',
`ForcingCH` continuum_le_continuum_check, `Erdos501/BorelNames` and
`InternalReals`; Mathlib's measurableEmbedding_embeddingReal. New compositions
and code maps are original metatheoretic adapters. No compiler has been run.
-/

open MeasureTheory Set Flypitch bSet Lattice
open Flypitch.Erdos501
open scoped Flypitch Fol

namespace ClassicismZFC.RealFieldCardinalCoding

noncomputable section

/-- One fixed genuine measurable injection, rather than ambiguous binary expansion. -/
def cantorCode : (ℕ → Bool) → ℝ := MeasureTheory.embeddingReal (ℕ → Bool)

theorem cantorCode_measurable : Measurable cantorCode :=
  MeasureTheory.measurable_embeddingReal (ℕ → Bool)

theorem cantorCode_injective : Function.Injective cantorCode :=
  (MeasureTheory.measurableEmbedding_embeddingReal (ℕ → Bool)).injective

section Random

open RandomForcing

variable {ι : Type}

private theorem powerset_entry_definite
    (i : (bv_powerset (omega : bSet (randomAlgebra ι))).type) :
    (⊤ : randomAlgebra ι) ≤ (bv_powerset omega).func i ⊆ᴮ omega :=
  check_set_of_indicator_subset

private theorem exists_power_reading
    (i : (bv_powerset (omega : bSet (randomAlgebra ι))).type) :
    ∃ f : RealCode ι,
      (⊤ : randomAlgebra ι) ≤ (bv_powerset omega).func i =ᴮ mkReal f.1 f.2 := by
  obtain ⟨f, hf, S, hS, hdep, heq⟩ :=
    exists_mkReal_bv_eq ((bv_powerset omega).func i) (powerset_entry_definite i)
  exact ⟨⟨f, hf⟩, heq⟩

/-- A Borel reading selected only after its actual existence theorem. -/
def powerReading (i : (bv_powerset (omega : bSet (randomAlgebra ι))).type) :
    RealCode ι := Classical.choose (exists_power_reading i)

theorem powerReading_spec (i : (bv_powerset (omega : bSet (randomAlgebra ι))).type) :
    (⊤ : randomAlgebra ι) ≤
      (bv_powerset omega).func i =ᴮ mkReal (powerReading i).1 (powerReading i).2 :=
  Classical.choose_spec (exists_power_reading i)

/-- The target element of Rdot, obtained by the measurable Cantor injection. -/
def randomIndexMap (i : (bv_powerset (omega : bSet (randomAlgebra ι))).type) :
    (Rdot : bSet (randomAlgebra ι)).type :=
  ⟨cantorCode ∘ (powerReading i).1,
    cantorCode_measurable.comp (powerReading i).2⟩

private theorem encoded_reading_eq (f g : RealCode ι) :
    (realName (cantorCode ∘ f.1) (cantorCode_measurable.comp f.2) =ᴮ
      realName (cantorCode ∘ g.1) (cantorCode_measurable.comp g.2)) =
      (mkReal f.1 f.2 =ᴮ mkReal g.1 g.2) := by
  rw [bv_eq_realName, bv_eq_mkReal]
  apply MeasureAlgebra.mk_congr
  ext x
  exact cantorCode_injective.eq_iff

private theorem source_reading_eq
    (i j : (bv_powerset (omega : bSet (randomAlgebra ι))).type) :
    ((bv_powerset omega).func i =ᴮ (bv_powerset omega).func j) =
      (mkReal (powerReading i).1 (powerReading i).2 =ᴮ
        mkReal (powerReading j).1 (powerReading j).2) := by
  apply le_antisymm
  · exact bv_trans (bv_symm (le_top.trans (powerReading_spec i)))
      (bv_trans le_rfl (le_top.trans (powerReading_spec j)))
  · exact bv_trans (le_top.trans (powerReading_spec i))
      (bv_trans le_rfl (bv_symm (le_top.trans (powerReading_spec j))))

/-- Exact Boolean equality preservation and reflection for the proposed map. -/
theorem randomIndexMap_eq
    (i j : (bv_powerset (omega : bSet (randomAlgebra ι))).type) :
    ((Rdot : bSet (randomAlgebra ι)).func (randomIndexMap i) =ᴮ
      Rdot.func (randomIndexMap j)) =
      ((bv_powerset omega).func i =ᴮ (bv_powerset omega).func j) := by
  exact (encoded_reading_eq (powerReading i) (powerReading j)).trans
    (source_reading_eq i j).symm

private theorem randomIndexMap_ext
    (i j : (bv_powerset (omega : bSet (randomAlgebra ι))).type)
    {Γ : randomAlgebra ι}
    (h : Γ ≤ (bv_powerset omega).func i =ᴮ (bv_powerset omega).func j) :
    Γ ≤ (Rdot : bSet (randomAlgebra ι)).func (randomIndexMap i) =ᴮ
      Rdot.func (randomIndexMap j) := by
  rw [randomIndexMap_eq]
  exact h

private theorem randomIndexMap_mem
    (i : (bv_powerset (omega : bSet (randomAlgebra ι))).type)
    {Γ : randomAlgebra ι} (_h : Γ ≤ (bv_powerset omega).bval i) :
    Γ ≤ (Rdot : bSet (randomAlgebra ι)).bval (randomIndexMap i) ∧ Γ ≤ ⊤ :=
  ⟨le_top, le_top⟩

private theorem randomIndexMap_inj
    (i j : (bv_powerset (omega : bSet (randomAlgebra ι))).type)
    {Γ : randomAlgebra ι}
    (h : Γ ≤ (Rdot : bSet (randomAlgebra ι)).func (randomIndexMap i) =ᴮ
      Rdot.func (randomIndexMap j)) :
    Γ ≤ (bv_powerset omega).func i =ᴮ (bv_powerset omega).func j := by
  rw [randomIndexMap_eq] at h
  exact h

/-- An actual internal, supported, injective function graph. -/
def randomPowersetGraph : bSet (randomAlgebra ι) :=
  functionMk' randomIndexMap (fun _ => ⊤) randomIndexMap_ext randomIndexMap_mem

theorem randomPowersetGraph_injective :
    (⊤ : randomAlgebra ι) ≤
      is_injective_function (bv_powerset omega) Rdot randomPowersetGraph :=
  le_inf
    (functionMk'_is_function randomIndexMap (fun _ => ⊤)
      randomIndexMap_ext randomIndexMap_mem)
    (functionMk'_is_inj randomIndexMap (fun _ => ⊤)
      randomIndexMap_ext randomIndexMap_mem randomIndexMap_inj)

theorem random_powerset_to_real :
    (⊤ : randomAlgebra ι) ≤ injects_into (bv_powerset omega) Rdot :=
  injects_into_of_injection_into
    (le_iSup_of_le randomPowersetGraph randomPowersetGraph_injective)

theorem random_real_subset_powerset :
    (⊤ : randomAlgebra ι) ≤ Rdot ⊆ᴮ bv_powerset omega := by
  rw [subset_unfold]
  apply le_iInf
  intro f
  rw [← deduction]
  exact (le_top.trans (bv_powerset_spec.mp (realName_definite (hf := f.2))))

theorem random_real_to_powerset :
    (⊤ : randomAlgebra ι) ≤ injects_into Rdot (bv_powerset omega) :=
  injects_into_of_subset random_real_subset_powerset

end Random

section Checked

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

/-- The checked rational-cut code is a subset of the ground-model omega. -/
theorem codeP_subset_omega (r : ℝ) : CheckReals.codeP r ⊆ PSet.omega := by
  intro q
  exact ⟨⟨Encodable.encode q.1⟩, PSet.Equiv.refl _⟩

theorem checked_real_subset_powerset :
    (⊤ : β) ≤ (CheckReals.Rc : bSet β) ⊆ᴮ bv_powerset omega := by
  rw [subset_unfold]
  apply le_iInf
  intro r
  rw [← deduction]
  exact le_top.trans (bv_powerset_spec.mp (check_subset (codeP_subset_omega r)))

theorem checked_real_to_powerset :
    (⊤ : β) ≤ injects_into (CheckReals.Rc : bSet β) (bv_powerset omega) :=
  injects_into_of_subset checked_real_subset_powerset

/-- Characteristic sequence of an actual ground-model set of natural numbers. -/
def subsetBits (s : PSet.{0}) (n : ℕ) : Bool := by
  classical
  exact decide (PSet.ofNat n ∈ s)

theorem subsetBits_of_equiv {s t : PSet.{0}} (h : PSet.Equiv s t) :
    subsetBits s = subsetBits t := by
  classical
  funext n
  simp only [subsetBits, PSet.Mem.congr_right h]

theorem subsetBits_reflect {s t : PSet.{0}} (hs : s ⊆ PSet.omega)
    (ht : t ⊆ PSet.omega) (h : subsetBits s = subsetBits t) : PSet.Equiv s t := by
  classical
  have hn : ∀ n, PSet.ofNat n ∈ s ↔ PSet.ofNat n ∈ t := by
    intro n
    simpa only [subsetBits, decide_eq_decide] using congrFun h n
  apply PSet.equiv_iff_mem.mpr
  intro z
  constructor
  · intro hz
    obtain ⟨n, hzn⟩ := PSet.mem_of_subset hs hz
    exact (PSet.Mem.congr_left hzn).mpr
      ((hn n.down).mp ((PSet.Mem.congr_left hzn).mp hz))
  · intro hz
    obtain ⟨n, hzn⟩ := PSet.mem_of_subset ht hz
    exact (PSet.Mem.congr_left hzn).mpr
      ((hn n.down).mpr ((PSet.Mem.congr_left hzn).mp hz))

private def checkedSubset
    (i : (check (PSet.powerset PSet.omega) : bSet β).type) : PSet.{0} :=
  (PSet.powerset PSet.omega).Func (check_cast i)

private theorem checkedSubset_sub
    (i : (check (PSet.powerset PSet.omega) : bSet β).type) :
    checkedSubset i ⊆ PSet.omega :=
  PSet.mem_powerset.mp (PSet.func_mem _ _)

/-- The map of indices behind the checked internal graph. -/
def checkedIndexMap
    (i : (check (PSet.powerset PSet.omega) : bSet β).type) :
    (CheckReals.Rc : bSet β).type := cantorCode (subsetBits (checkedSubset i))

private theorem checkedIndexMap_ext
    (i j : (check (PSet.powerset PSet.omega) : bSet β).type) {Γ : β}
    (h : Γ ≤ (check (PSet.powerset PSet.omega) : bSet β).func i =ᴮ
      (check (PSet.powerset PSet.omega)).func j) :
    Γ ≤ (CheckReals.Rc : bSet β).func (checkedIndexMap i) =ᴮ
      CheckReals.Rc.func (checkedIndexMap j) := by
  classical
  by_cases hΓ : Γ = ⊥
  · subst Γ; exact bot_le
  have hp : ⊥ < Γ := bot_lt_iff_ne_bot.mpr hΓ
  rw [check_func, check_func] at h
  have he : PSet.Equiv (checkedSubset i) (checkedSubset j) := check_eq_reflect hp h
  have hr : checkedIndexMap i = checkedIndexMap j :=
    congrArg cantorCode (subsetBits_of_equiv he)
  rw [hr]
  exact bv_refl

private theorem checkedIndexMap_mem
    (i : (check (PSet.powerset PSet.omega) : bSet β).type) {Γ : β}
    (_h : Γ ≤ (check (PSet.powerset PSet.omega) : bSet β).bval i) :
    Γ ≤ (CheckReals.Rc : bSet β).bval (checkedIndexMap i) ∧ Γ ≤ ⊤ :=
  ⟨le_top, le_top⟩

private theorem checkedIndexMap_inj
    (i j : (check (PSet.powerset PSet.omega) : bSet β).type) {Γ : β}
    (h : Γ ≤ (CheckReals.Rc : bSet β).func (checkedIndexMap i) =ᴮ
      CheckReals.Rc.func (checkedIndexMap j)) :
    Γ ≤ (check (PSet.powerset PSet.omega) : bSet β).func i =ᴮ
      (check (PSet.powerset PSet.omega)).func j := by
  classical
  by_cases hΓ : Γ = ⊥
  · subst Γ; exact bot_le
  have hp : ⊥ < Γ := bot_lt_iff_ne_bot.mpr hΓ
  change Γ ≤ check (CheckReals.codeP (checkedIndexMap i)) =ᴮ
    check (CheckReals.codeP (checkedIndexMap j)) at h
  have hr : checkedIndexMap i = checkedIndexMap j :=
    CheckReals.codeP_equiv_iff.mp (check_eq_reflect hp h)
  have hb : subsetBits (checkedSubset i) = subsetBits (checkedSubset j) :=
    cantorCode_injective hr
  rw [check_func, check_func]
  exact check_bv_eq (subsetBits_reflect (checkedSubset_sub i) (checkedSubset_sub j) hb)

def checkedPowersetGraph : bSet β :=
  functionMk' checkedIndexMap (fun _ => ⊤) checkedIndexMap_ext checkedIndexMap_mem

theorem checkedPowersetGraph_injective :
    (⊤ : β) ≤ is_injective_function (check (PSet.powerset PSet.omega))
      CheckReals.Rc checkedPowersetGraph :=
  le_inf
    (functionMk'_is_function checkedIndexMap (fun _ => ⊤)
      checkedIndexMap_ext checkedIndexMap_mem)
    (functionMk'_is_inj checkedIndexMap (fun _ => ⊤)
      checkedIndexMap_ext checkedIndexMap_mem checkedIndexMap_inj)

theorem checked_powerset_to_real :
    (⊤ : β) ≤ injects_into (check (PSet.powerset PSet.omega)) CheckReals.Rc :=
  injects_into_of_injection_into
    (le_iSup_of_le checkedPowersetGraph checkedPowersetGraph_injective)

end Checked

/-- Collapse's existing no-new-subsets injection completes the positive direction. -/
theorem collapse_powerset_to_real :
    (⊤ : collapse_algebra.𝔹_collapse) ≤
      injects_into (bv_powerset omega) CheckReals.Rc :=
  injects_into_trans collapse_algebra.continuum_le_continuum_check checked_powerset_to_real

theorem collapse_real_to_powerset :
    (⊤ : collapse_algebra.𝔹_collapse) ≤
      injects_into CheckReals.Rc (bv_powerset omega) := checked_real_to_powerset

#print axioms random_powerset_to_real
#print axioms random_real_to_powerset
#print axioms collapse_powerset_to_real
#print axioms collapse_real_to_powerset

end

end ClassicismZFC.RealFieldCardinalCoding
