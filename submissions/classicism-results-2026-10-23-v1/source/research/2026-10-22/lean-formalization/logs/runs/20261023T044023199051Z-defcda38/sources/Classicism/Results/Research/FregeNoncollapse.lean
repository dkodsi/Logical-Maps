import Classicism.Results.Research.FregeFiniteSets

/-!
# Arithmetic noncollapse, possible realization and the finite-number dichotomy

Direct source: `research/2026-10-22/notes/frege-infinity-20261022-1726.md`,
§§26–27 (unpaginated original research, `misc`).

The bottom cardinality counts nothing; it is not the zero cardinality.
Noncollapse is successor injectivity on INTERNAL numbers. IStar below has the
exact two Peano clauses used by Certified/Arithmetic.lean; ArithmeticI is its
diamond. None is the finite-distinctness schema or actual quantified Infinity.
The dichotomy applies to the numerical domain, not to arbitrary infinite sets.
-/

namespace Classicism.Research.FregeNoncollapse
open Classicism.Paper Classicism.Research.FregeFiniteSets

variable {σ : Type} [Ty σ]

def Bottom : (σ → Prop) → Prop := fun _ => False

def Noncollapse (σ : Type) [Ty σ] : Prop :=
  ∀ m n : (σ → Prop) → Prop, FiniteCardinality m → FiniteCardinality n →
    SucCard m = SucCard n → m = n

def IStar (σ : Type) [Ty σ] : Prop :=
  ∀ m n : (σ → Prop) → Prop, FiniteCardinality m → FiniteCardinality n →
    ZeroCard σ ≠ SucCard m ∧ (SucCard m = SucCard n → m = n)

def ArithmeticI (σ : Type) [Ty σ] : Prop := ◇ IStar σ

theorem istar_iff_noncollapse : IStar σ ↔ Noncollapse σ :=
  ⟨fun h m n hm hn => (h m n hm hn).2,
    fun h m n hm hn => ⟨frege_zero_ne_suc m, h m n hm hn⟩⟩

theorem successor_bottom : SucCard (Bottom (σ := σ)) = Bottom :=
  funext (fun X => propext
    ⟨fun h => h.elim fun _ hy => hy.2, False.elim⟩)

theorem zero_ne_bottom : ZeroCard σ ≠ (Bottom : (σ → Prop) → Prop) :=
  frege_realized_ne_bottom (ZeroCard σ) ⟨(fun _ => False), fun _ h => h⟩

theorem bottom_iff_necessarily_empty (n : (σ → Prop) → Prop) :
    n = Bottom ↔ □ (∀ X, ¬ n X) := by
  constructor
  · intro he
    exact modal_K _ _ (nec% (fun (h : n = Bottom) (X : σ → Prop) (hx : n X) =>
      Eq.mp (congrFun h X) hx)) (necessity_of_identity _ _ he)
  · intro he
    exact intensionality n Bottom (modal_K _ _
      (nec% (fun (h : ∀ X, ¬ n X) (X : σ → Prop) =>
        (show n X ↔ Bottom X from ⟨h X, False.elim⟩))) he)

theorem ne_bottom_iff_possible_instance (n : (σ → Prop) → Prop) :
    n ≠ Bottom ↔ ◇ (∃ X, n X) := by
  constructor
  · exact dia_exists_of_ne_bot n
  · intro hp he
    exact not_dia_of_box_not _ (modal_K _ _
      (nec% (fun (h : ∀ X, ¬ n X) (hex : ∃ X, n X) =>
        hex.elim fun X hx => h X hx)) ((bottom_iff_necessarily_empty n).1 he)) hp

/-- The only possible collision of distinct numerical successors is at bottom. -/
theorem successor_collision_bottom (m n : (σ → Prop) → Prop)
    (hm : FiniteCardinality m) (hn : FiniteCardinality n)
    (hne : m ≠ n) (he : SucCard m = SucCard n) : SucCard m = Bottom := by
  apply (frege_cardinal_exclusivity m hm n hn).elim
  · intro hmn
    exact (hne hmn).elim
  · intro hdis
    have hsdis : □ (∀ X, ¬ (SucCard m X ∧ SucCard n X)) :=
      modal_K _ _ (modal_K _ _ (nec% (frege_suc_disjoint m n))
        (frege_number_persistent n hn)) hdis
    apply (bottom_iff_necessarily_empty (SucCard m)).2
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (h : ∀ X, ¬ (SucCard m X ∧ SucCard n X))
        (e : SucCard m = SucCard n) (X : σ → Prop) (hx : SucCard m X) =>
          h X ⟨hx, Eq.mp (congrFun e X) hx⟩)) hsdis)
      (necessity_of_identity _ _ he)

theorem noncollapse_of_bottom_not_number
    (hbot : ¬ FiniteCardinality (Bottom (σ := σ))) : Noncollapse σ := by
  intro m n hm hn he
  exact (em (m = n)).elim id (fun hne =>
    (hbot ((successor_collision_bottom m n hm hn hne he) ▸
      finiteCardinality_suc m hm)).elim)

theorem no_numerical_fixed_point (h : Noncollapse σ)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) : n ≠ SucCard n := by
  refine (hn (fun m => FiniteCardinality m ∧ m ≠ SucCard m) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, frege_zero_ne_suc (ZeroCard σ)⟩
  · intro m hm
    exact ⟨finiteCardinality_suc m hm.1, fun he =>
      hm.2 (h m (SucCard m) hm.1 (finiteCardinality_suc m hm.1) he)⟩

theorem bottom_not_number_of_noncollapse (h : Noncollapse σ) :
    ¬ FiniteCardinality (Bottom (σ := σ)) :=
  fun hb => no_numerical_fixed_point h Bottom hb successor_bottom.symm

theorem noncollapse_iff_bottom_not_number :
    Noncollapse σ ↔ ¬ FiniteCardinality (Bottom (σ := σ)) :=
  ⟨bottom_not_number_of_noncollapse, noncollapse_of_bottom_not_number⟩

theorem noncollapse_iff_possible_realization : Noncollapse σ ↔
    ∀ n : (σ → Prop) → Prop, FiniteCardinality n → ◇ (∃ X, n X) := by
  constructor
  · intro h n hn
    apply (ne_bottom_iff_possible_instance n).1
    intro he
    exact bottom_not_number_of_noncollapse h (he ▸ hn)
  · intro h
    apply noncollapse_of_bottom_not_number
    intro hb
    exact (ne_bottom_iff_possible_instance Bottom).2 (h Bottom hb) rfl

theorem bottom_number_not_istar (hb : FiniteCardinality (Bottom (σ := σ))) :
    ¬ IStar σ := fun h => bottom_not_number_of_noncollapse
      (istar_iff_noncollapse.1 h) hb

theorem arithmeticI_iff_istar : ArithmeticI σ ↔ IStar σ := by
  constructor
  · intro hp
    apply (em (FiniteCardinality (Bottom (σ := σ)))).elim
    · intro hb
      exact (not_dia_of_box_not _ (modal_K _ _
        (nec% (bottom_number_not_istar (σ := σ)))
        (frege_number_persistent Bottom hb)) hp).elim
    · intro hb
      exact istar_iff_noncollapse.2 (noncollapse_of_bottom_not_number hb)
  · exact dia_intro _

theorem infinity_implies_noncollapse (h : Classicism.P.AxiomOfInfinity σ) :
    Noncollapse σ := fun m n hm hn => frege_infinity_suc_injective h m n hm hn

/-- A finite successor path exists even when the endpoint has collapsed. -/
theorem finite_successor_path (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    ∃ A : ((σ → Prop) → Prop) → Prop, Finite A ∧ A (ZeroCard σ) ∧ A n ∧
      (∀ m, A m → FiniteCardinality m) ∧
      ∀ m, A m → m ≠ n → A (SucCard m) := by
  refine (hn (fun n => FiniteCardinality n ∧
    ∃ A : ((σ → Prop) → Prop) → Prop, Finite A ∧ A (ZeroCard σ) ∧ A n ∧
      (∀ m, A m → FiniteCardinality m) ∧
      ∀ m, A m → m ≠ n → A (SucCard m)) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, (fun m => m = ZeroCard σ),
      finite_singleton _, rfl, rfl,
      (fun m hm => hm.symm ▸ finiteCardinality_zero), fun _ hm hne => (hne hm).elim⟩
  · intro n hn
    obtain ⟨A, hA, hzero, hend, hnum, hstep⟩ := hn.2
    refine ⟨finiteCardinality_suc n hn.1, (fun m => A m ∨ m = SucCard n),
      finite_adjoin A hA (SucCard n), Or.inl hzero, Or.inr rfl, ?_, ?_⟩
    · intro m hm
      exact hm.elim (hnum m) (fun he => he.symm ▸ finiteCardinality_suc n hn.1)
    · intro m hm hne
      apply hm.elim
      · intro ham
        exact (em (m = n)).elim (fun he => Or.inr (congrArg SucCard he))
          (fun he => Or.inl (hstep m ham he))
      · intro he
        exact (hne he).elim

theorem finite_numbers_of_bottom_number (hb : FiniteCardinality (Bottom (σ := σ))) :
    Finite (FiniteCardinality (σ := σ)) := by
  obtain ⟨A, hA, hzero, hbot, _, hstep⟩ := finite_successor_path Bottom hb
  have hclosed : ∀ m, A m → A (SucCard m) := by
    intro m hm
    exact (em (m = Bottom)).elim
      (fun he => ((congrArg SucCard he).trans successor_bottom).symm ▸ hbot)
      (fun he => hstep m hm he)
  exact finite_subset A FiniteCardinality hA (fun n hn => hn A ⟨hzero, hclosed⟩)

/-- A graph definition valid even when its carrier is the individual sort. -/
def DedekindInfinite {α : Type} [Ty α] (A : α → Prop) : Prop :=
  ∃ R : α → α → Prop,
    (∀ x, A x → ∃ y, R x y) ∧
    (∀ x y, A x → R x y → A y) ∧
    (∀ x y z, A x → R x y → R x z → y = z) ∧
    (∀ x z y, A x → A z → R x y → R z y → x = z) ∧
    ∃ y, A y ∧ ∀ x, A x → ¬ R x y

theorem dedekind_not_finite {α : Type} [Ty α] (A : α → Prop)
    (hd : DedekindInfinite A) : ¬ Finite A := by
  intro hf
  obtain ⟨R, ht, hc, hs, hi, y, hy, hmiss⟩ := hd
  obtain ⟨x, hx, hxy⟩ := finite_self_injection_surjective A R hf ht hc hs hi y hy
  exact hmiss x hx hxy

theorem noncollapse_dedekind (h : Noncollapse σ) :
    DedekindInfinite (FiniteCardinality (σ := σ)) := by
  refine ⟨(fun n m => FiniteCardinality n ∧ FiniteCardinality m ∧ SucCard n = m),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact ⟨SucCard n, hn, finiteCardinality_suc n hn, rfl⟩
  · intro n m _ hnm
    exact hnm.2.1
  · intro n m k _ hnm hnk
    exact hnm.2.2.symm.trans hnk.2.2
  · intro n m k hn hm hnk hmk
    exact h n m hn hm (hnk.2.2.trans hmk.2.2.symm)
  · exact ⟨ZeroCard σ, finiteCardinality_zero,
      fun n _ hn0 => frege_zero_ne_suc n hn0.2.2.symm⟩

theorem finite_numbers_iff_bottom_number : Finite (FiniteCardinality (σ := σ)) ↔
    FiniteCardinality (Bottom (σ := σ)) := by
  constructor
  · intro hf
    exact (em (FiniteCardinality (Bottom (σ := σ)))).elim id (fun hb =>
      (dedekind_not_finite _ (noncollapse_dedekind (noncollapse_of_bottom_not_number hb)) hf).elim)
  · exact finite_numbers_of_bottom_number

theorem infinite_numbers_iff_noncollapse : ¬ Finite (FiniteCardinality (σ := σ)) ↔
    Noncollapse σ :=
  ⟨fun hf => noncollapse_of_bottom_not_number
      (fun hb => hf (finite_numbers_of_bottom_number hb)),
    fun h => dedekind_not_finite _ (noncollapse_dedekind h)⟩

theorem infinite_numbers_iff_dedekind : ¬ Finite (FiniteCardinality (σ := σ)) ↔
    DedekindInfinite (FiniteCardinality (σ := σ)) :=
  ⟨fun h => noncollapse_dedekind (infinite_numbers_iff_noncollapse.1 h),
    dedekind_not_finite _⟩

theorem finite_universe_of_bottom_number (hb : FiniteCardinality (Bottom (σ := σ))) :
    Finite (fun _ : σ => True) :=
  (em (Finite (fun _ : σ => True))).elim id (fun hf =>
    (bottom_not_number_of_noncollapse (infinity_implies_noncollapse hf) hb).elim)

theorem necessary_finiteness_of_bottom_number
    (hb : FiniteCardinality (Bottom (σ := σ))) :
    □ (Finite (fun _ : σ => True)) ∧ □ (Finite (FiniteCardinality (σ := σ))) :=
  ⟨modal_K _ _ (nec% (finite_universe_of_bottom_number (σ := σ)))
      (frege_number_persistent Bottom hb),
    modal_K _ _ (nec% (finite_numbers_of_bottom_number (σ := σ)))
      (frege_number_persistent Bottom hb)⟩

/-- The finite case has a last nonbottom number before its absorbing bottom. -/
theorem last_possible_cardinality (hb : FiniteCardinality (Bottom (σ := σ))) :
    ∃ m : (σ → Prop) → Prop,
      FiniteCardinality m ∧ m ≠ Bottom ∧ SucCard m = Bottom := by
  have hp : ∀ n : (σ → Prop) → Prop, FiniteCardinality n →
      n ≠ Bottom ∨ ∃ m, FiniteCardinality m ∧ m ≠ Bottom ∧ SucCard m = Bottom := by
    intro n hn
    refine (hn (fun n => FiniteCardinality n ∧ (n ≠ Bottom ∨
      ∃ m, FiniteCardinality m ∧ m ≠ Bottom ∧ SucCard m = Bottom)) ⟨?_, ?_⟩).2
    · exact ⟨finiteCardinality_zero, Or.inl zero_ne_bottom⟩
    · intro n hn
      refine ⟨finiteCardinality_suc n hn.1, ?_⟩
      apply (em (SucCard n = Bottom)).elim
      · intro he
        apply (em (n = Bottom)).elim
        · intro hnb
          exact hn.2.elim (fun hne => (hne hnb).elim) Or.inr
        · intro hnb
          exact Or.inr ⟨n, hn.1, hnb, he⟩
      · exact Or.inl
  exact (hp Bottom hb).elim (fun h => (h rfl).elim) id

end Classicism.Research.FregeNoncollapse
