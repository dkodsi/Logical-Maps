import Flypitch4.Erdos501.InternalField

/-!
# The internal natural numbers of an actual Boolean-valued real field

Original source, misc, 23 October 2026. The name below has the finite sums of
one as its Boolean-valued members. We prove that it is least among ALL
internally represented inductive subsets and construct an actual set graph
of a bijection from the Boolean-valued omega. External induction is used only
to establish facts about names in the Boolean-valued universe; no assertion
of external standardness is made about a subsequently extracted ordinary
membership model. No natural-number coding hypothesis is assumed.
-/

open Flypitch bSet Lattice Flypitch.Erdos501
open scoped Flypitch

namespace ClassicismZFC.BooleanNaturals

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

noncomputable def naturals (F : Fld β) : bSet β :=
  Fld.seqName (fun n => F.mulN n F.one)

def Inductive (F : Fld β) (A : bSet β) : β :=
  (⨅ x, x ∈ᴮ A ⟹ x ∈ᴮ F.R) ⊓
  (F.zero ∈ᴮ A ⊓
    ⨅ x, ⨅ y, x ∈ᴮ F.R ⟹ (y ∈ᴮ F.R ⟹ (x ∈ᴮ A ⟹
      (Sem.app2 F.plus x F.one y ⟹ y ∈ᴮ A))))

def LeastInductive (F : Fld β) (N : bSet β) : β :=
  Inductive F N ⊓
    ⨅ A, Inductive F A ⟹ ⨅ x, x ∈ᴮ N ⟹ x ∈ᴮ A

/-- Pointwise graph support, matching the ordinary source graph predicate. -/
def Supported (A B G : bSet β) : β :=
  ⨅ x, ⨅ y, pair x y ∈ᴮ G ⟹ (x ∈ᴮ A ⊓ y ∈ᴮ B)

def Bijection (A B G : bSet β) : β :=
  Supported A B G ⊓ (is_func G ⊓ (is_total A B G ⊓
    (is_inj G ⊓ is_surj A B G)))

lemma mem_naturals (F : Fld β) (x : bSet β) :
    (x ∈ᴮ naturals F) = ⨆ n : ℕ, x =ᴮ F.mulN n F.one :=
  Fld.mem_seqName _ x

lemma numeral_mem (F : Fld β) (n : ℕ) {Γ : β} :
    Γ ≤ F.mulN n F.one ∈ᴮ naturals F :=
  Fld.seqName_mem (Γ := Γ) (fun k => F.mulN k F.one) n

lemma naturals_mem_field (F : Fld β) {Γ : β} (H : Γ ≤ F.COF)
    {x : bSet β} (hx : Γ ≤ x ∈ᴮ naturals F) : Γ ≤ x ∈ᴮ F.R := by
  rw [mem_naturals] at hx
  apply BV.iSup_elim hx
  intro n Δ hΔ heq
  exact mem_congr (bv_symm heq) bv_refl
    (F.mulN_mem (hΔ.trans H) (F.cof_one_mem (hΔ.trans H)) n)

lemma successor_mem (F : Fld β) {Γ : β} (H : Γ ≤ F.COF)
    {x y : bSet β} (hx : Γ ≤ x ∈ᴮ naturals F)
    (hadd : Γ ≤ Sem.app2 F.plus x F.one y) :
    Γ ≤ y ∈ᴮ naturals F := by
  have hxR := naturals_mem_field F H hx
  rw [mem_naturals] at hx
  apply BV.iSup_elim hx
  intro n Δ hΔ heq
  have H' := hΔ.trans H
  have hyadd := F.add_unique H' (hΔ.trans hxR) (F.cof_one_mem H')
    (hΔ.trans hadd)
  have haddEq := F.add_congr_left H' (hΔ.trans hxR) (F.cof_one_mem H') heq
  have hy : Δ ≤ y =ᴮ F.mulN (n + 1) F.one := bv_trans hyadd haddEq
  exact mem_congr (bv_symm hy) bv_refl (numeral_mem F (n + 1))

lemma naturals_inductive (F : Fld β) {Γ : β} (H : Γ ≤ F.COF) :
    Γ ≤ Inductive F (naturals F) := by
  refine le_inf ?_ (le_inf ?_ ?_)
  · apply le_iInf; intro x
    rw [← deduction]
    exact naturals_mem_field F (inf_le_left.trans H) inf_le_right
  · exact numeral_mem F 0
  · apply le_iInf; intro x
    apply le_iInf; intro y
    rw [← deduction, ← deduction, ← deduction, ← deduction]
    exact successor_mem F
      (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H))))
      (inf_le_left.trans inf_le_right) inf_le_right

lemma numeral_mem_inductive (F : Fld β) {Γ : β} (H : Γ ≤ F.COF)
    {A : bSet β} (hA : Γ ≤ Inductive F A) :
    ∀ n : ℕ, Γ ≤ F.mulN n F.one ∈ᴮ A := by
  intro n
  induction n with
  | zero => exact hA.trans (inf_le_right.trans inf_le_left)
  | succ n ih =>
    have hn := F.mulN_mem H (F.cof_one_mem H) n
    have hn' := F.mulN_mem H (F.cof_one_mem H) (n + 1)
    have hs := hA.trans (inf_le_right.trans inf_le_right)
    have hs' := hs.trans (iInf_le _ (F.mulN n F.one) |>.trans
      (iInf_le _ (F.mulN (n + 1) F.one)))
    have hadd : Γ ≤ Sem.app2 F.plus (F.mulN n F.one) F.one
        (F.mulN (n + 1) F.one) := by
      simpa only [Fld.mulN_succ] using F.add_app2 H hn (F.cof_one_mem H)
    exact BV.mp (BV.mp (BV.mp (BV.mp hs' hn) hn') ih)
      hadd

lemma naturals_least (F : Fld β) {Γ : β} (H : Γ ≤ F.COF)
    {A x : bSet β} (hA : Γ ≤ Inductive F A)
    (hx : Γ ≤ x ∈ᴮ naturals F) : Γ ≤ x ∈ᴮ A := by
  rw [mem_naturals] at hx
  apply BV.iSup_elim hx
  intro n Δ hΔ heq
  exact mem_congr (bv_symm heq) bv_refl
    (numeral_mem_inductive F (hΔ.trans H) (hΔ.trans hA) n)

theorem naturals_leastInductive (F : Fld β) {Γ : β} (H : Γ ≤ F.COF) :
    Γ ≤ LeastInductive F (naturals F) := by
  refine le_inf (naturals_inductive F H) ?_
  apply le_iInf; intro A
  rw [← deduction]
  apply le_iInf; intro x
  rw [← deduction]
  exact naturals_least F (inf_le_left.trans (inf_le_left.trans H))
    (inf_le_left.trans inf_le_right) inf_le_right

lemma unequal_numerals (F : Fld β) (H : (⊤ : β) ≤ F.COF)
    {n m : ℕ} (hnm : n ≠ m) : (F.mulN n F.one =ᴮ F.mulN m F.one) ≤ ⊥ := by
  let Δ := F.mulN n F.one =ᴮ F.mulN m F.one
  have H' : Δ ≤ F.COF := le_top.trans H
  rcases lt_or_gt_of_ne hnm with h | h
  · exact F.bot_of_lt_of_eq H' (F.mulN_mem H' (F.cof_one_mem H') n)
      (F.mulN_lt_mulN_left H' (F.cof_one_mem H') (F.zero_lt_one H') h) le_rfl
  · exact F.bot_of_lt_of_eq H' (F.mulN_mem H' (F.cof_one_mem H') m)
      (F.mulN_lt_mulN_left H' (F.cof_one_mem H') (F.zero_lt_one H') h)
      (bv_symm le_rfl)

private theorem numeralMap_congr (F : Fld β) :
    ∀ i j : (omega : bSet β).type,
      omega.func i =ᴮ omega.func j ≤ F.mulN i.down F.one =ᴮ F.mulN j.down F.one := by
  intro i j
  by_cases h : i.down = j.down
  · rw [h]; exact bv_refl
  · simp only [omega_func, of_nat_inj' h]
    exact bot_le

/-- The graph is a name in the universe, not an external function on a model. -/
noncomputable def numeralGraph (F : Fld β) : bSet β :=
  functionMk (fun i : (omega : bSet β).type => F.mulN i.down F.one)
    (numeralMap_congr F)

lemma numeralGraph_self (F : Fld β) (n : ℕ) {Γ : β} :
    Γ ≤ pair (of_nat n) (F.mulN n F.one) ∈ᴮ numeralGraph F := by
  have h := functionMk_self (u := (omega : bSet β))
    (F := fun i : (omega : bSet β).type => F.mulN i.down F.one)
    (h_congr := numeralMap_congr F) (i := ULift.up n)
  change (⊤ : β) ≤ pair (of_nat n) (F.mulN n F.one) ∈ᴮ numeralGraph F at h
  exact le_top.trans h

lemma numeralGraph_supported (F : Fld β) :
    (⊤ : β) ≤ Supported omega (naturals F) (numeralGraph F) := by
  apply le_iInf; intro x
  apply le_iInf; intro y
  rw [← deduction, top_inf_eq]
  have he : pair x y ∈ᴮ numeralGraph F ≤
      ⨆ i : (omega : bSet β).type,
        pair x y =ᴮ pair (of_nat i.down) (F.mulN i.down F.one) := by
    rw [mem_unfold]
    change (⨆ i : (omega : bSet β).type, (omega : bSet β).bval i ⊓
      pair x y =ᴮ pair ((omega : bSet β).func i) (F.mulN i.down F.one)) ≤ _
    simpa only [omega_bval, omega_func, top_inf_eq] using
      (le_refl (⨆ i : (omega : bSet β).type,
        pair x y =ᴮ pair (of_nat i.down) (F.mulN i.down F.one)))
  apply BV.iSup_elim he
  intro i Δ _ hi
  obtain ⟨hx, hy⟩ := eq_of_eq_pair hi
  exact le_inf (mem_congr (bv_symm hx) bv_refl of_nat_mem_omega)
    (mem_congr (bv_symm hy) bv_refl (numeral_mem F i.down))

lemma numeralGraph_total (F : Fld β) :
    (⊤ : β) ≤ is_total omega (naturals F) (numeralGraph F) := by
  apply is_total_iff_is_total'.mpr
  apply le_iInf; intro i
  rw [← deduction]
  apply le_iSup_of_le i.down
  exact le_inf le_top (numeralGraph_self F i.down)

lemma numeralGraph_surjective (F : Fld β) :
    (⊤ : β) ≤ is_surj omega (naturals F) (numeralGraph F) := by
  apply le_iInf; intro y
  rw [← deduction, top_inf_eq]
  rw [mem_naturals]
  apply iSup_le; intro n
  apply le_iSup_of_le (of_nat n)
  refine le_inf of_nat_mem_omega ?_
  exact mem_congr (pair_congr bv_refl (bv_symm le_rfl)) bv_refl
    (numeralGraph_self F n)

theorem numeralGraph_bijection (F : Fld β) (H : (⊤ : β) ≤ F.COF) :
    (⊤ : β) ≤ Bijection omega (naturals F) (numeralGraph F) := by
  refine le_inf (numeralGraph_supported F) (le_inf ?_ (le_inf
    (numeralGraph_total F) (le_inf ?_ (numeralGraph_surjective F))))
  · exact functionMk_is_func _ (numeralMap_congr F)
  · apply functionMk_inj_of_inj _ (numeralMap_congr F)
    intro i j hij
    apply unequal_numerals F H
    intro h
    apply hij
    exact ULift.ext i j h

theorem field_natural_witnesses (F : Fld β) (H : (⊤ : β) ≤ F.COF) :
    ∃ N G : bSet β, (⊤ : β) ≤ LeastInductive F N ⊓ Bijection omega N G :=
  ⟨naturals F, numeralGraph F,
    le_inf (naturals_leastInductive F H) (numeralGraph_bijection F H)⟩

#print axioms field_natural_witnesses

end ClassicismZFC.BooleanNaturals
