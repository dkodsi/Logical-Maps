import Classicism.Results.Research.FregeNoncollapse
import Classicism.Results.Records.C5

/-!
# C5 Frege realization, null collapse and exact Infinity equivalences

Direct source: `research/2026-10-22/notes/frege-infinity-20261022-1726.md`,
§20.1–§20.3 and §27.2 (unpaginated original research, `misc`).

C5 is the displayed BOXED ND_t premise. Atomicity, Actuality, Choice and rigid
comprehension are not premises. The proof constructs the finite-count stability
argument, rather than assuming numerical extensionality or a core interpretation.
-/

namespace Classicism.Research.C5Frege
open Classicism.Paper
open Classicism.Research.FregeNoncollapse
open Classicism.Research.FregeFiniteSets

variable {σ : Type} [Ty σ]

def Settled (p : Prop) : Prop := (p → □ p) ∧ (¬ p → □ (¬ p))

theorem settled_neg (p : Prop) (h : Settled p) : Settled (¬ p) := by
  refine ⟨h.2, ?_⟩
  intro hn
  have hp : p := (em p).elim id (fun hp => (hn hp).elim)
  exact modal_K _ _ (nec% (fun (hp : p) (hn : ¬ p) => hn hp)) (h.1 hp)

theorem settled_and (p q : Prop) (hp : Settled p) (hq : Settled q) :
    Settled (p ∧ q) := by
  constructor
  · intro h
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hp : p) (hq : q) => And.intro hp hq)) (hp.1 h.1)) (hq.1 h.2)
  · intro h
    apply (em p).elim
    · intro hpt
      exact modal_K _ _ (nec% (fun (hn : ¬ q) (ha : p ∧ q) => hn ha.2))
        (hq.2 (fun hqt => h ⟨hpt, hqt⟩))
    · intro hpn
      exact modal_K _ _ (nec% (fun (hn : ¬ p) (ha : p ∧ q) => hn ha.1)) (hp.2 hpn)

theorem settled_all (F : σ → Prop)
    (bf : ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x))
    (hF : ∀ x, Settled (F x)) : Settled (∀ x, F x) := by
  constructor
  · intro h
    exact bf F (fun x => (hF x).1 (h x))
  · intro h
    obtain ⟨x, hx⟩ := frege_outside_of_not_universal F h
    exact modal_K _ _ (nec% (fun (hx : ¬ F x) (hall : ∀ x, F x) => hx (hall x)))
      ((hF x).2 hx)

theorem settled_exists (F : σ → Prop)
    (bf : ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x))
    (hF : ∀ x, Settled (F x)) : Settled (∃ x, F x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact modal_K _ _ (nec% (fun (hx : F x) => (show ∃ x, F x from ⟨x, hx⟩)))
      ((hF x).1 hx)
  · intro h
    exact modal_K _ _ (nec% (fun (hn : ∀ x, ¬ F x) (he : ∃ x, F x) =>
      he.elim fun x hx => hn x hx))
      (bf (fun x => ¬ F x) (fun x => (hF x).2 (fun hx => h ⟨x, hx⟩)))

theorem persistent_membership_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (X : σ → Prop) (hX : Persistent X) (a : σ) : Settled (X a) := by
  have hp : □ (X a → □ (X a)) := converse_barcan (fun x => X x → □ (X x)) hX a
  refine ⟨modal_T _ hp, ?_⟩
  intro hn
  apply (em (◇ (X a))).elim
  · intro hd
    exact (hn (Proofs.b_dia_box_imp (Proofs.b_of_nd_t (modal_T _ c5)) (X a)
      (dia_mono _ _ hp hd))).elim
  · exact box_not_of_not_dia _

theorem deletion_weakly_persistent (X : σ → Prop) (a : σ) :
    WeaklyPersistent X → (∀ x y : σ, x ≠ y → □ (x ≠ y)) →
      WeaklyPersistent (fun x => X x ∧ x ≠ a) := by
  intro hX hnd x hx
  exact modal_K _ _ (modal_K _ _
    (nec% (fun (h : X x) (hne : x ≠ a) => And.intro h hne)) (hX x hx.1))
    (hnd x a hx.2)

theorem deletion_persistent
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (X : σ → Prop) (hX : Persistent X) (a : σ) :
    Persistent (fun x => X x ∧ x ≠ a) :=
  modal_K _ _ (modal_K _ _ (nec% (deletion_weakly_persistent X a)) hX)
    (Proofs.necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r
      (σ := σ) c5)

theorem persistent_count_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    ∀ X : σ → Prop, Persistent X → Settled (n X) := by
  apply hn (fun m => ∀ X : σ → Prop, Persistent X → Settled (m X))
  constructor
  · intro X hX
    exact settled_all (fun x => ¬ X x) (Proofs.bf_of_box_nd_t c5)
      (fun x => settled_neg (X x) (persistent_membership_settled c5 X hX x))
  · intro m hm X hX
    exact settled_exists (fun a => X a ∧ m (fun x => X x ∧ x ≠ a))
      (Proofs.bf_of_box_nd_t c5) (fun a => settled_and _ _
        (persistent_membership_settled c5 X hX a)
        (hm (fun x => X x ∧ x ≠ a) (deletion_persistent c5 X hX a)))

theorem top_persistent : Persistent (fun _ : σ => True) :=
  nec% (fun (_ : σ) (_ : True) => (show □ True from rfl))

theorem finite_top_excludes_successor (n : (σ → Prop) → Prop) :
    FiniteCardinality n → n (fun _ => True) → ∀ Y : σ → Prop, ¬ SucCard n Y :=
  fun hn htop Y => finite_upper_bound n hn Y (fun _ => True) htop
    (fun _ _ => True.intro)

theorem realized_or_bottom
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    (∃ X, n X) ∨ n = Bottom := by
  refine (hn (fun m => FiniteCardinality m ∧ ((∃ X, m X) ∨ m = Bottom)) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, Or.inl ⟨(fun _ => False), fun _ h => h⟩⟩
  · intro m hm
    refine ⟨finiteCardinality_suc m hm.1, ?_⟩
    apply hm.2.elim
    · intro hex
      obtain ⟨X, hX⟩ := hex
      apply (em (∀ x, X x)).elim
      · intro hall
        have htop : m (fun _ => True) := finiteCardinality_coext m hm.1 X _ hX
          (fun x => ⟨fun _ => True.intro, fun _ => hall x⟩)
        have hboxtop : □ (m (fun _ => True)) :=
          (persistent_count_settled c5 m hm.1 _ top_persistent).1 htop
        exact Or.inr ((bottom_iff_necessarily_empty (SucCard m)).2
          (modal_K _ _ (modal_K _ _ (nec% (finite_top_excludes_successor m))
            (frege_number_persistent m hm.1)) hboxtop))
      · intro hall
        obtain ⟨a, ha⟩ := frege_outside_of_not_universal X hall
        exact Or.inl ⟨(fun x => X x ∨ x = a), frege_fresh_point m hm.1 X a hX ha⟩
    · intro he
      exact Or.inr ((congrArg SucCard he).trans successor_bottom)

theorem null_collapse
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hempty : ∀ X, ¬ n X) : n = Bottom :=
  (realized_or_bottom c5 n hn).elim
    (fun h => (h.elim fun X hX => hempty X hX).elim) id

theorem numerical_extensionality
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (m n : (σ → Prop) → Prop) (hm : FiniteCardinality m)
    (hn : FiniteCardinality n) (hext : ∀ X, m X ↔ n X) : m = n := by
  apply (realized_or_bottom c5 m hm).elim
  · intro hex
    obtain ⟨X, hX⟩ := hex
    exact frege_common_instance_eq m n hm hn X hX ((hext X).1 hX)
  · intro hmb
    have hnb : n = Bottom := null_collapse c5 n hn
      (fun X hnX => Eq.mp (congrFun hmb X) ((hext X).2 hnX))
    exact hmb.trans hnb.symm

theorem infinity_iff_noncollapse
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) :
    Classicism.P.AxiomOfInfinity σ ↔ Noncollapse σ := by
  constructor
  · exact infinity_implies_noncollapse
  · intro hNC
    apply infinity_iff_realizes.2
    intro n hn
    exact (realized_or_bottom c5 n hn).elim id (fun he =>
      (bottom_not_number_of_noncollapse hNC (he ▸ hn)).elim)

theorem infinity_iff_bottom_not_number
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) :
    Classicism.P.AxiomOfInfinity σ ↔ ¬ FiniteCardinality (Bottom (σ := σ)) :=
  (infinity_iff_noncollapse c5).trans noncollapse_iff_bottom_not_number

theorem infinity_iff_arithmeticI
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) :
    Classicism.P.AxiomOfInfinity σ ↔ ArithmeticI σ :=
  (infinity_iff_noncollapse c5).trans
    (istar_iff_noncollapse.symm.trans arithmeticI_iff_istar.symm)

theorem finite_base_iff_numbers
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) :
    Finite (fun _ : σ => True) ↔ Finite (FiniteCardinality (σ := σ)) := by
  constructor
  · intro hf
    apply finite_numbers_of_bottom_number
    exact (em (FiniteCardinality (Bottom (σ := σ)))).elim id (fun hb =>
      (((infinity_iff_noncollapse c5).2 (noncollapse_of_bottom_not_number hb)) hf).elim)
  · intro hf
    exact finite_universe_of_bottom_number (finite_numbers_iff_bottom_number.1 hf)

end Classicism.Research.C5Frege
