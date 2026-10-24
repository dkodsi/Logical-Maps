import Classicism.Principles.Schematic
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

/-!
# Finitary C lemmas for Strong Possibility

Original research deductions, 22 October 2026; direct source: misc.
This file uses the existing relational type system and the existing `P.BoxNe` /
`P.DiaNe` definitions. It adds no axioms and no infinitary syntax.

Every shallow theorem below is submitted to the gate, the type checker, and the
object-language translator. Until the designated build owner runs these commands
successfully, this file is a proposed formalization, not a checked certificate.

The monism theorem here is the C implication `DiaNe E1 -> E1`. The further SP
conclusion also needs the separate consistency fact `Con(Max + E1)`, whose
coalesced-model construction is not silently assumed in this file.
-/

namespace Classicism.Research.StrongPossibilityConsequences

theorem box_compose (p q r : Prop) :
    □ (p → q) → □ (q → r) → □ (p → r) := fun hpq hqr =>
  modal_K _ _
    (modal_K _ _
      (nec% (fun (f : p → q) (g : q → r) (hp : p) => g (f hp))) hpq) hqr

theorem dia_and_left (p q : Prop) : ◇ (p ∧ q) → ◇ p :=
  dia_mono _ _ (nec% (fun (h : p ∧ q) => h.1))

theorem dia_and_right (p q : Prop) : ◇ (p ∧ q) → ◇ q :=
  dia_mono _ _ (nec% (fun (h : p ∧ q) => h.2))

theorem boxNe_elim (p : Prop) : P.BoxNe p → p := fun ⟨q, hq, hb⟩ =>
  (box_elim hb) (dia_intro q hq)

theorem diaNe_intro (p : Prop) : p → P.DiaNe p := fun hp hn =>
  (boxNe_elim (¬ p) hn) hp

theorem boxNe_of_box (p : Prop) : □ p → P.BoxNe p := fun hp =>
  ⟨True, trivial, box_imp_of_box (◇ True) p hp⟩

theorem boxNe_mono (p q : Prop) : □ (p → q) → P.BoxNe p → P.BoxNe q :=
  fun hpq ⟨r, hr, hrp⟩ => ⟨r, hr, box_compose (◇ r) p q hrp hpq⟩

theorem diaNe_mono (p q : Prop) : □ (p → q) → P.DiaNe p → P.DiaNe q :=
  fun hpq hp hnq => hp (boxNe_mono (¬ q) (¬ p)
    (modal_K _ _ (nec% (contra_imp p q)) hpq) hnq)

theorem boxNe_and (p q : Prop) : P.BoxNe p → P.BoxNe q → P.BoxNe (p ∧ q) :=
  fun ⟨r, hr, hrp⟩ ⟨s, hs, hsq⟩ =>
    ⟨r ∧ s, ⟨hr, hs⟩,
      modal_K _ _
        (modal_K _ _
          (nec% (fun (f : ◇ r → p) (g : ◇ s → q) (h : ◇ (r ∧ s)) =>
            And.intro (f (dia_and_left r s h)) (g (dia_and_right r s h)))) hrp) hsq⟩

theorem diaNe_forall {σ : Type} [Ty σ] (X : σ → Prop) :
    P.DiaNe (∀ x, X x) → ∀ x, P.DiaNe (X x) := fun h x =>
  diaNe_mono _ _ (nec% (fun (ha : ∀ y, X y) => ha x)) h

theorem ne_boxNe {σ : Type} [Ty σ] (x y : σ) : x ≠ y → P.BoxNe (x ≠ y) :=
  fun h => ⟨x ≠ y, h, nec% (ne_of_dia_ne x y)⟩

theorem diaNe_eq {σ : Type} [Ty σ] (x y : σ) : P.DiaNe (x = y) → x = y :=
  fun h => (em (x = y)).elim (fun he => he) (fun hn => (h (ne_boxNe x y hn)).elim)

/-- The actual truth value of a finite Boolean identity matrix is H-stable
on either side. This predicate is object-language notation, not a new axiom. -/
def DecidesNe (p : Prop) : Prop := (p → P.BoxNe p) ∧ (¬ p → P.BoxNe (¬ p))

theorem decidesNe_eq {σ : Type} [Ty σ] (x y : σ) : DecidesNe (x = y) :=
  ⟨fun h => boxNe_of_box _ (necessity_of_identity x y h), ne_boxNe x y⟩

theorem decidesNe_neg (p : Prop) : DecidesNe p → DecidesNe (¬ p) := fun h =>
  ⟨h.2, fun hnn => by
    have hp : P.BoxNe p := h.1 ((not_not_eq p).mp hnn)
    show P.BoxNe (¬ ¬ p)
    rw [not_not_eq]
    exact hp⟩

theorem decidesNe_and (p q : Prop) : DecidesNe p → DecidesNe q → DecidesNe (p ∧ q) :=
  fun hp hq => ⟨fun h => boxNe_and p q (hp.1 h.1) (hq.1 h.2), fun hn =>
    (em p).elim
      (fun hpt => boxNe_mono (¬ q) (¬ (p ∧ q))
        (nec% (fun (hqn : ¬ q) (hpq : p ∧ q) => hqn hpq.2))
        (hq.2 (fun hqt => hn ⟨hpt, hqt⟩)))
      (fun hpn => boxNe_mono (¬ p) (¬ (p ∧ q))
        (nec% (fun (hpn' : ¬ p) (hpq : p ∧ q) => hpn' hpq.1)) (hp.2 hpn))⟩

theorem decidesNe_or (p q : Prop) : DecidesNe p → DecidesNe q → DecidesNe (p ∨ q) :=
  fun hp hq => ⟨fun h => h.elim
    (fun hpt => boxNe_mono p (p ∨ q) (nec% (fun (hx : p) => Or.inl hx)) (hp.1 hpt))
    (fun hqt => boxNe_mono q (p ∨ q) (nec% (fun (hx : q) => Or.inr hx)) (hq.1 hqt)),
    fun hn => boxNe_mono (¬ p ∧ ¬ q) (¬ (p ∨ q))
      (nec% (fun (h : ¬ p ∧ ¬ q) (h' : p ∨ q) => h'.elim h.1 h.2))
      (boxNe_and (¬ p) (¬ q)
        (hp.2 (fun hpt => hn (Or.inl hpt)))
        (hq.2 (fun hqt => hn (Or.inr hqt))))⟩

theorem decidesNe_imp (p q : Prop) : DecidesNe p → DecidesNe q → DecidesNe (p → q) :=
  fun hp hq => by
    rw [imp_eq_not_or]
    exact decidesNe_or (¬ p) q (decidesNe_neg p hp) hq

theorem diaNe_reflect (p : Prop) : DecidesNe p → P.DiaNe p → p :=
  fun h hd => (em p).elim (fun hp => hp) (fun hn => (hd (h.2 hn)).elim)

theorem boxNe_exists {σ : Type} [Ty σ] (X : σ → Prop) :
    (∀ x, X x → P.BoxNe (X x)) → (∃ x, X x) → P.BoxNe (∃ x, X x) :=
  fun h ⟨x, hx⟩ => boxNe_mono (X x) (∃ y, X y)
    (nec% (fun (h' : X x) => Exists.intro x h')) (h x hx)

theorem diaNe_forall_reflect {σ : Type} [Ty σ] (X : σ → Prop) :
    (∀ x, P.DiaNe (X x) → X x) → P.DiaNe (∀ x, X x) → ∀ x, X x :=
  fun h hd x => h x (diaNe_forall X hd x)

theorem diaNe_forall_decides {σ : Type} [Ty σ] (X : σ → Prop) :
    (∀ x, DecidesNe (X x)) → P.DiaNe (∀ x, X x) → ∀ x, X x :=
  fun h => diaNe_forall_reflect X (fun x => diaNe_reflect (X x) (h x))

/-- C proves the distinctness-preserving reflection of monism, at any admitted
type. Existence is separate; at `e` it is already part of C. -/
theorem diaNe_monism {σ : Type} [Ty σ] :
    P.DiaNe (∀ x y : σ, x = y) → ∀ x y : σ, x = y := fun h x y =>
  diaNe_eq x y (diaNe_forall (fun z : σ => x = z)
    (diaNe_forall (fun z : σ => ∀ w : σ, z = w) h x) y)

theorem diaNe_one_name {σ : Type} [Ty σ] (a : σ) :
    P.DiaNe (∀ x : σ, x = a) → ∀ x : σ, x = a :=
  diaNe_forall_reflect (fun x : σ => x = a) (fun x => diaNe_eq x a)

/-- A finite named-exhaustion instance. This does not introduce a countable
disjunction, and does not assert that its sentence is Max-consistent. -/
theorem diaNe_two_names {σ : Type} [Ty σ] (a b : σ) :
    P.DiaNe (∀ x : σ, x = a ∨ x = b) → ∀ x : σ, x = a ∨ x = b :=
  diaNe_forall_decides (fun x : σ => x = a ∨ x = b)
    (fun x => decidesNe_or _ _ (decidesNe_eq x a) (decidesNe_eq x b))

/-- The codomain is relational: this declaration does not form a forbidden
individual-valued function type. -/
theorem diaNe_forall_identity {σ τ : Type} [Ty σ] [Rel τ] (F G : σ → τ) :
    P.DiaNe (∀ x : σ, F x = G x) → ∀ x : σ, F x = G x :=
  diaNe_forall_reflect (fun x : σ => F x = G x) (fun x => diaNe_eq (F x) (G x))

theorem diamond_idempotent_eq (p : Prop) : (◇ p) = ◇ ◇ p :=
  propext ⟨dia_intro (◇ p), dia_dia p⟩

theorem boxNe_fixed_iff (p : Prop) :
    P.BoxNe p ↔ ∃ r : Prop, r ≠ False ∧ r = ◇ r ∧ □ (r → p) :=
  ⟨fun ⟨q, hq, hb⟩ =>
    ⟨◇ q, dia_intro (◇ q) (dia_intro q hq), diamond_idempotent_eq q, hb⟩,
    fun ⟨r, hr, hfix, hb⟩ =>
      ⟨r, hfix.mpr hr, by
        show □ (◇ r → p)
        rw [← hfix]
        exact hb⟩⟩

theorem imp_not_eq_not_and (p q : Prop) : (p → ¬ q) = ¬ (p ∧ q) :=
  propext ⟨fun h hpq => h hpq.1 hpq.2, fun h hp hq => h ⟨hp, hq⟩⟩

theorem box_imp_not_eq_and_bot (p q : Prop) : (□ (p → ¬ q)) = ((p ∧ q) = False) := by
  rw [imp_not_eq_not_and]
  exact box_not_eq (p ∧ q)

/-- The exact universal-identity form of distinctness-preserving possibility.
This is the bridge used by the later algebraic quotient arguments. -/
theorem diaNe_fixed_iff (p : Prop) :
    P.DiaNe p ↔ ∀ r : Prop, r = ◇ r → r ≠ False → (r ∧ p) ≠ False :=
  ⟨fun hd r hfix hr hzero => hd ((boxNe_fixed_iff (¬ p)).mpr
    ⟨r, hr, hfix, (box_imp_not_eq_and_bot r p).mpr hzero⟩),
    fun h hn => by
      obtain ⟨r, hr, hfix, hb⟩ := (boxNe_fixed_iff (¬ p)).mp hn
      exact h r hfix hr ((box_imp_not_eq_and_bot r p).mp hb)⟩

theorem diaNe_monism_not_two {σ : Type} [Ty σ] :
    P.DiaNe (∀ x y : σ, x = y) → ¬ ∃ x y : σ, x ≠ y :=
  fun h ⟨x, y, hn⟩ => hn (diaNe_monism h x y)

#classicism_check box_compose dia_and_left dia_and_right boxNe_elim diaNe_intro
  boxNe_of_box boxNe_mono diaNe_mono boxNe_and diaNe_forall ne_boxNe diaNe_eq
  decidesNe_eq decidesNe_neg decidesNe_and decidesNe_or decidesNe_imp diaNe_reflect
  boxNe_exists diaNe_forall_reflect diaNe_forall_decides diaNe_monism diaNe_one_name
  diaNe_two_names diaNe_forall_identity diamond_idempotent_eq boxNe_fixed_iff
  imp_not_eq_not_and box_imp_not_eq_and_bot diaNe_fixed_iff diaNe_monism_not_two

#classicism_types box_compose dia_and_left dia_and_right boxNe_elim diaNe_intro
  boxNe_of_box boxNe_mono diaNe_mono boxNe_and diaNe_forall ne_boxNe diaNe_eq
  decidesNe_eq decidesNe_neg decidesNe_and decidesNe_or decidesNe_imp diaNe_reflect
  boxNe_exists diaNe_forall_reflect diaNe_forall_decides diaNe_monism diaNe_one_name
  diaNe_two_names diaNe_forall_identity diamond_idempotent_eq boxNe_fixed_iff
  imp_not_eq_not_and box_imp_not_eq_and_bot diaNe_fixed_iff diaNe_monism_not_two

#classicism_derive box_compose dia_and_left dia_and_right boxNe_elim diaNe_intro
  boxNe_of_box boxNe_mono diaNe_mono boxNe_and diaNe_forall ne_boxNe diaNe_eq
  decidesNe_eq decidesNe_neg decidesNe_and decidesNe_or decidesNe_imp diaNe_reflect
  boxNe_exists diaNe_forall_reflect diaNe_forall_decides diaNe_monism diaNe_one_name
  diaNe_two_names diaNe_forall_identity diamond_idempotent_eq boxNe_fixed_iff
  imp_not_eq_not_and box_imp_not_eq_and_bot diaNe_fixed_iff diaNe_monism_not_two

end Classicism.Research.StrongPossibilityConsequences
