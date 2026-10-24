import StrongPossibilityConsequencesC

/-!
# Further C certificates: D reflection, atomhood, and splitting

Original finitary research deductions; direct source: misc.
No consistency/model assumption is introduced. In particular the atom/split
contradiction below is only its displayed C implication, not an unconditional
certificate for pure SP versus signature Maximalism.
Pending the sole build owner's gate/type/translation checks.
-/

namespace Classicism.Research.StrongPossibilityConsequences

theorem decidesNe_iff (p q : Prop) : DecidesNe p → DecidesNe q → DecidesNe (p ↔ q) :=
  fun hp hq => by
    rw [iff_eq_and_imp]
    exact decidesNe_and _ _ (decidesNe_imp p q hp hq) (decidesNe_imp q p hq hp)

theorem decidesNe_fixed_matrix (p r : Prop) :
    DecidesNe (r = ◇ r → r ≠ False → (r ∧ p) ≠ False) :=
  decidesNe_imp _ _ (decidesNe_eq r (◇ r))
    (decidesNe_imp _ _ (decidesNe_neg _ (decidesNe_eq r False))
      (decidesNe_neg _ (decidesNe_eq (r ∧ p) False)))

/-- D is itself D-reflecting. The proof uses its universal Boolean-identity
presentation and never necessitates the hypothesis `h`. -/
theorem diaNe_idempotent (p : Prop) : P.DiaNe (P.DiaNe p) → P.DiaNe p := fun h =>
  (diaNe_fixed_iff p).mpr
    (diaNe_forall_decides
      (fun r : Prop => r = ◇ r → r ≠ False → (r ∧ p) ≠ False)
      (fun r => decidesNe_fixed_matrix p r)
      (diaNe_mono _ _ (nec% ((diaNe_fixed_iff p).mp)) h))

theorem decidesNe_le {τ : Type} [Rel τ] (x y : τ) : DecidesNe (Rel.le x y) :=
  decidesNe_eq y (Rel.or x y)

theorem decidesNe_atom_matrix {τ : Type} [Rel τ] (w z : τ) :
    DecidesNe ((Rel.le z w ∧ z ≠ w) ↔ Rel.le z (Rel.neg z)) :=
  decidesNe_iff _ _
    (decidesNe_and _ _ (decidesNe_le z w) (decidesNe_neg _ (decidesNe_eq z w)))
    (decidesNe_le z (Rel.neg z))

/-- Atomhood is a universal Boolean-identity formula at each admitted
relational type, so D-reflection applies without Atomicity or completeness. -/
theorem diaNe_atom {τ : Type} [Rel τ] (w : τ) : P.DiaNe (Atom w) → Atom w :=
  diaNe_forall_decides
    (fun z : τ => (Rel.le z w ∧ z ≠ w) ↔ Rel.le z (Rel.neg z))
    (fun z => decidesNe_atom_matrix w z)

theorem atom_no_split (w p : Prop) :
    Atom w → ◇ (w ∧ p) → ◇ (w ∧ ¬ p) → False := fun hw hp hnp =>
  (atom_le_or_le_neg w p hw).elim
    (fun hle => not_dia_of_box_not (w ∧ ¬ p)
      (modal_K _ _
        (nec% (fun (f : w → p) (h : w ∧ ¬ p) => h.2 (f h.1)))
        ((le_iff_prop w p).mp hle)) hnp)
    (fun hle => not_dia_of_box_not (w ∧ p)
      (modal_K _ _
        (nec% (fun (f : w → ¬ p) (h : w ∧ p) => f h.1 h.2))
        ((le_iff_prop w (¬ p)).mp hle)) hp)

/-- The object-level core needed by the signature incompatibility argument.
The consistency side condition supplying `D Atom(w)` is kept outside this
theorem, as are the signature instances supplying both ordinary possibilities. -/
theorem diaNe_atom_no_split (w p : Prop) :
    P.DiaNe (Atom w) → ◇ (w ∧ p) → ◇ (w ∧ ¬ p) → False :=
  fun hw => atom_no_split w p (diaNe_atom w hw)

#classicism_check decidesNe_iff decidesNe_fixed_matrix diaNe_idempotent
  decidesNe_le decidesNe_atom_matrix diaNe_atom atom_no_split diaNe_atom_no_split

#classicism_types decidesNe_iff decidesNe_fixed_matrix diaNe_idempotent
  decidesNe_le decidesNe_atom_matrix diaNe_atom atom_no_split diaNe_atom_no_split

#classicism_derive decidesNe_iff decidesNe_fixed_matrix diaNe_idempotent
  decidesNe_le decidesNe_atom_matrix diaNe_atom atom_no_split diaNe_atom_no_split

end Classicism.Research.StrongPossibilityConsequences
