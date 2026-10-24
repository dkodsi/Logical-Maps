import Classicism.Cardinality
import Classicism.Principles.Infinity

/-!
# Internal Frege cardinalities: fresh points, realization, and exclusivity

Sources (unpaginated): research/2026-10-22/notes/frege-infinity-20261022-1726.md
§1, and topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md
§1, Lemmas 1–4. The fresh-point/Infinity deduction is original research (`misc`);
the exclusivity argument follows the recorded proof, retaining its boxed disjunct.

These are shallow object-language C proofs, with a separate certificate driver.
No Choice, BF, ND, external natural numbers, or individual-valued operation occurs.
In particular, realization is an existential theorem for every internal number,
not an operation simultaneously choosing its instances.
-/

namespace Classicism.Research

variable {σ : Type} [Ty σ]

/-- The existing extension-invariance lemma in its symmetric form. -/
theorem frege_coext_iff (n : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (X Y : σ → Prop) (hXY : ∀ u, X u ↔ Y u) : n X ↔ n Y :=
  ⟨fun hx => finiteCardinality_coext n hn X Y hx hXY,
   fun hy => finiteCardinality_coext n hn Y X hy (fun u => (hXY u).symm)⟩

/-- Adjoining one point outside a counted property realizes the successor. -/
theorem frege_fresh_point (n : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (X : σ → Prop) (a : σ) (hX : n X) (ha : ¬ X a) :
    SucCard n (fun u => X u ∨ u = a) := by
  refine ⟨a, Or.inr rfl, ?_⟩
  apply finiteCardinality_coext n hn X _ hX
  intro u
  exact ⟨fun hu => ⟨Or.inl hu, fun e => ha (e ▸ hu)⟩,
    fun hu => hu.1.elim id (fun e => False.elim (hu.2 e))⟩

theorem frege_outside_of_not_universal (X : σ → Prop) (h : ¬ ∀ u, X u) :
    ∃ a, ¬ X a :=
  (em (∃ a, ¬ X a)).elim id (fun hnone =>
    False.elim (h (fun u => (em (X u)).elim id
      (fun hu => False.elim (hnone ⟨u, hu⟩)))))

/-- Under quantified Infinity, no property counted by a finite cardinal is universal. -/
theorem frege_infinity_outside (hInf : P.AxiomOfInfinity σ)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (X : σ → Prop) (hX : n X) : ∃ a, ¬ X a := by
  apply frege_outside_of_not_universal X
  intro hall
  exact hInf ⟨n, hn, finiteCardinality_coext n hn X (fun _ => True) hX
    (fun u => ⟨fun _ => True.intro, fun _ => hall u⟩)⟩

/-- Quantified Infinity realizes every internal finite cardinality, without Choice. -/
theorem frege_infinity_realizes (hInf : P.AxiomOfInfinity σ)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) : ∃ X, n X := by
  refine (hn (fun m => FiniteCardinality m ∧ ∃ X, m X) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, (fun _ => False), fun _ h => h⟩
  · intro m hm
    refine ⟨finiteCardinality_suc m hm.1, ?_⟩
    exact hm.2.elim (fun X hX =>
      (frege_infinity_outside hInf m hm.1 X hX).elim (fun a ha =>
        ⟨(fun u => X u ∨ u = a), frege_fresh_point m hm.1 X a hX ha⟩))

/-- A realized cardinality is not the empty cardinality object. -/
theorem frege_realized_ne_bottom (n : (σ → Prop) → Prop) (h : ∃ X, n X) :
    n ≠ (fun _ => False) := fun he =>
  h.elim (fun X hX => Eq.mp (congrFun he X) hX)

theorem frege_infinity_ne_bottom (hInf : P.AxiomOfInfinity σ)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    n ≠ (fun _ => False) :=
  frege_realized_ne_bottom n (frege_infinity_realizes hInf n hn)

/-- Zero differs from every successor, independently of Infinity. -/
theorem frege_zero_ne_suc (n : (σ → Prop) → Prop) : ZeroCard σ ≠ SucCard n := by
  intro he
  have hzero : ZeroCard σ (fun _ => False) := fun _ h => h
  exact (Eq.mp (congrFun he (fun _ => False)) hzero).elim (fun _ h => h.1)

/-- Internal case analysis, without identifying numbers with external numerals. -/
theorem frege_cases (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    n = ZeroCard σ ∨ ∃ m, FiniteCardinality m ∧ n = SucCard m := by
  refine (hn (fun q => FiniteCardinality q ∧
    (q = ZeroCard σ ∨ ∃ m, FiniteCardinality m ∧ q = SucCard m)) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, Or.inl rfl⟩
  · intro q hq
    exact ⟨finiteCardinality_suc q hq.1, Or.inr ⟨q, hq.1, rfl⟩⟩

/-- Numberhood persists by its own impredicative induction. -/
theorem frege_number_persistent (n : (σ → Prop) → Prop) :
    FiniteCardinality n → □ (FiniteCardinality n) := fun hn =>
  hn (fun q => □ (FiniteCardinality q))
    ⟨nec% (finiteCardinality_zero (σ := σ)),
     fun q hq => modal_K _ _ (nec% (finiteCardinality_suc q)) hq⟩

/-- Removing either of two members leaves the same finite count.
The proof transfers applications by coextension; it does not identify arbitrary
coextensive property objects under hypotheses. -/
theorem frege_swap (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    ∀ (X : σ → Prop) (a b : σ), n (fun u => X u ∧ u ≠ b) →
      X a → X b → a ≠ b → n (fun u => X u ∧ u ≠ a) := by
  refine (hn (fun q => FiniteCardinality q ∧
    ∀ (X : σ → Prop) (a b : σ), q (fun u => X u ∧ u ≠ b) →
      X a → X b → a ≠ b → q (fun u => X u ∧ u ≠ a)) ⟨?_, ?_⟩).2
  · refine ⟨finiteCardinality_zero, ?_⟩
    intro X a b hzero ha _ hab
    exact False.elim (hzero a ⟨ha, hab⟩)
  · intro q hq
    refine ⟨finiteCardinality_suc q hq.1, ?_⟩
    intro X a b hs ha hb hab
    obtain ⟨z, hz, hdel⟩ := hs
    have hswap : q (fun u => (X u ∧ u ≠ b) ∧ u ≠ a) := by
      exact (em (z = a)).elim
        (fun he => he ▸ hdel)
        (fun hza => hq.2 (fun u => X u ∧ u ≠ b) a z hdel
          ⟨ha, hab⟩ hz (fun haz => hza haz.symm))
    refine ⟨b, ⟨hb, fun hba => hab hba.symm⟩, ?_⟩
    exact finiteCardinality_coext q hq.1 _ _ hswap (fun u =>
      ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩,
       fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩)

theorem frege_zero_suc_disjoint (m : (σ → Prop) → Prop) :
    ∀ X, ¬ (ZeroCard σ X ∧ SucCard m X) := fun X h =>
  h.2.elim (fun a ha => h.1 a ha.1)

theorem frege_suc_zero_disjoint (m : (σ → Prop) → Prop) :
    ∀ X, ¬ (SucCard m X ∧ ZeroCard σ X) := fun X h =>
  h.1.elim (fun a ha => h.2 a ha.1)

/-- The closed C implication used inside the box in exclusivity's successor case. -/
theorem frege_suc_disjoint (n m : (σ → Prop) → Prop) :
    FiniteCardinality m → (∀ X, ¬ (n X ∧ m X)) →
      ∀ X, ¬ (SucCard n X ∧ SucCard m X) := by
  intro hm hdis X hs
  obtain ⟨a, ha, hna⟩ := hs.1
  obtain ⟨b, hb, hmb⟩ := hs.2
  have hma : m (fun u => X u ∧ u ≠ a) :=
    (em (a = b)).elim (fun he => he.symm ▸ hmb)
      (fun hab => frege_swap m hm X a b hmb ha hb hab)
  exact hdis _ ⟨hna, hma⟩

/-- The exact boxed alternative of recorded Lemma 4. -/
theorem frege_cardinal_exclusivity (n : (σ → Prop) → Prop)
    (hn : FiniteCardinality n) :
    ∀ m, FiniteCardinality m →
      n = m ∨ □ (∀ X, ¬ (n X ∧ m X)) := by
  refine (hn (fun q => FiniteCardinality q ∧
    ∀ m, FiniteCardinality m → q = m ∨ □ (∀ X, ¬ (q X ∧ m X))) ⟨?_, ?_⟩).2
  · refine ⟨finiteCardinality_zero, ?_⟩
    intro m hm
    apply (frege_cases m hm).elim
    · intro he
      exact Or.inl he.symm
    · intro hs
      obtain ⟨r, _, he⟩ := hs
      rw [he]
      exact Or.inr (nec% (frege_zero_suc_disjoint r))
  · intro q hq
    refine ⟨finiteCardinality_suc q hq.1, ?_⟩
    intro m hm
    apply (frege_cases m hm).elim
    · intro he
      rw [he]
      exact Or.inr (nec% (frege_suc_zero_disjoint q))
    · intro hs
      obtain ⟨r, hr, he⟩ := hs
      rw [he]
      apply (hq.2 r hr).elim
      · intro hqr
        exact Or.inl (congrArg SucCard hqr)
      · intro hdis
        exact Or.inr (modal_K _ _
          (modal_K _ _ (nec% (frege_suc_disjoint q r))
            (frege_number_persistent r hr)) hdis)

/-- A common current instance identifies finite cardinality objects literally. -/
theorem frege_common_instance_eq (n m : (σ → Prop) → Prop)
    (hn : FiniteCardinality n) (hm : FiniteCardinality m)
    (X : σ → Prop) (hnX : n X) (hmX : m X) : n = m :=
  (frege_cardinal_exclusivity n hn m hm).elim id (fun h =>
    False.elim (modal_T _ h X ⟨hnX, hmX⟩))

/-- Under quantified Infinity, current coextension of number objects identifies them. -/
theorem frege_infinity_numerical_extensionality (hInf : P.AxiomOfInfinity σ)
    (n m : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hm : FiniteCardinality m) (hext : ∀ X, n X ↔ m X) : n = m :=
  (frege_infinity_realizes hInf n hn).elim (fun X hX =>
    frege_common_instance_eq n m hn hm X hX ((hext X).1 hX))

/-- Realization gives successor injectivity by deleting the same witnessed point. -/
theorem frege_infinity_suc_injective (hInf : P.AxiomOfInfinity σ)
    (n m : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hm : FiniteCardinality m) (he : SucCard n = SucCard m) : n = m := by
  obtain ⟨X, hs⟩ := frege_infinity_realizes hInf (SucCard n)
    (finiteCardinality_suc n hn)
  obtain ⟨a, ha, hna⟩ := hs
  have hsm : SucCard m X := Eq.mp (congrFun he X) ⟨a, ha, hna⟩
  obtain ⟨b, hb, hmb⟩ := hsm
  have hma : m (fun u => X u ∧ u ≠ a) :=
    (em (a = b)).elim (fun hab => hab.symm ▸ hmb)
      (fun hab => frege_swap m hm X a b hmb ha hb hab)
  exact frege_common_instance_eq n m hn hm _ hna hma

end Classicism.Research
