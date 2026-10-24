import Classicism.Results.Research.FregeInfinity

/-!
# Choice-free internal finite-set calculus

Direct sources, all unpaginated original research (`misc`):
`research/2026-10-22/notes/world-cardinality-ucp-20261022.md`, §20.A;
`research/2026-10-22/notes/relational-coding-recursion-20261022.md`, §27.1;
`research/2026-10-22/notes/frege-infinity-20261022-1726.md`, §7.

Finiteness is an actual instance of an internal Frege cardinality, never an
external finite list or the finite-distinctness schema. Images are relations,
so both source and output sorts may be the individual sort. All inductions are
the exact impredicative number induction of C. No Choice, BF or ND is assumed.
-/

namespace Classicism.Research.FregeFiniteSets

variable {σ τ : Type} [Ty σ] [Ty τ]

def Finite (A : σ → Prop) : Prop := ∃ n, FiniteCardinality n ∧ n A

def Image (A : σ → Prop) (R : σ → τ → Prop) (y : τ) : Prop :=
  ∃ x, A x ∧ R x y

theorem finite_coext (A B : σ → Prop) (hA : Finite A)
    (h : ∀ x, A x ↔ B x) : Finite B := by
  obtain ⟨n, hn, hna⟩ := hA
  exact ⟨n, hn, finiteCardinality_coext n hn A B hna h⟩

theorem finite_empty : Finite (fun _ : σ => False) :=
  ⟨ZeroCard σ, finiteCardinality_zero, fun _ h => h⟩

theorem finite_of_empty (A : σ → Prop) (h : ∀ x, ¬ A x) : Finite A :=
  finite_coext _ A finite_empty (fun x => ⟨False.elim, h x⟩)

theorem finite_singleton (a : σ) : Finite (fun x => x = a) :=
  ⟨SucCard (ZeroCard σ), finiteCardinality_suc _ finiteCardinality_zero,
    a, rfl, fun x hx => hx.2 hx.1⟩

theorem finite_adjoin (A : σ → Prop) (hA : Finite A) (a : σ) :
    Finite (fun x => A x ∨ x = a) := by
  obtain ⟨n, hn, hna⟩ := hA
  apply (em (A a)).elim
  · intro ha
    exact ⟨n, hn, finiteCardinality_coext n hn A _ hna
      (fun x => ⟨Or.inl, fun h => h.elim id (fun he => he.symm ▸ ha)⟩)⟩
  · intro ha
    exact ⟨SucCard n, finiteCardinality_suc n hn, frege_fresh_point n hn A a hna ha⟩

theorem finite_at_most_one (A : σ → Prop)
    (h : ∀ x y, A x → A y → x = y) : Finite A := by
  apply (em (∃ a, A a)).elim
  · intro hex
    obtain ⟨a, ha⟩ := hex
    exact finite_coext _ A (finite_singleton a)
      (fun x => ⟨fun he => he.symm ▸ ha, fun hx => h x a hx ha⟩)
  · intro hn
    exact finite_of_empty A (fun x hx => hn ⟨x, hx⟩)

theorem finite_subset (A B : σ → Prop) (hA : Finite A)
    (hBA : ∀ x, B x → A x) : Finite B := by
  obtain ⟨n, hn, hna⟩ := hA
  have hsub : ∀ X Y : σ → Prop, n X → (∀ x, Y x → X x) → Finite Y := by
    apply hn (fun m => ∀ X Y : σ → Prop, m X → (∀ x, Y x → X x) → Finite Y)
    constructor
    · intro X Y hx hYX
      exact finite_of_empty Y (fun x hy => hx x (hYX x hy))
    · intro m hm X Y hx hYX
      obtain ⟨a, ha, hdel⟩ := hx
      have hYdel : Finite (fun x => Y x ∧ x ≠ a) :=
        hm (fun x => X x ∧ x ≠ a) (fun x => Y x ∧ x ≠ a) hdel
          (fun x hy => ⟨hYX x hy.1, hy.2⟩)
      apply (em (Y a)).elim
      · intro hya
        exact finite_coext _ Y (finite_adjoin _ hYdel a) (fun x =>
          ⟨fun h => h.elim And.left (fun he => he.symm ▸ hya),
            fun hy => (em (x = a)).elim Or.inr (fun he => Or.inl ⟨hy, he⟩)⟩)
      · intro hya
        exact finite_coext _ Y hYdel (fun x =>
          ⟨And.left, fun hy => ⟨hy, fun he => hya (he ▸ hy)⟩⟩)
  exact hsub A B hna hBA

theorem finite_union (A B : σ → Prop) (hA : Finite A) (hB : Finite B) :
    Finite (fun x => A x ∨ B x) := by
  obtain ⟨n, hn, hna⟩ := hA
  have hu : ∀ X : σ → Prop, n X → Finite (fun x => X x ∨ B x) := by
    apply hn (fun m => ∀ X : σ → Prop, m X → Finite (fun x => X x ∨ B x))
    constructor
    · intro X hx
      exact finite_coext B _ hB
        (fun x => ⟨Or.inr, fun h => h.elim (fun hX => (hx x hX).elim) id⟩)
    · intro m hm X hx
      obtain ⟨a, ha, hdel⟩ := hx
      have hpre := finite_adjoin _ (hm _ hdel) a
      apply finite_coext _ _ hpre
      intro x
      constructor
      · intro h
        exact h.elim (fun h => h.elim (fun hX => Or.inl hX.1) Or.inr)
          (fun he => Or.inl (he.symm ▸ ha))
      · intro h
        exact h.elim
          (fun hX => (em (x = a)).elim Or.inr (fun he => Or.inl (Or.inl ⟨hX, he⟩)))
          (fun hB => Or.inl (Or.inr hB))
  exact hu A hna

/-- A finite represented union of finite fibres needs no choices of enumerations. -/
theorem finite_fibre_union (A : σ → Prop) (R : σ → τ → Prop)
    (hA : Finite A) (hR : ∀ x, A x → Finite (R x)) : Finite (Image A R) := by
  obtain ⟨n, hn, hna⟩ := hA
  have hi : ∀ X : σ → Prop, n X →
      (∀ x, X x → Finite (R x)) → Finite (Image X R) := by
    apply hn (fun m => ∀ X : σ → Prop, m X →
      (∀ x, X x → Finite (R x)) → Finite (Image X R))
    constructor
    · intro X hx _
      exact finite_of_empty _ (fun y hy => hy.elim fun x hxy => hx x hxy.1)
    · intro m hm X hx hRX
      obtain ⟨a, ha, hdel⟩ := hx
      have hsmall := hm (fun x => X x ∧ x ≠ a) hdel (fun x h => hRX x h.1)
      apply finite_coext _ (Image X R) (finite_union _ _ hsmall (hRX a ha))
      intro y
      constructor
      · intro h
        exact h.elim (fun hi => hi.elim fun x hxy => ⟨x, hxy.1.1, hxy.2⟩)
          (fun hay => ⟨a, ha, hay⟩)
      · intro hi
        obtain ⟨x, hx, hxy⟩ := hi
        exact (em (x = a)).elim (fun he => Or.inr (he ▸ hxy))
          (fun he => Or.inl ⟨x, ⟨hx, he⟩, hxy⟩)
  exact hi A hna hR

/-- Even partial single-valued relational images of finite domains are finite. -/
theorem finite_functional_image (A : σ → Prop) (R : σ → τ → Prop)
    (hA : Finite A) (hR : ∀ x, A x → ∀ y z, R x y → R x z → y = z) :
    Finite (Image A R) :=
  finite_fibre_union A R hA (fun x hx => finite_at_most_one (R x) (hR x hx))

theorem finite_injection_domain (A : σ → Prop) (B : τ → Prop)
    (R : σ → τ → Prop) (hB : Finite B)
    (htotal : ∀ x, A x → ∃ y, B y ∧ R x y)
    (hinj : ∀ x z y, A x → A z → R x y → R z y → x = z) : Finite A := by
  have hf : Finite (Image B (fun y x => A x ∧ R x y)) :=
    finite_fibre_union B _ hB (fun y _ => finite_at_most_one _
      (fun x z hx hz => hinj x z y hx.1 hz.1 hx.2 hz.2))
  exact finite_coext _ A hf (fun x =>
    ⟨fun h => h.elim fun _ hy => hy.2.1,
      fun hx => (htotal x hx).elim fun y hy => ⟨y, hy.1, hx, hy.2⟩⟩)

/-- A finite set of truth coordinates can separate only a Frege-finite family. -/
theorem finite_separated_family (A : σ → Prop) (H : τ → Prop)
    (E : σ → τ → Prop) (hA : Finite A)
    (hsep : ∀ u v, H u → H v → (∀ x, A x → (E x u ↔ E x v)) → u = v) :
    Finite H := by
  obtain ⟨n, hn, hna⟩ := hA
  have hs : ∀ X : σ → Prop, n X → ∀ K : τ → Prop,
      (∀ u v, K u → K v → (∀ x, X x → (E x u ↔ E x v)) → u = v) → Finite K := by
    apply hn (fun m => ∀ X : σ → Prop, m X → ∀ K : τ → Prop,
      (∀ u v, K u → K v → (∀ x, X x → (E x u ↔ E x v)) → u = v) → Finite K)
    constructor
    · intro X hx K hK
      exact finite_at_most_one K (fun u v hu hv => hK u v hu hv
        (fun x hX => (hx x hX).elim))
    · intro m hm X hx K hK
      obtain ⟨a, ha, hdel⟩ := hx
      have hyes : Finite (fun u => K u ∧ E a u) := by
        apply hm (fun x => X x ∧ x ≠ a) hdel (fun u => K u ∧ E a u)
        intro u v hu hv hagree
        apply hK u v hu.1 hv.1
        intro x hx
        apply (em (x = a)).elim
        · intro he
          rw [he]
          exact ⟨fun _ => hv.2, fun _ => hu.2⟩
        · intro he
          exact hagree x ⟨hx, he⟩
      have hno : Finite (fun u => K u ∧ ¬ E a u) := by
        apply hm (fun x => X x ∧ x ≠ a) hdel (fun u => K u ∧ ¬ E a u)
        intro u v hu hv hagree
        apply hK u v hu.1 hv.1
        intro x hx
        apply (em (x = a)).elim
        · intro he
          rw [he]
          exact ⟨fun h => (hu.2 h).elim, fun h => (hv.2 h).elim⟩
        · intro he
          exact hagree x ⟨hx, he⟩
      exact finite_coext _ K (finite_union _ _ hyes hno) (fun u =>
        ⟨fun h => h.elim And.left And.left,
          fun hu => (em (E a u)).elim (fun he => Or.inl ⟨hu, he⟩)
            (fun he => Or.inr ⟨hu, he⟩)⟩)
  exact hs A hna H hsep

theorem equal_count_inclusion (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    ∀ X Y : σ → Prop, n X → n Y → (∀ x, X x → Y x) → ∀ x, X x ↔ Y x := by
  refine (hn (fun m => FiniteCardinality m ∧ ∀ X Y : σ → Prop,
    m X → m Y → (∀ x, X x → Y x) → ∀ x, X x ↔ Y x) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, fun X Y hx hy _ x =>
      ⟨fun h => (hx x h).elim, fun h => (hy x h).elim⟩⟩
  · intro m hm
    refine ⟨finiteCardinality_suc m hm.1, ?_⟩
    intro X Y hx hy hXY
    obtain ⟨a, ha, hma⟩ := hx
    obtain ⟨b, hb, hmb⟩ := hy
    have hYa : Y a := hXY a ha
    have hmYa : m (fun x => Y x ∧ x ≠ a) :=
      (em (a = b)).elim (fun he => he.symm ▸ hmb)
        (fun he => frege_swap m hm.1 Y a b hmb hYa hb he)
    have hdel := hm.2 _ _ hma hmYa (fun x h => ⟨hXY x h.1, h.2⟩)
    intro x
    exact ⟨hXY x, fun hy => (em (x = a)).elim (fun he => he.symm ▸ ha)
      (fun he => ((hdel x).2 ⟨hy, he⟩).1)⟩

theorem finite_upper_bound (n : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (X Y : σ → Prop) (hy : n Y) (hXY : ∀ x, X x → Y x) : ¬ SucCard n X := by
  intro hs
  obtain ⟨a, ha, hdel⟩ := hs
  have he := equal_count_inclusion n hn _ Y hdel hy (fun x h => hXY x h.1)
  exact ((he a).2 (hXY a ha)).2 rfl

theorem infinity_iff_realizes : Classicism.P.AxiomOfInfinity σ ↔
    ∀ n : (σ → Prop) → Prop, FiniteCardinality n → ∃ X, n X := by
  constructor
  · exact fun hi n hn => frege_infinity_realizes hi n hn
  · intro hr hf
    obtain ⟨n, hn, htop⟩ := hf
    obtain ⟨X, hX⟩ := hr (SucCard n) (finiteCardinality_suc n hn)
    exact finite_upper_bound n hn X _ htop (fun _ _ => True.intro) hX

theorem infinity_iff_outsiders : Classicism.P.AxiomOfInfinity σ ↔
    ∀ X : σ → Prop, Finite X → ∃ a, ¬ X a := by
  constructor
  · intro hi X hX
    obtain ⟨n, hn, hnX⟩ := hX
    exact frege_infinity_outside hi n hn X hnX
  · intro hout hfinite
    obtain ⟨a, ha⟩ := hout (fun _ => True) hfinite
    exact ha True.intro

/-- A bijection onto its represented image preserves the same-sort count. -/
theorem injective_image_count (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    ∀ (A : σ → Prop) (R : σ → σ → Prop), n A →
      (∀ x, A x → ∃ y, R x y) →
      (∀ x y z, A x → R x y → R x z → y = z) →
      (∀ x z y, A x → A z → R x y → R z y → x = z) → n (Image A R) := by
  refine (hn (fun m => FiniteCardinality m ∧
    ∀ (A : σ → Prop) (R : σ → σ → Prop), m A →
      (∀ x, A x → ∃ y, R x y) →
      (∀ x y z, A x → R x y → R x z → y = z) →
      (∀ x z y, A x → A z → R x y → R z y → x = z) → m (Image A R))
    ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, fun A R hA _ _ _ y hy =>
      hy.elim fun x hx => hA x hx.1⟩
  · intro m hm
    refine ⟨finiteCardinality_suc m hm.1, ?_⟩
    intro A R hA htotal hsingle hinj
    obtain ⟨a, ha, hdel⟩ := hA
    obtain ⟨y, hay⟩ := htotal a ha
    have hsmall := hm.2 (fun x => A x ∧ x ≠ a) R hdel
      (fun x hx => htotal x hx.1)
      (fun x u v hx => hsingle x u v hx.1)
      (fun x z u hx hz => hinj x z u hx.1 hz.1)
    refine ⟨y, ⟨a, ha, hay⟩, ?_⟩
    apply finiteCardinality_coext m hm.1 _ _ hsmall
    intro u
    constructor
    · intro h
      obtain ⟨x, hx, hxu⟩ := h
      exact ⟨⟨x, hx.1, hxu⟩, fun he =>
        hx.2 (hinj x a y hx.1 ha (he ▸ hxu) hay)⟩
    · intro h
      obtain ⟨x, hx, hxu⟩ := h.1
      exact ⟨x, ⟨hx, fun he => h.2 (hsingle a u y ha (he ▸ hxu) hay)⟩, hxu⟩

/-- The finite pigeonhole principle stated for graphs, including individual sorts. -/
theorem finite_self_injection_surjective (A : σ → Prop) (R : σ → σ → Prop)
    (hA : Finite A) (htotal : ∀ x, A x → ∃ y, R x y)
    (hclosed : ∀ x y, A x → R x y → A y)
    (hsingle : ∀ x y z, A x → R x y → R x z → y = z)
    (hinj : ∀ x z y, A x → A z → R x y → R z y → x = z) :
    ∀ y, A y → ∃ x, A x ∧ R x y := by
  obtain ⟨n, hn, hnA⟩ := hA
  have hnI := injective_image_count n hn A R hnA htotal hsingle hinj
  have he := equal_count_inclusion n hn (Image A R) A hnI hnA
    (fun y hy => hy.elim fun x hx => hclosed x y hx.1 hx.2)
  exact fun y hy => (he y).2 hy

end Classicism.Research.FregeFiniteSets
