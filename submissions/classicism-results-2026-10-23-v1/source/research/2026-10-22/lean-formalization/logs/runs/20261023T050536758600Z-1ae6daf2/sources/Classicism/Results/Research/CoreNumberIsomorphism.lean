import Classicism.Results.Research.FregeInfinity

/-!
# The arithmetic kernel of the Actuality/Gallin number comparison

Direct source: research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md
§§1–3; research/2026-10-22/notes/actuality-world-slice-core.md §5 (unpaginated, `misc`).

The world/core construction is owned separately. Here its precise arithmetic
interface is explicit: a represented property field P, existence of a current
P-coextension for each property, a represented cardinality map q preserving
application on P, and (where needed) its forward/range statements for a target
number predicate K. These are hypotheses, not added axioms or completed proofs
that Actuality/Gallin supplies the interface.

The injectivity theorem proves the substantive new step using quantified Infinity
and literal Frege-cardinality exclusivity. The inverse is only a relational graph.
Subset/image equalities below are current biconditionals, not identities of
intensional predicates. Admission of their target-core representatives remains
the separate core-comprehension obligation.
-/

namespace Classicism.Research

variable {σ : Type} [Ty σ]

/-- A normalized property field need only supply existential coextensions. -/
def PropertyFieldCovers (P : (σ → Prop) → Prop) : Prop :=
  ∀ X : σ → Prop, ∃ Y : σ → Prop, P Y ∧ ∀ u, X u ↔ Y u

/-- Only application to members of the represented property field is compared. -/
def NumberMapTests (P : (σ → Prop) → Prop)
    (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop)) : Prop :=
  ∀ n, FiniteCardinality n → ∀ Y, P Y → (q n Y ↔ n Y)

/-- Quantified Infinity turns the represented number map into an injection. -/
theorem core_number_injective (hInf : Classicism.P.AxiomOfInfinity σ)
    (P : (σ → Prop) → Prop) (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (hcovers : PropertyFieldCovers P) (htests : NumberMapTests P q)
    (n m : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hm : FiniteCardinality m) (he : q n = q m) : n = m := by
  obtain ⟨X, hnX⟩ := frege_infinity_realizes hInf n hn
  obtain ⟨Y, hPY, hXY⟩ := hcovers X
  have hnY : n Y := finiteCardinality_coext n hn X Y hnX hXY
  have hqnY : q n Y := (htests n hn Y hPY).2 hnY
  have hqmY : q m Y := Eq.mp (congrFun he Y) hqnY
  exact frege_common_instance_eq n m hn hm Y hnY ((htests m hm Y hPY).1 hqmY)

theorem core_number_identity_iff (hInf : Classicism.P.AxiomOfInfinity σ)
    (P : (σ → Prop) → Prop) (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (hcovers : PropertyFieldCovers P) (htests : NumberMapTests P q)
    (n m : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hm : FiniteCardinality m) : q n = q m ↔ n = m :=
  ⟨core_number_injective hInf P q hcovers htests n m hn hm,
   fun he => congrArg q he⟩

/-- The represented target universal property transfers quantified Infinity exactly.
The target number predicate K and its range proof are supplied by the core owner. -/
theorem core_quantified_infinity_iff
    (P : (σ → Prop) → Prop) (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (K : ((σ → Prop) → Prop) → Prop) (U : σ → Prop)
    (htests : NumberMapTests P q) (hPU : P U) (hU : ∀ u, U u)
    (hforward : ∀ n, FiniteCardinality n → K (q n))
    (honto : ∀ y, K y → ∃ n, FiniteCardinality n ∧ q n = y) :
    Classicism.P.AxiomOfInfinity σ ↔ ¬ ∃ y, K y ∧ y U := by
  constructor
  · intro hInf htarget
    obtain ⟨y, hKy, hyU⟩ := htarget
    obtain ⟨n, hn, he⟩ := honto y hKy
    have hqnU : q n U := Eq.mpr (congrFun he U) hyU
    have hnU : n U := (htests n hn U hPU).1 hqnU
    exact hInf ⟨n, hn, finiteCardinality_coext n hn U (fun _ => True) hnU
      (fun u => ⟨fun _ => True.intro, fun _ => hU u⟩)⟩
  · intro htarget hambient
    obtain ⟨n, hn, hntop⟩ := hambient
    have hnU : n U := finiteCardinality_coext n hn (fun _ => True) U hntop
      (fun u => ⟨fun _ => hU u, fun _ => True.intro⟩)
    exact htarget ⟨q n, hforward n hn, (htests n hn U hPU).2 hnU⟩

/-- An inverse graph on the two number fields; no selecting operation is introduced. -/
def NumberInverse (K : ((σ → Prop) → Prop) → Prop)
    (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (y n : (σ → Prop) → Prop) : Prop :=
  K y ∧ FiniteCardinality n ∧ q n = y

/-- The inverse graph is total and single-valued once the source is infinite. -/
theorem core_number_inverse_graph (hInf : Classicism.P.AxiomOfInfinity σ)
    (P : (σ → Prop) → Prop) (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (K : ((σ → Prop) → Prop) → Prop)
    (hcovers : PropertyFieldCovers P) (htests : NumberMapTests P q)
    (honto : ∀ y, K y → ∃ n, FiniteCardinality n ∧ q n = y) :
    ∀ y, K y → ∃ n, NumberInverse K q y n ∧
      ∀ m, NumberInverse K q y m → m = n := by
  intro y hy
  obtain ⟨n, hn, hqn⟩ := honto y hy
  refine ⟨n, ⟨hy, hn, hqn⟩, ?_⟩
  intro m hm
  exact core_number_injective hInf P q hcovers htests m n hm.2.1 hn
    (hm.2.2.trans hqn.symm)

/-- Pushforward of an admitted numerical predicate as an ambient graph formula. -/
def NumberPush (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (V : ((σ → Prop) → Prop) → Prop) (y : (σ → Prop) → Prop) : Prop :=
  ∃ n, FiniteCardinality n ∧ q n = y ∧ V n

/-- Pulling back this pushforward recovers the source predicate on numbers. -/
theorem core_number_push_pull (hInf : Classicism.P.AxiomOfInfinity σ)
    (P : (σ → Prop) → Prop) (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (hcovers : PropertyFieldCovers P) (htests : NumberMapTests P q)
    (V : ((σ → Prop) → Prop) → Prop) (n : (σ → Prop) → Prop)
    (hn : FiniteCardinality n) : NumberPush q V (q n) ↔ V n := by
  constructor
  · intro h
    obtain ⟨m, hm, he, hVm⟩ := h
    exact (core_number_injective hInf P q hcovers htests m n hm hn he) ▸ hVm
  · intro hVn
    exact ⟨n, hn, rfl, hVn⟩

/-- Surjectivity recovers target predicates, at the level of current extensions. -/
theorem core_number_pull_push
    (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (K V : ((σ → Prop) → Prop) → Prop)
    (honto : ∀ y, K y → ∃ n, FiniteCardinality n ∧ q n = y)
    (y : (σ → Prop) → Prop) (hy : K y) :
    NumberPush q (fun n => V (q n)) y ↔ V y := by
  constructor
  · intro h
    obtain ⟨n, _, he, hV⟩ := h
    exact he ▸ hV
  · intro hV
    obtain ⟨n, hn, he⟩ := honto y hy
    exact ⟨n, hn, he, Eq.mp (congrArg V he.symm) hV⟩

/-- Successor is reflected by any injective-on-numbers commuting core map.
This is conditional on the core's checked successor equation, not its construction. -/
theorem core_number_successor_iff (hInf : Classicism.P.AxiomOfInfinity σ)
    (P : (σ → Prop) → Prop) (q : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (s : ((σ → Prop) → Prop) → ((σ → Prop) → Prop))
    (hcovers : PropertyFieldCovers P) (htests : NumberMapTests P q)
    (hcomm : ∀ n, FiniteCardinality n → q (SucCard n) = s (q n))
    (n m : (σ → Prop) → Prop) (hn : FiniteCardinality n)
    (hm : FiniteCardinality m) : q n = s (q m) ↔ n = SucCard m := by
  constructor
  · intro he
    exact core_number_injective hInf P q hcovers htests n (SucCard m) hn
      (finiteCardinality_suc m hm) (he.trans (hcomm m hm).symm)
  · intro he
    exact (congrArg q he).trans (hcomm m hm)

end Classicism.Research
