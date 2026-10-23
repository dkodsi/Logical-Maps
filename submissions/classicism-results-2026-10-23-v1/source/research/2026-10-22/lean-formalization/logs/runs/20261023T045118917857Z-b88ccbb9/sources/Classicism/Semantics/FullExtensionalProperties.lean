import Classicism.Semantics.Relational
import Classicism.Certified.Signatures

/-!
# Full extensional one-world schema validation

Ordinary metatheory for the existing `Interp` interpretation. Coordinates are
introduced only to prove the semantic lattice facts; each exported schema
theorem below refers to the existing generated `.quoted`/`.schemaIn` formulas.
External classical choice is used to validate the existential FC schema. No
logical choice operator is added and no shallow C derivation is claimed.

Source: central-questions-audit.md, "Other verified properties" (original local
research, unpaginated, misc). Exact syntax and C soundness are those already
defined by Semantics/Relational and Semantics/Denotation.
-/

namespace Classicism.Meta.FullExtensional
noncomputable section

def Coord (E : Type) : RTy → Type
  | .t => Unit
  | .arr σ ρ => σ.denote E × Coord E ρ

def read (E : Type) : ∀ ρ : RTy, ρ.denote E → Coord E ρ → Prop
  | .t, p, _ => p
  | .arr _ ρ, X, i => read E ρ (X i.1) i.2

def write (E : Type) : ∀ ρ : RTy, (Coord E ρ → Prop) → ρ.denote E
  | .t, P => P ()
  | .arr _ ρ, P => fun x => write E ρ (fun i => P (x, i))

theorem read_write (E : Type) : ∀ (ρ : RTy) (P : Coord E ρ → Prop) (i : Coord E ρ),
    read E ρ (write E ρ P) i = P i
  | .t, _, () => rfl
  | .arr _ ρ, P, (x, i) => read_write E ρ (fun j => P (x, j)) i

theorem write_read (E : Type) : ∀ (ρ : RTy) (X : ρ.denote E), write E ρ (read E ρ X) = X
  | .t, _ => rfl
  | .arr _ ρ, X => by funext x; exact write_read E ρ (X x)

theorem read_injective (E : Type) (ρ : RTy) {X Y : ρ.denote E}
    (h : ∀ i, read E ρ X i = read E ρ Y i) : X = Y := by
  have he := congrArg (write E ρ) (funext h)
  simpa only [write_read] using he

theorem read_or (E : Type) : ∀ (ρ : RTy) (X Y : ρ.denote E) (i : Coord E ρ),
    read E ρ (RTy.orD E ρ X Y) i = (read E ρ X i ∨ read E ρ Y i)
  | .t, _, _, _ => rfl
  | .arr _ ρ, X, Y, (x, i) => read_or E ρ (X x) (Y x) i

theorem read_neg (E : Type) : ∀ (ρ : RTy) (X : ρ.denote E) (i : Coord E ρ),
    read E ρ (RTy.negD E ρ X) i = (¬ read E ρ X i)
  | .t, _, _ => rfl
  | .arr _ ρ, X, (x, i) => read_neg E ρ (X x) i

def LeR (E : Type) (ρ : RTy) (X Y : ρ.denote E) : Prop := Y = RTy.orD E ρ X Y

def AtomR (E : Type) (ρ : RTy) (Y : ρ.denote E) : Prop :=
  ∀ Z, (LeR E ρ Z Y ∧ Z ≠ Y) ↔ LeR E ρ Z (RTy.negD E ρ Z)

theorem le_iff (E : Type) (ρ : RTy) (X Y : ρ.denote E) :
    LeR E ρ X Y ↔ ∀ i, read E ρ X i → read E ρ Y i := by
  constructor
  · intro h i hx
    have he := congrArg (fun Z => read E ρ Z i) h
    rw [read_or] at he
    exact Eq.mpr he (Or.inl hx)
  · intro h
    apply read_injective E ρ
    intro i
    rw [read_or]
    exact propext ⟨Or.inr, fun hp => hp.elim (h i) id⟩

theorem le_neg_iff (E : Type) (ρ : RTy) (X : ρ.denote E) :
    LeR E ρ X (RTy.negD E ρ X) ↔ ∀ i, ¬ read E ρ X i := by
  rw [le_iff]
  simp only [read_neg]
  exact ⟨fun h i hi => h i hi hi, fun h i _ => h i⟩

def singleton (E : Type) (ρ : RTy) (i : Coord E ρ) : ρ.denote E :=
  write E ρ (fun j => j = i)

@[simp] theorem read_singleton (E : Type) (ρ : RTy) (i j : Coord E ρ) :
    read E ρ (singleton E ρ i) j = (j = i) := read_write E ρ _ j

theorem singleton_atom (E : Type) (ρ : RTy) (i : Coord E ρ) : AtomR E ρ (singleton E ρ i) := by
  intro Z
  constructor
  · rintro ⟨hz, hne⟩
    apply (le_neg_iff E ρ Z).2
    intro j hj
    have hji : j = i := by
      have h := (le_iff E ρ Z _).1 hz j hj
      simpa only [read_singleton] using h
    have hi : read E ρ Z i := hji ▸ hj
    apply hne
    apply read_injective E ρ
    intro k
    rw [read_singleton]
    apply propext
    constructor
    · intro hk
      have h := (le_iff E ρ Z _).1 hz k hk
      simpa only [read_singleton] using h
    · intro hki
      exact hki.symm ▸ hi
  · intro hz
    have hn := (le_neg_iff E ρ Z).1 hz
    refine ⟨(le_iff E ρ Z _).2 (fun j hj => (hn j hj).elim), ?_⟩
    intro he
    have h := hn i
    rw [he, read_singleton] at h
    exact h rfl

theorem atomicity (E : Type) (ρ : RTy) (X : ρ.denote E) :
    LeR E ρ X (RTy.negD E ρ X) ∨ ∃ Y, AtomR E ρ Y ∧ LeR E ρ Y X := by
  classical
  by_cases hz : LeR E ρ X (RTy.negD E ρ X)
  · exact Or.inl hz
  · have hi : ∃ i, read E ρ X i := by
      by_contra hn
      exact hz ((le_neg_iff E ρ X).2 (fun i hi => hn ⟨i, hi⟩))
    obtain ⟨i, hi⟩ := hi
    refine Or.inr ⟨singleton E ρ i, singleton_atom E ρ i, ?_⟩
    apply (le_iff E ρ _ X).2
    intro j hj
    have he : j = i := by simpa only [read_singleton] using hj
    exact he.symm ▸ hi

theorem coext_eq (E : Type) : ∀ (ρ : RTy) (X Y : ρ.denote E), RTy.coextD E ρ X Y → X = Y
  | .t, X, Y, h => propext ⟨fun hx => h.1.elim (fun hn => (hn hx).elim) id,
      fun hy => h.2.elim (fun hn => (hn hy).elim) id⟩
  | .arr _ ρ, X, Y, h => funext fun x => coext_eq E ρ (X x) (Y x) (h x)

variable {Sig : Signature}

theorem box_iff (I : Interp Sig) (p : Sentence Sig) : Sentence.holds I (Term.box p) ↔ p.holds I := by
  change (p.denote I .nil = ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q)) ↔ p.denote I .nil
  rw [top_eq]
  exact ⟨fun h => Eq.mpr h True.intro, fun hp => propext ⟨fun _ => True.intro, fun _ => hp⟩⟩

theorem dia_iff (I : Interp Sig) (p : Sentence Sig) : Sentence.holds I (Term.dia p) ↔ p.holds I := by
  classical
  change (¬ p.denote I .nil = ((∀ q : Prop, q) ∧ ¬ ∀ q : Prop, q)) ↔ p.denote I .nil
  rw [bot_eq]
  exact ⟨fun hn => Classical.byContradiction (fun hp => hn (propext ⟨hp, False.elim⟩)),
    fun hp he => Eq.mp he hp⟩

/-- Exact generated all-type Extensionality instance, interpreted in the full model. -/
theorem extensionality_quoted (I : Interp Sig) (ρ : RTy) :
    Sentence.holds I (Term.ofPure (P.Extensionality.quoted ρ)) := by
  classical
  simp only [P.Extensionality.quoted, Term.ofPure, Sentence.holds, Term.denote, Var.denote, imp_eq]
  exact coext_eq I.D ρ

theorem atomicity_quoted (I : Interp Sig) (ρ : RTy) :
    Sentence.holds I (Term.ofPure (P.Atomicity.quoted ρ)) := by
  simpa only [P.Atomicity.quoted, Term.ofPure, Sentence.holds, Term.denote, Var.denote,
    iff_eq, imp_eq, iff_eq', AtomR, LeR] using atomicity I.D ρ

theorem functionalChoice_quoted (I : Interp Sig) (σ : Ty) (ρ : RTy) :
    Sentence.holds I (Term.ofPure (P.FunctionalChoice.quoted σ ρ)) := by
  classical
  simp only [P.FunctionalChoice.quoted, Term.ofPure, Sentence.holds, Term.denote, Var.denote, imp_eq]
  intro U hU
  exact ⟨fun x => Classical.choose (hU x), fun x => Classical.choose_spec (hU x)⟩

theorem distinctness_quoted (I : Interp Sig) (σ : Ty) :
    Sentence.holds I (Term.ofPure (P.NecessityOfDistinctness.quoted σ)) := by
  simp only [P.NecessityOfDistinctness.quoted, Term.ofPure, Sentence.holds,
    Term.denote, Var.denote, top_eq, imp_eq]
  intro x y hne
  exact propext ⟨fun _ => True.intro, fun _ => hne⟩

theorem boxedFunctionalChoice_quoted (I : Interp Sig) (σ : Ty) (ρ : RTy) :
    Sentence.holds I (Term.ofPure (P.NecFunctionalChoice.quoted σ ρ)) := by
  change Sentence.holds I (Term.box (Term.ofPure (P.FunctionalChoice.quoted σ ρ)))
  exact (box_iff I _).2 (functionalChoice_quoted I σ ρ)

theorem boxedDistinctness_quoted (I : Interp Sig) (σ : Ty) :
    Sentence.holds I (Term.ofPure (P.NecNecessityOfDistinctness.quoted σ)) := by
  change Sentence.holds I (Term.box (Term.ofPure (P.NecessityOfDistinctness.quoted σ)))
  exact (box_iff I _).2 (distinctness_quoted I σ)

theorem holds_extensionality (I : Interp Sig) : P.Extensionality.schemaIn.holds I := by
  rintro _ ⟨_, ⟨ρ, _, rfl⟩, rfl⟩
  exact extensionality_quoted I ρ

theorem holds_atomicity (I : Interp Sig) : P.Atomicity.schemaIn.holds I := by
  rintro _ ⟨_, ⟨ρ, _, rfl⟩, rfl⟩
  exact atomicity_quoted I ρ

theorem holds_functionalChoice (I : Interp Sig) : P.FunctionalChoice.schemaIn.holds I := by
  rintro _ ⟨_, ⟨σ, ρ, _, _, rfl⟩, rfl⟩
  exact functionalChoice_quoted I σ ρ

theorem holds_boxedFunctionalChoice (I : Interp Sig) : P.NecFunctionalChoice.schemaIn.holds I := by
  rintro _ ⟨_, ⟨σ, ρ, _, _, rfl⟩, rfl⟩
  exact boxedFunctionalChoice_quoted I σ ρ

theorem holds_C5 (I : Interp Sig) : P.NecNecessityOfDistinctness.schemaIn.holds I := by
  rintro _ ⟨_, ⟨σ, _, rfl⟩, rfl⟩
  exact boxedDistinctness_quoted I σ

theorem intensionalChoice_quoted (I : Interp Sig) (σ : Ty) :
    Sentence.holds I (Term.ofPure (P.IntensionalChoice.quoted σ)) := by
  simp only [P.IntensionalChoice.quoted, Term.ofPure, Sentence.holds,
    Term.denote, Var.denote, top_eq, imp_eq]
  intro F hF
  obtain ⟨x, hx⟩ := Eq.mpr hF True.intro
  refine ⟨(fun y => y = x), ?_, ?_⟩
  · funext y
    apply propext
    exact ⟨Or.inr, fun h => h.elim (fun he => he.symm ▸ hx) id⟩
  · apply propext
    exact ⟨fun _ => True.intro, fun _ => ⟨x, rfl, fun y hy => hy⟩⟩

theorem holds_intensionalChoice (I : Interp Sig) : P.IntensionalChoice.schemaIn.holds I := by
  rintro _ ⟨_, ⟨σ, _, rfl⟩, rfl⟩
  exact intensionalChoice_quoted I σ

theorem distinctnessPreservingCollapse_quoted (I : Interp Sig) :
    Sentence.holds I (Term.ofPure P.DistinctnessPreservingCollapse.quoted) := by
  simp only [P.DistinctnessPreservingCollapse.quoted, Term.ofPure, Sentence.holds,
    Term.denote, Var.denote, top_eq, bot_eq, imp_eq]
  intro p hp
  refine ⟨True, True.intro, ?_⟩
  apply propext
  exact ⟨fun _ => True.intro, fun _ _ => hp⟩

theorem holds_distinctnessPreservingCollapse (I : Interp Sig) :
    P.DistinctnessPreservingCollapse.schemaIn.holds I := by
  rintro _ ⟨_, rfl, rfl⟩
  exact distinctnessPreservingCollapse_quoted I

theorem holds_noContingency (I : Interp Sig) : (AxiomSet.noContingency Sig).holds I := by
  classical
  rintro _ ⟨_, p, rfl⟩
  change ¬ p.holds I ∨ Sentence.holds I (Term.box p)
  exact (Classical.em (p.holds I)).elim (fun h => Or.inr ((box_iff I p).2 h)) Or.inl

theorem holds_modalFreedom (I : Interp Sig) : (AxiomSet.modalFreedom Sig).holds I := by
  classical
  rintro _ ⟨_, cs, ds, P, Q, _, rfl⟩
  change ¬ (Sentence.holds I (Term.dia (Term.atConsts cs P)) ∧ Sentence.holds I (Term.dia (Term.atConsts ds Q))) ∨
    Sentence.holds I (Term.dia (Term.conj (Term.atConsts cs P) (Term.atConsts ds Q)))
  rcases Classical.em (Sentence.holds I (Term.dia (Term.atConsts cs P)) ∧
      Sentence.holds I (Term.dia (Term.atConsts ds Q))) with h | h
  · apply Or.inr
    apply (dia_iff I _).2
    exact ⟨(dia_iff I _).1 h.1, (dia_iff I _).1 h.2⟩
  · exact Or.inl h

end
end Classicism.Meta.FullExtensional
