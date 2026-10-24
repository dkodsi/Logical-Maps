import Classicism.Paper

/-!
# Impredicative averaging along an admitted operation

Direct source: `research/2026-10-23/choice-transversal-coherence/continuation-obstructions.md`,
§§1–2, and `continuation-code-operations.md`, §3 (`misc`, original ordinary
research, 23 October 2026; unpaginated).

`Orbit` is available at every relational code type. `Average` is the unary
material-union construction, with `AverageT` its separate nullary case. The
unary statements admit vectorization; this module itself does not assert a
checked all-arity certificate. No operation has individual-valued output.

Only `orbit_step_eq` uses Logical Equivalence, on an unconditional theorem.
The actual fibre-preservation hypothesis is never boxed or used under that
rule. The propositions-as-codes case needs no inhabitation assumption.
-/

namespace Classicism.Research.OrbitAveraging
open Classicism.Paper

section orbit
variable {τ : Type} [Rel τ]

/-- Two-way closure under the one displayed operation. -/
def Invariant (g : τ → τ) (P : τ → Prop) : Prop :=
  ∀ C, P C ↔ P (g C)

/-- Intersection of all admitted invariant predicates containing `A`. -/
def Orbit (g : τ → τ) (A B : τ) : Prop :=
  ∀ P : τ → Prop, P A ∧ Invariant g P → P B

theorem orbit_refl (g : τ → τ) (A : τ) : Orbit g A A :=
  fun _ h => h.1

theorem orbit_closed (g : τ → τ) (A : τ) : Invariant g (Orbit g A) :=
  fun C =>
    ⟨fun h P hP => (hP.2 C).1 (h P hP),
     fun h P hP => (hP.2 C).2 (h P hP)⟩

theorem orbit_step_iff (g : τ → τ) (A B : τ) :
    Orbit g A B ↔ Orbit g (g A) B :=
  ⟨fun h P hP => h P ⟨(hP.2 A).2 hP.1, hP.2⟩,
   fun h P hP => h P ⟨(hP.2 A).1 hP.1, hP.2⟩⟩

/-- Unconditional Logical Equivalence, with no actual fibre hypothesis. -/
theorem orbit_step_eq (g : τ → τ) (A : τ) :
    Orbit g A = Orbit g (g A) :=
  funext fun B => propext (orbit_step_iff g A B)

/-- An actual coextension fibre is one of the predicates in the intersection. -/
theorem orbit_coext_of_fiber (g : τ → τ) (A B : τ)
    (hf : ∀ C : τ, C ≡ A ↔ g C ≡ A) (h : Orbit g A B) : B ≡ A :=
  h (fun C => C ≡ A) ⟨Rel.coext_refl A, hf⟩

end orbit

section unary
variable {σ : Type} [Ty σ]

/-- Material union of the internally generated orbit of a property code. -/
def Average (g : (σ → Prop) → (σ → Prop)) (A : σ → Prop) : σ → Prop :=
  fun x => ∃ B : σ → Prop, Orbit g A B ∧ B x

theorem average_step_eq (g : (σ → Prop) → (σ → Prop)) (A : σ → Prop) :
    Average g A = Average g (g A) :=
  congrArg (fun P : (σ → Prop) → Prop =>
    fun x : σ => ∃ B : σ → Prop, P B ∧ B x) (orbit_step_eq g A)

/-- Every member of the internal orbit has the same averaging entity. -/
theorem average_eq_of_orbit (g : (σ → Prop) → (σ → Prop)) (A B : σ → Prop)
    (h : Orbit g A B) : Average g A = Average g B := by
  have he : Average g B = Average g A :=
    h (fun C => Average g C = Average g A)
      ⟨rfl, fun C =>
        ⟨fun hC => (average_step_eq g C).symm.trans hC,
         fun hC => (average_step_eq g C).trans hC⟩⟩
  exact he.symm

theorem average_coext_of_fiber (g : (σ → Prop) → (σ → Prop)) (A : σ → Prop)
    (hf : ∀ B : σ → Prop, B ≡ A ↔ g B ≡ A) : Average g A ≡ A := by
  intro x
  constructor
  · intro h
    obtain ⟨B, hB, hx⟩ := h
    exact (orbit_coext_of_fiber g A B hf hB x).1 hx
  · intro hx
    exact ⟨A, orbit_refl g A, hx⟩

theorem average_coext_of_preserves (g : (σ → Prop) → (σ → Prop))
    (hp : ∀ B : σ → Prop, g B ≡ B) (A : σ → Prop) : Average g A ≡ A :=
  average_coext_of_fiber g A (fun B =>
    ⟨fun h x => (hp B x).trans (h x),
     fun h x => (hp B x).symm.trans (h x)⟩)

end unary

/-- The nullary material union; its property codes are propositions. -/
def AverageT (g : Prop → Prop) (A : Prop) : Prop :=
  ∃ B : Prop, Orbit g A B ∧ B

theorem averageT_step_eq (g : Prop → Prop) (A : Prop) :
    AverageT g A = AverageT g (g A) :=
  congrArg (fun P : Prop → Prop => ∃ B : Prop, P B ∧ B) (orbit_step_eq g A)

theorem averageT_eq_of_orbit (g : Prop → Prop) (A B : Prop)
    (h : Orbit g A B) : AverageT g A = AverageT g B := by
  have he : AverageT g B = AverageT g A :=
    h (fun C => AverageT g C = AverageT g A)
      ⟨rfl, fun C =>
        ⟨fun hC => (averageT_step_eq g C).symm.trans hC,
         fun hC => (averageT_step_eq g C).trans hC⟩⟩
  exact he.symm

theorem averageT_coext_of_fiber (g : Prop → Prop) (A : Prop)
    (hf : ∀ B : Prop, (B ↔ A) ↔ (g B ↔ A)) : AverageT g A ↔ A := by
  constructor
  · intro h
    obtain ⟨B, hB, hBtrue⟩ := h
    exact (orbit_coext_of_fiber g A B hf hB).1 hBtrue
  · intro hA
    exact ⟨A, orbit_refl g A, hA⟩

theorem averageT_coext_of_preserves (g : Prop → Prop)
    (hp : ∀ B : Prop, g B ↔ B) (A : Prop) : AverageT g A ↔ A :=
  averageT_coext_of_fiber g A (fun B =>
    ⟨fun h => (hp B).trans h, fun h => (hp B).symm.trans h⟩)

end Classicism.Research.OrbitAveraging
