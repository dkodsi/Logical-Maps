import Classicism.Results.Research.FregeFiniteSets
import Classicism.Principles.Lattice

/-!
# Exact finite-profile and raw world-representation consequences

Direct source: `research/2026-10-22/notes/world-cardinality-ucp-20261022.md`,
§§8, 12, 20 (unpaginated original research, `misc`). The finite separating-family
proof also follows relational-coding-recursion-20261022.md §27.1.

Every profile quantified here is an admitted current predicate. Raw world
representation is not the rigid-profile possibility principle UCP. These results
hold in C without Choice, C5, Atomicity of the whole algebra or external fullness.
Quantified domain Infinity, not its finite-distinctness schema, is used at the end.
-/

namespace Classicism.Research.FiniteProfiles
open Classicism.Paper Classicism.Research.FregeFiniteSets

variable {σ τ : Type} [Ty σ] [Ty τ]

def ProfilesExist (H : τ → Prop) (E : σ → τ → Prop) : Prop :=
  ∀ X : σ → Prop, ∃ w, H w ∧ ∀ x, X x ↔ E x w

def ProfilesSeparate (H : τ → Prop) (E : σ → τ → Prop) : Prop :=
  ∀ u v, H u → H v → (∀ x, E x u ↔ E x v) → u = v

def UniqueProfiles (H : τ → Prop) (E : σ → τ → Prop) : Prop :=
  ∀ X : σ → Prop, ∃ w, (H w ∧ ∀ x, X x ↔ E x w) ∧
    ∀ v, (H v ∧ ∀ x, X x ↔ E x v) → v = w

theorem unique_profiles_iff (H : τ → Prop) (E : σ → τ → Prop) :
    UniqueProfiles H E ↔ ProfilesExist H E ∧ ProfilesSeparate H E := by
  constructor
  · intro h
    constructor
    · intro X
      obtain ⟨w, hw, _⟩ := h X
      exact ⟨w, hw⟩
    · intro u v hu hv huv
      obtain ⟨w, _, hunique⟩ := h (fun x => E x u)
      exact (hunique u ⟨hu, fun _ => Iff.rfl⟩).trans (hunique v ⟨hv, huv⟩).symm
  · intro h X
    obtain ⟨w, hw, hp⟩ := h.1 X
    refine ⟨w, ⟨hw, hp⟩, ?_⟩
    intro v hv
    exact h.2 v w hv.1 hw (fun x => (hv.2 x).symm.trans (hp x))

theorem finite_profiles_of_finite_coordinates (H : τ → Prop) (E : σ → τ → Prop)
    (hsep : ProfilesSeparate H E) (hfin : Finite (fun _ : σ => True)) : Finite H :=
  finite_separated_family (fun _ => True) H E hfin
    (fun u v hu hv hagree => hsep u v hu hv (fun x => hagree x True.intro))

/-- Singleton profiles give a relational injection of coordinates; no selector is taken. -/
theorem finite_coordinates_of_finite_profiles (H : τ → Prop) (E : σ → τ → Prop)
    (hex : ProfilesExist H E) (hfin : Finite H) : Finite (fun _ : σ => True) := by
  let R : σ → τ → Prop := fun x w => ∀ z, z = x ↔ E z w
  apply finite_injection_domain (fun _ => True) H R hfin
  · intro x _
    exact hex (fun z => z = x)
  · intro x z w _ _ hx hz
    exact (hz x).2 ((hx x).1 rfl)

theorem finite_profiles_iff_coordinates (H : τ → Prop) (E : σ → τ → Prop)
    (h : UniqueProfiles H E) : Finite H ↔ Finite (fun _ : σ => True) :=
  ⟨finite_coordinates_of_finite_profiles H E ((unique_profiles_iff H E).1 h).1,
    finite_profiles_of_finite_coordinates H E ((unique_profiles_iff H E).1 h).2⟩

/-- Cantor diagonalization excludes even many-code, disjoint-fibre labellings. -/
theorem profiles_no_injection (H : τ → Prop) (E : σ → τ → Prop)
    (hex : ProfilesExist H E) (R : τ → σ → Prop)
    (htotal : ∀ w, H w → ∃ x, R w x)
    (hinj : ∀ u v x, H u → H v → R u x → R v x → u = v) : False := by
  obtain ⟨w, hw, hprofile⟩ := hex (fun x => ∃ u, H u ∧ R u x ∧ ¬ E x u)
  obtain ⟨a, hwa⟩ := htotal w hw
  have hneg : ¬ E a w := by
    intro he
    obtain ⟨u, hu, hua, hnot⟩ := (hprofile a).2 he
    have huw : u = w := hinj u w a hu hw hua hwa
    exact hnot (huw.symm ▸ he)
  exact hneg ((hprofile a).1 ⟨w, hw, hwa, hneg⟩)

def RawWR (V : σ → Prop) : Prop :=
  ProfilesExist (Atom (τ := Prop)) (fun x w => w ≤ V x)

def RawUWR (V : σ → Prop) : Prop :=
  UniqueProfiles (Atom (τ := Prop)) (fun x w => w ≤ V x)

def WorldSeparation (V : σ → Prop) : Prop :=
  ProfilesSeparate (Atom (τ := Prop)) (fun x w => w ≤ V x)

theorem raw_uwr_iff (V : σ → Prop) : RawUWR V ↔ RawWR V ∧ WorldSeparation V :=
  unique_profiles_iff _ _

theorem raw_wr_no_injection (V : σ → Prop) (hV : RawWR V)
    (R : Prop → σ → Prop) (htotal : ∀ w, Atom w → ∃ x, R w x)
    (hinj : ∀ u v x, Atom u → Atom v → R u x → R v x → u = v) : False :=
  profiles_no_injection _ _ hV R htotal hinj

theorem no_raw_wr_propositions (V : Prop → Prop) : ¬ RawWR V := by
  intro hV
  exact raw_wr_no_injection V hV (fun w x => w = x)
    (fun w _ => ⟨w, rfl⟩) (fun u v x _ _ hu hv => hu.trans hv.symm)

/-- A concrete constant-relation injection, with its needed argument witness explicit. -/
theorem no_raw_wr_unary (a : σ) (V : (σ → Prop) → Prop) : ¬ RawWR V := by
  intro hV
  exact raw_wr_no_injection V hV (fun w X => (fun _ : σ => w) = X)
    (fun w _ => ⟨(fun _ => w), rfl⟩)
    (fun u v X _ _ hu hv => congrFun (hu.trans hv.symm) a)

theorem raw_uwr_finite_atoms_iff (V : σ → Prop) (hV : RawUWR V) :
    Finite (Atom (τ := Prop)) ↔ Finite (fun _ : σ => True) :=
  finite_profiles_iff_coordinates _ _ hV

theorem raw_uwr_infinity_iff (V : σ → Prop) (hV : RawUWR V) :
    Classicism.P.AxiomOfInfinity σ ↔ ¬ Finite (Atom (τ := Prop)) :=
  ⟨fun hi hf => hi ((raw_uwr_finite_atoms_iff V hV).1 hf),
    fun ha hf => ha ((raw_uwr_finite_atoms_iff V hV).2 hf)⟩

end Classicism.Research.FiniteProfiles
