import ClassicismZFC.CHCardinality

/-!
# Internal Schroeder--Bernstein by a finite defining formula

The least closed set is the intersection of the internally represented
candidates. Its existence follows from actual finite-formula Separation.
The proof uses neither an externally indexed omega-union nor external
subsets of the carrier. Every final bijection is an internal graph.

Original source, misc, 23 October 2026. Not yet compiler-certified.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.CHCardinality

open SetLaws

universe u
variable {M : Type u} [L.Structure M]

def Step (G H x y : M) : Prop := ∃ b, Edge G x b ∧ Edge H b y

def Root (A H x : M) : Prop := memM x A ∧ ¬ ∃ b, Edge H b x

def Candidate (A G H U : M) : Prop :=
  Subset U A ∧ (∀ x, Root A H x → memM x U) ∧
    ∀ x y, memM x U → Step G H x y → memM y U

def stepF (G H x y : Tm) : Fm := exF fun b =>
  andF (memF (pairT x (varT b)) G) (memF (pairT (varT b) y) H)

def rootF (A H x : Tm) : Fm :=
  andF (memF x A) (notF (exF fun b => memF (pairT (varT b) x) H))

def candidateF (A G H U : Tm) : Fm :=
  andF (subsetF U A)
    (andF (allF fun x => impF (rootF A H (varT x)) (memF (varT x) U))
      (allF fun x => allF fun y => impF (memF (varT x) U)
        (impF (stepF G H (varT x) (varT y)) (memF (varT y) U))))

/-- Initial levels `A,G,H,x`; the candidate set is bound at level 4. -/
def closureFilter : L.BoundedFormula Empty 4 :=
  (allF fun U => impF
    (candidateF (varT 0) (varT 1) (varT 2) (varT U))
    (memF (varT 3) (varT U))) 4

theorem realize_closureFilter (A G H x : M) :
    closureFilter.Realize default (Fin.snoc ![A, G, H] x) ↔
      ∀ U, Candidate A G H U → memM x U := by
  simp [closureFilter, candidateF, rootF, stepF, Candidate, Root, Step,
    Subset, Edge, subsetF, allF, exF, andF, notF, impF, memF, varT, memM, Fin.snoc]

/-- The least internally coded candidate exists. -/
theorem least_candidate (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B G H : M} (hG : Injection A B G) (hH : Injection B A H) :
    ∃ U, Candidate A G H U ∧ ∀ V, Candidate A G H V → Subset U V := by
  obtain ⟨U, hU⟩ := Separation.separation hZFC 3 closureFilter ![A, G, H] A
  have hmem : ∀ x, memM x U ↔ memM x A ∧ ∀ V, Candidate A G H V → memM x V :=
    fun x => by rw [hU x, realize_closureFilter]
  have hUA : Subset U A := fun x hx => ((hmem x).mp hx).1
  refine ⟨U, ⟨hUA, ?_, ?_⟩, ?_⟩
  · intro x hx
    exact (hmem x).mpr ⟨hx.1, fun V hV => hV.2.1 x hx⟩
  · intro x y hx hxy
    obtain ⟨b, hxb, hby⟩ := hxy
    refine (hmem y).mpr ⟨(hH.1 b y hby).2, ?_⟩
    intro V hV
    exact hV.2.2 x y (((hmem x).mp hx).2 V hV) ⟨b, hxb, hby⟩
  · intro V hV x hx
    exact ((hmem x).mp hx).2 V hV

/-- The one-step image union the root set is itself internally definable.
Initial levels `A,G,H,U,y`. -/
def oneStepFilter : L.BoundedFormula Empty 5 :=
  (orF (rootF (varT 0) (varT 2) (varT 4))
    (exF fun x => andF (memF (varT x) (varT 3))
      (stepF (varT 1) (varT 2) (varT x) (varT 4)))) 5

theorem realize_oneStepFilter (A G H U y : M) :
    oneStepFilter.Realize default (Fin.snoc ![A, G, H, U] y) ↔
      Root A H y ∨ ∃ x, memM x U ∧ Step G H x y := by
  simp [oneStepFilter, rootF, stepF, Root, Step, Edge,
    orF, exF, andF, notF, memF, varT, memM, Fin.snoc]

/-- Minimality proves the needed fixed-point equation without transfinite
or external finite iteration. -/
theorem least_candidate_fixed (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B G H U : M} (hH : Injection B A H)
    (hU : Candidate A G H U)
    (hmin : ∀ V, Candidate A G H V → Subset U V) :
    ∀ y, memM y U ↔ Root A H y ∨ ∃ x, memM x U ∧ Step G H x y := by
  obtain ⟨V, hV⟩ := Separation.separation hZFC 4 oneStepFilter ![A, G, H, U] A
  have hVmem : ∀ y, memM y V ↔ memM y A ∧
      (Root A H y ∨ ∃ x, memM x U ∧ Step G H x y) :=
    fun y => by rw [hV y, realize_oneStepFilter]
  have hVU : Subset V U := by
    intro y hy
    rcases ((hVmem y).mp hy).2 with hr | ⟨x, hx, hxy⟩
    · exact hU.2.1 y hr
    · exact hU.2.2 x y hx hxy
  have hVcand : Candidate A G H V := by
    refine ⟨fun y hy => ((hVmem y).mp hy).1, ?_, ?_⟩
    · intro y hy
      exact (hVmem y).mpr ⟨hy.1, Or.inl hy⟩
    · intro x y hx hxy
      obtain ⟨b, hxb, hby⟩ := hxy
      exact (hVmem y).mpr ⟨(hH.1 b y hby).2, Or.inr ⟨x, hVU x hx, b, hxb, hby⟩⟩
  intro y
  constructor
  · intro hy
    exact ((hVmem y).mp (hmin V hVcand y hy)).2
  · rintro (hr | ⟨x, hx, hxy⟩)
    · exact hU.2.1 y hr
    · exact hU.2.2 x y hx hxy

/-- Piecewise graph: use G on U and the inverse of H off U.
Initial levels `U,G,H,z`. -/
def sbFilter : L.BoundedFormula Empty 4 :=
  (exF fun x => exF fun y =>
    andF (eqF (varT 3) (pairT (varT x) (varT y)))
      (orF
        (andF (memF (varT x) (varT 0))
          (memF (pairT (varT x) (varT y)) (varT 1)))
        (andF (notF (memF (varT x) (varT 0)))
          (memF (pairT (varT y) (varT x)) (varT 2))))) 4

theorem realize_sbFilter (U G H z : M) :
    sbFilter.Realize default (Fin.snoc ![U, G, H] z) ↔
      ∃ x y, z = pairM x y ∧
        ((memM x U ∧ Edge G x y) ∨ (¬ memM x U ∧ Edge H y x)) := by
  simp [sbFilter, exF, andF, orF, notF, eqF, memF, varT, Edge, memM, Fin.snoc]

theorem sb_graph (hZFC : M ⊨ Erdos501.FOL.ZFC) (A B U G H : M) :
    ∃ K, ∀ x y, Edge K x y ↔ memM x A ∧ memM y B ∧
      ((memM x U ∧ Edge G x y) ∨ (¬ memM x U ∧ Edge H y x)) := by
  obtain ⟨K, hK⟩ := graph_separation hZFC 3 sbFilter ![U, G, H] A B
  refine ⟨K, ?_⟩
  intro x y
  rw [hK, realize_sbFilter]
  constructor
  · rintro ⟨hx, hy, a, b, heq, hab⟩
    obtain ⟨rfl, rfl⟩ := pair_injective hZFC x y a b heq
    exact ⟨hx, hy, hab⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, x, y, rfl, hxy⟩

/-- Actual internal Schroeder--Bernstein. The conclusion quantifies over
an element of the model, not over external functions on its carrier. -/
theorem schroeder_bernstein (hZFC : M ⊨ Erdos501.FOL.ZFC)
    {A B : M} (hAB : Injects A B) (hBA : Injects B A) : Equinumerous A B := by
  classical
  obtain ⟨G, hG⟩ := hAB
  obtain ⟨H, hH⟩ := hBA
  obtain ⟨U, hU, hmin⟩ := least_candidate hZFC hG hH
  have hfix := least_candidate_fixed hZFC hH hU hmin
  obtain ⟨K, hK⟩ := sb_graph hZFC A B U G H
  refine ⟨K, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y h
    exact ⟨((hK x y).mp h).1, ((hK x y).mp h).2.1⟩
  · intro x hx
    by_cases hxU : memM x U
    · obtain ⟨y, hxy⟩ := hG.2.1 x hx
      exact ⟨y, (hK x y).mpr ⟨hx, (hG.1 x y hxy).2, Or.inl ⟨hxU, hxy⟩⟩⟩
    · have hex : ∃ y, Edge H y x := by
        by_contra hn
        exact hxU (hU.2.1 x ⟨hx, hn⟩)
      obtain ⟨y, hyx⟩ := hex
      exact ⟨y, (hK x y).mpr ⟨hx, (hH.1 y x hyx).1, Or.inr ⟨hxU, hyx⟩⟩⟩
  · intro x y z hxy hxz
    rcases ((hK x y).mp hxy).2.2 with ⟨hxU, hxy⟩ | ⟨hxU, hyx⟩ <;>
      rcases ((hK x z).mp hxz).2.2 with ⟨hxU', hxz⟩ | ⟨hxU', hzx⟩
    · exact hG.2.2.1 x y z hxy hxz
    · exact False.elim (hxU' hxU)
    · exact False.elim (hxU hxU')
    · exact hH.2.2.2 y z x hyx hzx
  · intro x y z hxz hyz
    rcases ((hK x z).mp hxz).2.2 with ⟨hxU, hxz⟩ | ⟨hxU, hzx⟩ <;>
      rcases ((hK y z).mp hyz).2.2 with ⟨hyU, hyz⟩ | ⟨hyU, hzy⟩
    · exact hG.2.2.2 x y z hxz hyz
    · exact False.elim (hyU (hU.2.2 x y hxU ⟨z, hxz, hzy⟩))
    · exact False.elim (hxU (hU.2.2 y x hyU ⟨z, hyz, hzx⟩))
    · exact hH.2.2.1 z x y hzx hzy
  · intro y hy
    by_cases hex : ∃ x, memM x U ∧ Edge G x y
    · obtain ⟨x, hxU, hxy⟩ := hex
      exact ⟨x, (hK x y).mpr ⟨hU.1 x hxU, hy, Or.inl ⟨hxU, hxy⟩⟩⟩
    · obtain ⟨x, hyx⟩ := hH.2.1 y hy
      have hxU : ¬ memM x U := by
        intro hx
        rcases (hfix x).mp hx with hr | ⟨a, ha, b, hab, hbx⟩
        · exact hr.2 ⟨y, hyx⟩
        · have hby : b = y := hH.2.2.2 b y x hbx hyx
          subst b
          exact hex ⟨a, ha, hab⟩
      exact ⟨x, (hK x y).mpr ⟨(hH.1 y x hyx).2, hy, Or.inr ⟨hxU, hyx⟩⟩⟩

#print axioms least_candidate
#print axioms least_candidate_fixed
#print axioms sb_graph
#print axioms schroeder_bernstein

end ClassicismZFC.CHCardinality
