import Classicism.Results.Research.MaxAtomicityMostowski

/-!
# What small rows and small-subset filling determine

Direct source: `max-atomicity-inconsistency-proof.md`, section 3 (misc,
unpaginated). This proves the set-theoretic core of the HCode characterization.

The size bound is expressed by actual embeddings into a fixed type K. No
cardinal-arithmetic or collapse conclusion is assumed. The collapse range is
proved to contain exactly the sets that hereditarily have K-small member sets.
In particular, any two well-founded extensional presentations with the same
row bound and filling property collapse onto literally the same ZFSet.

For infinite K the further identification with the usual transitive-closure
definition of H_(|K|+) needs the countable-union cardinal bound. That result and
the C-term interpretation are separate obligations, not renamed as proved here.
Source submission only: the designated serial compiler performs Lean checking.
-/

namespace Classicism.Meta.Research.MaxAtomicityHereditaryCover

open MaxAtomicityMostowski

universe u

variable {A : Type u} {r : A → A → Prop} (K : Type u)

def MembersSmall (x : ZFSet.{u}) : Prop :=
  Nonempty ({z : ZFSet.{u} // z ∈ x} ↪ K)

def HereditarilySmall (x : ZFSet.{u}) : Prop :=
  ZFSet.Hereditarily (MembersSmall K) x

def RowsSmall (r : A → A → Prop) : Prop :=
  ∀ x : A, Nonempty ({y : A // r y x} ↪ K)

def FillsSmall (r : A → A → Prop) : Prop :=
  ∀ X : Set A, Nonempty (X ↪ K) → ∃ x : A, ∀ y : A, r y x ↔ y ∈ X

/-- The explicit predecessor/member equivalence transfers the size bound. -/
theorem membersSmall_collapse (wf : WellFounded r) (hext : Extensional r)
    (hrows : RowsSmall K r) (x : A) : MembersSmall K (collapse wf x) := by
  obtain ⟨e⟩ := hrows x
  exact ⟨(predecessorEquiv wf hext x).symm.toEmbedding.trans e⟩

/-- All descendants inherit the row bound by actual well-founded induction. -/
theorem collapse_hereditarilySmall (wf : WellFounded r) (hext : Extensional r)
    (hrows : RowsSmall K r) (x : A) : HereditarilySmall K (collapse wf x) := by
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.hereditarily_iff.mpr
    constructor
    · exact membersSmall_collapse K wf hext hrows x
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := (mem_collapse wf x z).1 hz
      rw [← hyz]
      exact ih y hy

/-- Filling is sufficient for the reverse inclusion. The small subset being
filled is built from all preimages of members of x; its embedding into K is
constructed using collapse injectivity and the given member embedding for x. -/
theorem hereditarilySmall_mem_range (wf : WellFounded r) (hext : Extensional r)
    (hfill : FillsSmall K r) :
    ∀ x : ZFSet.{u}, HereditarilySmall K x → x ∈ collapseRange wf := by
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    have hxsmall : MembersSmall K x := ZFSet.Hereditarily.self hx
    obtain ⟨e⟩ := hxsmall
    let X : Set A := {a | collapse wf a ∈ x}
    let j : X ↪ K :=
      { toFun := fun a => e ⟨collapse wf a.1, a.2⟩
        inj' := by
          intro a b hab
          apply Subtype.ext
          apply collapse_injective wf hext
          exact congrArg Subtype.val (e.injective hab) }
    obtain ⟨a, ha⟩ := hfill X ⟨j⟩
    have hax : collapse wf a = x := by
      apply ZFSet.ext
      intro z
      constructor
      · intro hza
        obtain ⟨b, hba, hbz⟩ := (mem_collapse wf a z).1 hza
        have hbx : collapse wf b ∈ x := (ha b).1 hba
        exact hbz ▸ hbx
      · intro hzx
        have hzsmall : HereditarilySmall K z := ZFSet.Hereditarily.mem hx hzx
        have hzrange : z ∈ collapseRange wf := ih z hzx hzsmall
        obtain ⟨b, hbz⟩ := (mem_collapseRange wf z).1 hzrange
        apply (mem_collapse wf a z).2
        refine ⟨b, (ha b).2 ?_, hbz⟩
        change collapse wf b ∈ x
        rw [hbz]
        exact hzx
    exact (mem_collapseRange wf x).2 ⟨a, hax⟩

/-- Exact characterization of the collapse range, with both directions proved. -/
theorem mem_range_iff_hereditarilySmall (wf : WellFounded r)
    (hext : Extensional r) (hrows : RowsSmall K r) (hfill : FillsSmall K r)
    (x : ZFSet.{u}) : x ∈ collapseRange wf ↔ HereditarilySmall K x := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (mem_collapseRange wf x).1 hx
    rw [← ha]
    exact collapse_hereditarilySmall K wf hext hrows a
  · exact hereditarilySmall_mem_range K wf hext hfill x

/-- Small rows and filling determine one literal target set, independently
of the choice of presentation carrier or relation. -/
theorem collapseRange_eq {A' : Type u} {r' : A' → A' → Prop}
    (wf : WellFounded r) (wf' : WellFounded r')
    (hext : Extensional r) (hext' : Extensional r')
    (hrows : RowsSmall K r) (hrows' : RowsSmall K r')
    (hfill : FillsSmall K r) (hfill' : FillsSmall K r') :
    collapseRange wf = collapseRange wf' := by
  apply ZFSet.ext
  intro x
  rw [mem_range_iff_hereditarilySmall K wf hext hrows hfill,
    mem_range_iff_hereditarilySmall K wf' hext' hrows' hfill']

end Classicism.Meta.Research.MaxAtomicityHereditaryCover

#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryCover.membersSmall_collapse
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryCover.collapse_hereditarilySmall
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryCover.hereditarilySmall_mem_range
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryCover.mem_range_iff_hereditarilySmall
#print axioms Classicism.Meta.Research.MaxAtomicityHereditaryCover.collapseRange_eq
