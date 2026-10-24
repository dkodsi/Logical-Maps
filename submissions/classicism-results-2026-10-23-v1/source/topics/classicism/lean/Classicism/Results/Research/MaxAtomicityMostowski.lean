import Mathlib.SetTheory.ZFC.Basic

/-!
# Mostowski collapse for the universe-code argument

Direct source: the original proof in
`research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md`,
section 3 (misc, unpaginated). This file supplies the well-founded extensional
collapse used there, as ordinary Lean metatheory over Mathlib's actual ZFSet.

The collapse is constructed by well-founded recursion. Injectivity, exact
membership preservation, transitivity of its range, uniqueness of the recursive
map, and the predecessor/member bijection are conclusions with proof bodies.
No collapse, embedding, or set-theoretic existence axiom is introduced.

This alone does not identify the range with H_(kappa+). That additionally needs
the cardinality and small-subset filling arguments and their HCode interpretation.
This source awaits the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityMostowski

universe u

variable {A : Type u} {r : A → A → Prop}

/-- Extensionality in exactly the predecessor-set sense used by HCode. -/
def Extensional (r : A → A → Prop) : Prop :=
  ∀ x y : A, (∀ z : A, r z x ↔ r z y) → x = y

/-- A genuine ZFSet-valued well-founded recursive construction. -/
noncomputable def collapse (wf : WellFounded r) : A → ZFSet.{u} :=
  wf.fix (fun x ih => ZFSet.range (fun y : {y : A // r y x} => ih y.1 y.2))

theorem collapse_eq (wf : WellFounded r) (x : A) :
    collapse wf x = ZFSet.range (fun y : {y : A // r y x} => collapse wf y.1) := by
  exact wf.fix_eq _ x

/-- The recursive equation stated as exact membership, in both directions. -/
theorem mem_collapse (wf : WellFounded r) (x : A) (z : ZFSet.{u}) :
    z ∈ collapse wf x ↔ ∃ y : A, r y x ∧ collapse wf y = z := by
  rw [collapse_eq, ZFSet.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.1, y.2, hy⟩
  · rintro ⟨y, hy, hz⟩
    exact ⟨⟨y, hy⟩, hz⟩

theorem collapse_mem_of_rel (wf : WellFounded r) {x y : A} (hxy : r x y) :
    collapse wf x ∈ collapse wf y :=
  (mem_collapse wf y (collapse wf x)).2 ⟨x, hxy, rfl⟩

/-- A single well-founded induction proves global injectivity. In the reverse
membership direction the induction is applied to a predecessor of x, not to an
unjustified predecessor of the other argument. -/
theorem collapse_injective (wf : WellFounded r) (hext : Extensional r) :
    Function.Injective (collapse wf) := by
  intro x
  induction x using wf.induction with
  | h x ih =>
    intro y hxy
    apply hext x y
    intro z
    constructor
    · intro hzx
      have hzmem : collapse wf z ∈ collapse wf y := by
        rw [← hxy]
        exact collapse_mem_of_rel wf hzx
      obtain ⟨w, hwy, hwz⟩ := (mem_collapse wf y (collapse wf z)).1 hzmem
      have hzw : z = w := ih z hzx hwz.symm
      exact hzw.symm ▸ hwy
    · intro hzy
      have hzmem : collapse wf z ∈ collapse wf x := by
        rw [hxy]
        exact collapse_mem_of_rel wf hzy
      obtain ⟨w, hwx, hwz⟩ := (mem_collapse wf x (collapse wf z)).1 hzmem
      have hwz' : w = z := ih w hwx hwz
      exact hwz' ▸ hwx

/-- Extensionality upgrades forward membership preservation to equivalence. -/
theorem collapse_mem_iff (wf : WellFounded r) (hext : Extensional r) (x y : A) :
    collapse wf x ∈ collapse wf y ↔ r x y := by
  constructor
  · intro h
    obtain ⟨z, hzy, hzx⟩ := (mem_collapse wf y (collapse wf x)).1 h
    have hzx' : z = x := collapse_injective wf hext hzx
    exact hzx' ▸ hzy
  · exact collapse_mem_of_rel wf

/-- The range is itself an actual set, not merely an external class. -/
noncomputable def collapseRange (wf : WellFounded r) : ZFSet.{u} :=
  ZFSet.range (collapse wf)

theorem mem_collapseRange (wf : WellFounded r) (z : ZFSet.{u}) :
    z ∈ collapseRange wf ↔ ∃ x : A, collapse wf x = z :=
  ZFSet.mem_range

/-- Every member of a member of the range lies in the range. No assumption of
transitivity of r is needed for the transitivity of the collapsed set. -/
theorem collapseRange_transitive (wf : WellFounded r) :
    ∀ x : ZFSet.{u}, x ∈ collapseRange wf →
      ∀ z : ZFSet.{u}, z ∈ x → z ∈ collapseRange wf := by
  intro x hx z hz
  obtain ⟨a, ha⟩ := (mem_collapseRange wf x).1 hx
  rw [← ha] at hz
  obtain ⟨b, _, hb⟩ := (mem_collapse wf a z).1 hz
  exact (mem_collapseRange wf z).2 ⟨b, hb⟩

/-- Any other map satisfying the same recursive membership equation is equal
to this collapse. Extensionality of r is unnecessary for recursion uniqueness. -/
theorem collapse_unique (wf : WellFounded r) (g : A → ZFSet.{u})
    (hg : ∀ x : A, ∀ z : ZFSet.{u},
      z ∈ g x ↔ ∃ y : A, r y x ∧ g y = z) : g = collapse wf := by
  funext x
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [hg x z, mem_collapse]
    constructor
    · rintro ⟨y, hy, hyz⟩
      exact ⟨y, hy, (ih y hy).symm.trans hyz⟩
    · rintro ⟨y, hy, hyz⟩
      exact ⟨y, hy, (ih y hy).trans hyz⟩

/-- A predecessor is sent to the corresponding member of the collapsed set. -/
noncomputable def predecessorMap (wf : WellFounded r) (x : A) :
    {y : A // r y x} → {z : ZFSet.{u} // z ∈ collapse wf x} :=
  fun y => ⟨collapse wf y.1, collapse_mem_of_rel wf y.2⟩

theorem predecessorMap_bijective (wf : WellFounded r) (hext : Extensional r)
    (x : A) : Function.Bijective (predecessorMap wf x) := by
  constructor
  · intro y z h
    apply Subtype.ext
    apply collapse_injective wf hext
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨y, hy, hyz⟩ := (mem_collapse wf x z.1).1 z.2
    refine ⟨⟨y, hy⟩, ?_⟩
    exact Subtype.ext hyz

/-- The actual bijection needed to transfer the row cardinality bound. -/
noncomputable def predecessorEquiv (wf : WellFounded r) (hext : Extensional r)
    (x : A) : {y : A // r y x} ≃ {z : ZFSet.{u} // z ∈ collapse wf x} :=
  Equiv.ofBijective (predecessorMap wf x) (predecessorMap_bijective wf hext x)

/-- Existence of a transitive-set presentation, including the actual map and
its injectivity and exact membership theorem. No presentation is an input. -/
theorem exists_transitive_collapse (wf : WellFounded r) (hext : Extensional r) :
    ∃ M : ZFSet.{u}, ∃ f : A → ZFSet.{u},
      Function.Injective f ∧
      (∀ z : ZFSet.{u}, z ∈ M ↔ ∃ x : A, f x = z) ∧
      (∀ x y : A, f x ∈ f y ↔ r x y) ∧
      (∀ x : ZFSet.{u}, x ∈ M → ∀ z : ZFSet.{u}, z ∈ x → z ∈ M) :=
  ⟨collapseRange wf, collapse wf, collapse_injective wf hext,
    mem_collapseRange wf, collapse_mem_iff wf hext, collapseRange_transitive wf⟩

end Classicism.Meta.Research.MaxAtomicityMostowski

#print axioms Classicism.Meta.Research.MaxAtomicityMostowski.collapse_injective
#print axioms Classicism.Meta.Research.MaxAtomicityMostowski.collapse_mem_iff
#print axioms Classicism.Meta.Research.MaxAtomicityMostowski.collapseRange_transitive
#print axioms Classicism.Meta.Research.MaxAtomicityMostowski.collapse_unique
#print axioms Classicism.Meta.Research.MaxAtomicityMostowski.predecessorMap_bijective
#print axioms Classicism.Meta.Research.MaxAtomicityMostowski.exists_transitive_collapse
