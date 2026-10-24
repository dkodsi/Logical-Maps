import ClassicismZFC.SourceFieldSemantics

/-!
# Derived algebra for the source field graphs

All results below follow directly from the twenty source clauses decomposed
by `SourceFieldSemantics.Field`. No external field instance or extra algebra
law is assumed. Domain guards are retained; operation-output membership is
derived from the source operation's totality and unrestricted uniqueness.
-/

open FirstOrder FirstOrder.Language
open Erdos501.FOL
open scoped FirstOrder

namespace ClassicismZFC.SourceFieldAlgebra

open SetLaws SourceFieldSemantics

universe u

variable {M : Type u} [L.Structure M]
variable {E Add Mul Lt zero one : M}

/-- Even an initially unguarded graph output lies in the domain. -/
theorem op_output_mem {Op x y z : M} (hOp : IsOp2 E Op)
    (hx : memM x E) (hy : memM y E) (hg : app2 Op x y z) : memM z E := by
  obtain ⟨w, hw, _, huniq⟩ := hOp x hx y hy
  rw [huniq z hg]
  exact hw

/-- The source operation clause compares arbitrary competing outputs. -/
theorem op_output_unique {Op x y z w : M} (hOp : IsOp2 E Op)
    (hx : memM x E) (hy : memM y E)
    (hz : app2 Op x y z) (hw : app2 Op x y w) : z = w := by
  obtain ⟨v, _, _, huniq⟩ := hOp x hx y hy
  exact (huniq z hz).trans (huniq w hw).symm

variable (H : SourceFieldSemantics.Field E Add Mul Lt zero one)

include H

theorem le_refl {x : M} (_hx : memM x E) : le Lt x x := Or.inr rfl

theorem le_total {a b : M} (ha : memM a E) (hb : memM b E) :
    le Lt a b ∨ le Lt b a := by
  rcases H.total a ha b hb with hab | hab | hba
  · exact Or.inl (Or.inl hab)
  · exact Or.inl (Or.inr hab)
  · exact Or.inr (Or.inl hba)

theorem le_antisymm {a b : M} (ha : memM a E) (hb : memM b E)
    (hab : le Lt a b) (hba : le Lt b a) : a = b := by
  rcases hab with hab | hab
  · rcases hba with hba | hba
    · exact False.elim (H.irrefl a ha (H.trans a ha b hb a ha hab hba))
    · exact hba.symm
  · exact hab

theorem le_trans {a b c : M} (ha : memM a E) (hb : memM b E) (hc : memM c E)
    (hab : le Lt a b) (hbc : le Lt b c) : le Lt a c := by
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · exact Or.inl (H.trans a ha b hb c hc hab hbc)
    · subst c
      exact Or.inl hab
  · subst b
    exact hbc

/-- Add the same element on the right, including the equality case. -/
theorem add_le_add_right {a b c x y : M}
    (ha : memM a E) (hb : memM b E) (hc : memM c E)
    (_hx : memM x E) (_hy : memM y E) (hab : le Lt a b)
    (hax : app2 Add a c x) (hby : app2 Add b c y) : le Lt x y := by
  rcases hab with hab | hab
  · exact Or.inl (H.addCompat a ha b hb c hc x y hab hax hby)
  · subst b
    exact Or.inr (op_output_unique H.isOp2_plus ha hc hax hby)

/-- Add the same element on the left, by commutativity and right monotonicity. -/
theorem add_le_add_left {a b c x y : M}
    (ha : memM a E) (hb : memM b E) (hc : memM c E)
    (hx : memM x E) (hy : memM y E) (hab : le Lt a b)
    (hax : app2 Add c a x) (hby : app2 Add c b y) : le Lt x y :=
  add_le_add_right H ha hb hc hx hy hab
    (H.comm_plus c hc a ha x hax) (H.comm_plus c hc b hb y hby)

/-- Cancellation of a common right summand follows from strict compatibility
and totality of the source order. -/
theorem add_cancel_right {a b c z : M}
    (ha : memM a E) (hb : memM b E) (hc : memM c E)
    (haz : app2 Add a c z) (hbz : app2 Add b c z) : a = b := by
  have hz : memM z E := op_output_mem H.isOp2_plus ha hc haz
  rcases H.total a ha b hb with hab | hab | hba
  · exact False.elim (H.irrefl z hz (H.addCompat a ha b hb c hc z z hab haz hbz))
  · exact hab
  · exact False.elim (H.irrefl z hz (H.addCompat b hb a ha c hc z z hba hbz haz))

theorem add_cancel_left {a b c z : M}
    (ha : memM a E) (hb : memM b E) (hc : memM c E)
    (haz : app2 Add c a z) (hbz : app2 Add c b z) : a = b :=
  add_cancel_right H ha hb hc
    (H.comm_plus c hc a ha z haz) (H.comm_plus c hc b hb z hbz)

/-- The equality-form associativity clause supplies the required graph edge. -/
theorem graph_assoc_plus {a b c x y z : M}
    (ha : memM a E) (hb : memM b E) (hc : memM c E)
    (hab : app2 Add a b x) (hxc : app2 Add x c y) (hbc : app2 Add b c z) :
    app2 Add a z y := by
  have hz : memM z E := op_output_mem H.isOp2_plus hb hc hbc
  obtain ⟨w, _, haw, _⟩ := H.isOp2_plus a ha z hz
  have heq : y = w := H.assoc_plus a ha b hb c hc x y z w hab hxc hbc haw
  rw [heq]
  exact haw

theorem graph_assoc_times {a b c x y z : M}
    (ha : memM a E) (hb : memM b E) (hc : memM c E)
    (hab : app2 Mul a b x) (hxc : app2 Mul x c y) (hbc : app2 Mul b c z) :
    app2 Mul a z y := by
  have hz : memM z E := op_output_mem H.isOp2_times hb hc hbc
  obtain ⟨w, _, haw, _⟩ := H.isOp2_times a ha z hz
  have heq : y = w := H.assoc_times a ha b hb c hc x y z w hab hxc hbc haw
  rw [heq]
  exact haw

/-- The source distributivity equality supplies the desired sum graph. -/
theorem graph_distrib {a b c s t x y : M}
    (ha : memM a E) (hb : memM b E) (hc : memM c E)
    (hbc : app2 Add b c s) (has : app2 Mul a s t)
    (hab : app2 Mul a b x) (hac : app2 Mul a c y) : app2 Add x y t := by
  have hx : memM x E := op_output_mem H.isOp2_times ha hb hab
  have hy : memM y E := op_output_mem H.isOp2_times ha hc hac
  obtain ⟨w, _, hxy, _⟩ := H.isOp2_plus x hx y hy
  have heq : t = w := H.distrib a ha b hb c hc s t x y w hbc has hab hac hxy
  rw [heq]
  exact hxy

/-- `x*0=0`, derived from distributivity and additive cancellation. -/
theorem mul_zero_right {x : M} (hx : memM x E) : app2 Mul x zero zero := by
  obtain ⟨z, hz, hxz, _⟩ := H.isOp2_times x hx zero H.zero_mem
  have hzz : app2 Add z z z :=
    graph_distrib H hx H.zero_mem H.zero_mem
      (H.ident_plus zero H.zero_mem) hxz hxz hxz
  have hz0 : z = zero :=
    add_cancel_left H hz H.zero_mem hz hzz (H.ident_plus z hz)
  simpa only [hz0] using hxz

theorem mul_zero_left {x : M} (hx : memM x E) : app2 Mul zero x zero :=
  H.comm_times x hx zero H.zero_mem zero (mul_zero_right H hx)

theorem mul_zero_right_eq {x z : M} (hx : memM x E)
    (h : app2 Mul x zero z) : z = zero :=
  op_output_unique H.isOp2_times hx H.zero_mem h (mul_zero_right H hx)

theorem mul_zero_left_eq {x z : M} (hx : memM x E)
    (h : app2 Mul zero x z) : z = zero :=
  op_output_unique H.isOp2_times H.zero_mem hx h (mul_zero_left H hx)

/-- Nonnegative factors have a nonnegative product: strict positivity handles
the nonzero case, and the proved zero laws handle the equality cases. -/
theorem mul_nonneg {a b c : M}
    (ha : memM a E) (hb : memM b E) (_hc : memM c E)
    (h0a : le Lt zero a) (h0b : le Lt zero b) (hmul : app2 Mul a b c) :
    le Lt zero c := by
  rcases h0a with h0a | h0a
  · rcases h0b with h0b | h0b
    · exact Or.inl (H.mulPos a ha b hb c h0a h0b hmul)
    · subst b
      exact Or.inr (mul_zero_right_eq H ha hmul).symm
  · subst a
    exact Or.inr (mul_zero_left_eq H hb hmul).symm

#print axioms op_output_mem
#print axioms op_output_unique
#print axioms le_refl
#print axioms le_total
#print axioms le_antisymm
#print axioms le_trans
#print axioms add_le_add_right
#print axioms add_le_add_left
#print axioms add_cancel_right
#print axioms add_cancel_left
#print axioms graph_assoc_plus
#print axioms graph_assoc_times
#print axioms graph_distrib
#print axioms mul_zero_right
#print axioms mul_zero_left
#print axioms mul_zero_right_eq
#print axioms mul_zero_left_eq
#print axioms mul_nonneg

end ClassicismZFC.SourceFieldAlgebra
