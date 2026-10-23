import Classicism.Results.Research.CrossBaseArithmetic
import Classicism.Certified.Arithmetic

/-!
# The arithmetic graphs agree with the repository's existing arithmetic vocabulary

Direct source: relational-coding-recursion-20261022.md §34.2 and
infinity-core-number-isomorphism.md §3, under research/2026-10-22/notes and
proof-refinements respectively (unpaginated original research, misc).

The old Sum/Prod definitions omit outer number guards. This module proves the
exact comparison ON NUMBERS; it does not silently identify the predicates away
from that field. The existing definitions and generated statements are untouched.
-/

namespace Classicism.Research.FregeArithmeticVocabulary
open Classicism.Research.FregeArithmeticGraphs
open Classicism.Research.FregeNoncollapse
open Classicism.Research.CrossBaseArithmetic

variable {σ ρ : Type} [Ty σ] [Ty ρ]

theorem addGraph_iff_sum (a b c : (σ → Prop) → Prop)
    (ha : FiniteCardinality a) (hb : FiniteCardinality b) (hc : FiniteCardinality c) :
    AddGraph a b c ↔ Arith.Sum σ a b c :=
  ⟨fun h => h.2.2.2, fun h => ⟨ha, hb, hc, h⟩⟩

theorem mulGraph_iff_prod (a b c : (σ → Prop) → Prop)
    (ha : FiniteCardinality a) (hb : FiniteCardinality b) (hc : FiniteCardinality c) :
    MulGraph a b c ↔ Arith.Prod σ a b c := by
  constructor
  · intro h R hz hs
    exact h.2.2.2 R hz (fun i j k hi hj hk hij hadd =>
      hs i j k hi hj hk hij hadd.2.2.2)
  · intro h
    refine ⟨ha, hb, hc, ?_⟩
    intro R hz hs
    exact h R hz (fun i j k hi hj hk hij hsum =>
      hs i j k hi hj hk hij ⟨ha, hj, hk, hsum⟩)

theorem sum_cross_base (hσ : Noncollapse σ) (hρ : Noncollapse ρ)
    (a b c : (σ → Prop) → Prop) (A B C : (ρ → Prop) → Prop)
    (ha : Synch a A) (hb : Synch b B) (hc : Synch c C) :
    Arith.Sum σ a b c ↔ Arith.Sum ρ A B C :=
  ((addGraph_iff_sum a b c (synch_numbers a A ha).1
      (synch_numbers b B hb).1 (synch_numbers c C hc).1).symm.trans
    (addition_iff hσ hρ a b c A B C ha hb hc)).trans
    (addGraph_iff_sum A B C (synch_numbers a A ha).2
      (synch_numbers b B hb).2 (synch_numbers c C hc).2)

theorem prod_cross_base (hσ : Noncollapse σ) (hρ : Noncollapse ρ)
    (a b c : (σ → Prop) → Prop) (A B C : (ρ → Prop) → Prop)
    (ha : Synch a A) (hb : Synch b B) (hc : Synch c C) :
    Arith.Prod σ a b c ↔ Arith.Prod ρ A B C :=
  ((mulGraph_iff_prod a b c (synch_numbers a A ha).1
      (synch_numbers b B hb).1 (synch_numbers c C hc).1).symm.trans
    (multiplication_iff hσ hρ a b c A B C ha hb hc)).trans
    (mulGraph_iff_prod A B C (synch_numbers a A ha).2
      (synch_numbers b B hb).2 (synch_numbers c C hc).2)

theorem equality_cross_base (hσ : Noncollapse σ) (hρ : Noncollapse ρ)
    (a b : (σ → Prop) → Prop) (A B : (ρ → Prop) → Prop)
    (ha : Synch a A) (hb : Synch b B) : a = b ↔ A = B := by
  constructor
  · intro he
    exact synch_functional hσ b (synch_numbers b B hb).1 A B (he ▸ ha) hb
  · intro he
    exact synch_injective hρ a b B (he ▸ ha) hb

end Classicism.Research.FregeArithmeticVocabulary
