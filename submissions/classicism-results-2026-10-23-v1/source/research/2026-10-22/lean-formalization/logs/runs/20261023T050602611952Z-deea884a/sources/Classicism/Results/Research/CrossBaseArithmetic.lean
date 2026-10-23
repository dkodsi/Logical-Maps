import Classicism.Results.Research.FregeNoncollapse
import Classicism.Results.Research.FregeArithmeticGraphs

/-!
# The canonical synchronized-successor graph between counting bases

Direct source: `research/2026-10-22/notes/relational-coding-recursion-20261022.md`,
§34.1–§34.2 (unpaginated original research, `misc`).

Source arithmetic noncollapse makes this a surjective function GRAPH, even when
the target arithmetic collapses. Both noncollapse premises give a graph bijection
and arithmetic agreement. No operation realizing the graph is selected, no actual
quantified Infinity is substituted for noncollapse, and no graph identity follows
merely from current coextension. The Max operational obstruction is owned separately.
-/

namespace Classicism.Research.CrossBaseArithmetic
open Classicism.Research.FregeNoncollapse
open Classicism.Research.FregeArithmeticGraphs

variable {σ ρ : Type} [Ty σ] [Ty ρ]

def Synch (x : (σ → Prop) → Prop) (y : (ρ → Prop) → Prop) : Prop :=
  ∀ R : ((σ → Prop) → Prop) → ((ρ → Prop) → Prop) → Prop,
    R (ZeroCard σ) (ZeroCard ρ) →
      (∀ u v, R u v → R (SucCard u) (SucCard v)) → R x y

theorem synch_zero : Synch (ZeroCard σ) (ZeroCard ρ) := fun _ hz _ => hz

theorem synch_suc (x : (σ → Prop) → Prop) (y : (ρ → Prop) → Prop)
    (h : Synch x y) : Synch (SucCard x) (SucCard y) :=
  fun R hz hs => hs x y (h R hz hs)

theorem synch_numbers (x : (σ → Prop) → Prop) (y : (ρ → Prop) → Prop)
    (h : Synch x y) : FiniteCardinality x ∧ FiniteCardinality y :=
  h (fun u v => FiniteCardinality u ∧ FiniteCardinality v)
    ⟨finiteCardinality_zero, finiteCardinality_zero⟩
    (fun u v huv => ⟨finiteCardinality_suc u huv.1, finiteCardinality_suc v huv.2⟩)

theorem synch_symm (x : (σ → Prop) → Prop) (y : (ρ → Prop) → Prop)
    (h : Synch x y) : Synch y x :=
  h (fun u v => Synch v u) synch_zero (fun u v huv => synch_suc v u huv)

theorem synch_unfold (x : (σ → Prop) → Prop) (y : (ρ → Prop) → Prop) :
    Synch x y ↔ (x = ZeroCard σ ∧ y = ZeroCard ρ) ∨
      ∃ u v, Synch u v ∧ x = SucCard u ∧ y = SucCard v := by
  constructor
  · intro h
    have hs := h (fun u v => Synch u v ∧
      ((u = ZeroCard σ ∧ v = ZeroCard ρ) ∨
        ∃ a b, Synch a b ∧ u = SucCard a ∧ v = SucCard b))
      ⟨synch_zero, Or.inl ⟨rfl, rfl⟩⟩
      (fun u v huv => ⟨synch_suc u v huv.1, Or.inr ⟨u, v, huv.1, rfl, rfl⟩⟩)
    exact hs.2
  · intro h
    apply h.elim
    · intro hz
      exact hz.2.symm ▸ (hz.1.symm ▸ synch_zero)
    · intro hs
      obtain ⟨u, v, huv, hx, hy⟩ := hs
      exact hy.symm ▸ (hx.symm ▸ synch_suc u v huv)

theorem synch_total (x : (σ → Prop) → Prop) (hx : FiniteCardinality x) :
    ∃ y : (ρ → Prop) → Prop, Synch x y := by
  apply hx (fun u => ∃ v : (ρ → Prop) → Prop, Synch u v)
  constructor
  · exact ⟨ZeroCard ρ, synch_zero⟩
  · intro u hu
    obtain ⟨v, huv⟩ := hu
    exact ⟨SucCard v, synch_suc u v huv⟩

theorem synch_onto (y : (ρ → Prop) → Prop) (hy : FiniteCardinality y) :
    ∃ x : (σ → Prop) → Prop, Synch x y := by
  obtain ⟨x, hyx⟩ := synch_total (ρ := σ) y hy
  exact ⟨x, synch_symm y x hyx⟩

theorem synch_at_zero (y : (ρ → Prop) → Prop)
    (h : Synch (ZeroCard σ) y) : y = ZeroCard ρ := by
  apply ((synch_unfold (ZeroCard σ) y).1 h).elim
  · exact And.right
  · intro hs
    obtain ⟨u, v, _, hu, _⟩ := hs
    exact (frege_zero_ne_suc u hu).elim

theorem synch_at_suc (hNC : Noncollapse σ)
    (x : (σ → Prop) → Prop) (y : (ρ → Prop) → Prop)
    (hx : FiniteCardinality x) (h : Synch (SucCard x) y) :
    ∃ v, Synch x v ∧ y = SucCard v := by
  apply ((synch_unfold (SucCard x) y).1 h).elim
  · intro hz
    exact (frege_zero_ne_suc x hz.1.symm).elim
  · intro hs
    obtain ⟨u, v, huv, hu, hv⟩ := hs
    have he : x = u := hNC x u hx (synch_numbers u v huv).1 hu
    exact ⟨v, he.symm ▸ huv, hv⟩

theorem synch_functional (hNC : Noncollapse σ)
    (x : (σ → Prop) → Prop) (hx : FiniteCardinality x) :
    ∀ y z : (ρ → Prop) → Prop, Synch x y → Synch x z → y = z := by
  refine (hx (fun u => FiniteCardinality u ∧ ∀ y z : (ρ → Prop) → Prop,
    Synch u y → Synch u z → y = z) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, fun y z hy hz =>
      (synch_at_zero y hy).trans (synch_at_zero z hz).symm⟩
  · intro u hu
    refine ⟨finiteCardinality_suc u hu.1, ?_⟩
    intro y z hy hz
    obtain ⟨v, huv, hyv⟩ := synch_at_suc hNC u y hu.1 hy
    obtain ⟨w, huw, hzw⟩ := synch_at_suc hNC u z hu.1 hz
    exact hyv.trans ((congrArg SucCard (hu.2 v w huv huw)).trans hzw.symm)

theorem synch_injective (hNC : Noncollapse ρ)
    (x z : (σ → Prop) → Prop) (y : (ρ → Prop) → Prop)
    (hxy : Synch x y) (hzy : Synch z y) : x = z :=
  synch_functional hNC y (synch_numbers x y hxy).2 x z
    (synch_symm x y hxy) (synch_symm z y hzy)

/-- This conclusion asserts totality, onto and both graph uniqueness clauses. -/
theorem synch_bijection (hσ : Noncollapse σ) (hρ : Noncollapse ρ) :
    (∀ x : (σ → Prop) → Prop, FiniteCardinality x →
      ∃ y : (ρ → Prop) → Prop, Synch x y) ∧
    (∀ y : (ρ → Prop) → Prop, FiniteCardinality y →
      ∃ x : (σ → Prop) → Prop, Synch x y) ∧
    (∀ x y z, Synch (σ := σ) (ρ := ρ) x y → Synch x z → y = z) ∧
    (∀ x z y, Synch (σ := σ) (ρ := ρ) x y → Synch z y → x = z) :=
  ⟨synch_total, synch_onto,
    (fun x y z hy hz => synch_functional hσ x (synch_numbers x y hy).1 y z hy hz),
    synch_injective hρ⟩

theorem synch_unique_graph
    (R : ((σ → Prop) → Prop) → ((ρ → Prop) → Prop) → Prop)
    (hz : R (ZeroCard σ) (ZeroCard ρ))
    (hs : ∀ x y, R x y → R (SucCard x) (SucCard y))
    (hnum : ∀ x y, R x y → FiniteCardinality x)
    (hfun : ∀ x y z, R x y → R x z → y = z) :
    ∀ x y, R x y ↔ Synch x y := by
  intro x y
  constructor
  · intro hxy
    obtain ⟨z, hxz⟩ := synch_total (ρ := ρ) x (hnum x y hxy)
    have he : y = z := hfun x y z hxy (hxz R hz hs)
    exact he.symm ▸ hxz
  · intro hxy
    exact hxy R hz hs

/-- Source noncollapse suffices for the homomorphism into possibly collapsed arithmetic. -/
theorem addition_forward (hNC : Noncollapse σ)
    (a b c : (σ → Prop) → Prop) (A B C : (ρ → Prop) → Prop)
    (hadd : AddGraph a b c) (ha : Synch a A) (hb : Synch b B) (hc : Synch c C) :
    AddGraph A B C := by
  have hlift : ∀ I J : (ρ → Prop) → Prop,
      Synch b I → Synch c J → AddGraph A I J := by
    apply hadd.2.2.2 (fun i j => ∀ I J : (ρ → Prop) → Prop,
      Synch i I → Synch j J → AddGraph A I J)
    · intro I J hI hJ
      have heI : I = ZeroCard ρ := synch_at_zero I hI
      have heJ : J = A := synch_functional hNC a hadd.1 J A hJ ha
      exact heJ.symm ▸ (heI.symm ▸ add_zero A (synch_numbers a A ha).2)
    · intro i j hi hj hij I J hI hJ
      obtain ⟨U, hiU, hIU⟩ := synch_at_suc hNC i I hi hI
      obtain ⟨V, hjV, hJV⟩ := synch_at_suc hNC j J hj hJ
      exact hJV.symm ▸ (hIU.symm ▸ add_suc A U V (hij U V hiU hjV))
  exact hlift B C hb hc

theorem addition_iff (hσ : Noncollapse σ) (hρ : Noncollapse ρ)
    (a b c : (σ → Prop) → Prop) (A B C : (ρ → Prop) → Prop)
    (ha : Synch a A) (hb : Synch b B) (hc : Synch c C) :
    AddGraph a b c ↔ AddGraph A B C :=
  ⟨fun h => addition_forward hσ a b c A B C h ha hb hc,
    fun h => addition_forward hρ A B C a b c h
      (synch_symm a A ha) (synch_symm b B hb) (synch_symm c C hc)⟩

theorem multiplication_forward (hNC : Noncollapse σ)
    (a b c : (σ → Prop) → Prop) (A B C : (ρ → Prop) → Prop)
    (hmul : MulGraph a b c) (ha : Synch a A) (hb : Synch b B) (hc : Synch c C) :
    MulGraph A B C := by
  have hlift : ∀ I J : (ρ → Prop) → Prop,
      Synch b I → Synch c J → MulGraph A I J := by
    apply hmul.2.2.2 (fun i j => ∀ I J : (ρ → Prop) → Prop,
      Synch i I → Synch j J → MulGraph A I J)
    · intro I J hI hJ
      exact (synch_at_zero J hJ).symm ▸ ((synch_at_zero I hI).symm ▸
        mul_zero A (synch_numbers a A ha).2)
    · intro i j k hi hj hk hij hadd I K hI hK
      obtain ⟨U, hiU, hIU⟩ := synch_at_suc hNC i I hi hI
      obtain ⟨V, hjV⟩ := synch_total (ρ := ρ) j hj
      have hAVK : AddGraph A V K := addition_forward hNC a j k A V K hadd ha hjV hK
      exact hIU.symm ▸ mul_suc A U V K (hij U V hiU hjV) hAVK
  exact hlift B C hb hc

theorem multiplication_iff (hσ : Noncollapse σ) (hρ : Noncollapse ρ)
    (a b c : (σ → Prop) → Prop) (A B C : (ρ → Prop) → Prop)
    (ha : Synch a A) (hb : Synch b B) (hc : Synch c C) :
    MulGraph a b c ↔ MulGraph A B C :=
  ⟨fun h => multiplication_forward hσ a b c A B C h ha hb hc,
    fun h => multiplication_forward hρ A B C a b c h
      (synch_symm a A ha) (synch_symm b B hb) (synch_symm c C hc)⟩

end Classicism.Research.CrossBaseArithmetic
