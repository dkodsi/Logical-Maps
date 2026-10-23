import Classicism.Results.Research.FregeArithmeticGraphs

/-!
# Internal additive arithmetic and numerical order for rational coding

Concrete C theorems about the submitted Frege AddGraph. This is internal Frege
induction, not Lean Nat induction or an assumed semiring interface. Quantified
Infinity is retained exactly where successor cancellation/functionality is used.
The code type is (σt)t, so every displayed operation/relation has an allowed type.

Source: arithmetic resource in proof-refinements/choice-free-faithful-probability.md
and infinity-core-number-isomorphism.md, section 3 (unpaginated). The detailed
graph proofs below are new formalization work by OpenAI Codex, 22 October 2026.
-/

namespace Classicism.Research.ProbabilityNaturalOrder
open Classicism.Research.FregeArithmeticGraphs

variable {σ : Type} [Ty σ]

theorem add_zero_left (b : (σ → Prop) → Prop) (hb : FiniteCardinality b) :
    AddGraph (ZeroCard σ) b b := by
  refine (hb (fun n => FiniteCardinality n ∧ AddGraph (ZeroCard σ) n n) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, add_zero (ZeroCard σ) finiteCardinality_zero⟩
  · intro n hn
    exact ⟨finiteCardinality_suc n hn.1, add_suc (ZeroCard σ) n n hn.2⟩

theorem add_suc_left (a b c : (σ → Prop) → Prop) (h : AddGraph a b c) :
    AddGraph (SucCard a) b (SucCard c) :=
  h.2.2.2 (fun i j => AddGraph (SucCard a) i (SucCard j))
    (add_zero (SucCard a) (finiteCardinality_suc a h.1))
    (fun i j _ _ hij => add_suc (SucCard a) i (SucCard j) hij)

theorem add_comm (a b c : (σ → Prop) → Prop) (h : AddGraph a b c) : AddGraph b a c :=
  h.2.2.2 (fun i j => AddGraph i a j) (add_zero_left a h.1)
    (fun i j _ _ hij => add_suc_left i a j hij)

theorem add_assoc_forward (a b c u v : (σ → Prop) → Prop)
    (hab : AddGraph a b u) (huc : AddGraph u c v) :
    ∃ t, AddGraph b c t ∧ AddGraph a t v :=
  huc.2.2.2 (fun i j => ∃ t, AddGraph b i t ∧ AddGraph a t j)
    ⟨b, add_zero b hab.2.1, hab⟩
    (fun i j _ _ hij => hij.elim fun t ht =>
      ⟨SucCard t, add_suc b i t ht.1, add_suc a t j ht.2⟩)

theorem add_assoc_reverse (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c t v : (σ → Prop) → Prop)
    (hbc : AddGraph b c t) (hat : AddGraph a t v) :
    ∃ u, AddGraph a b u ∧ AddGraph u c v := by
  obtain ⟨u, hab⟩ := add_total a b hat.1 hbc.1
  obtain ⟨v', huv⟩ := add_total u c hab.2.2.1 hbc.2.1
  obtain ⟨t', hbt, hat'⟩ := add_assoc_forward a b c u v' hab huv
  have htt : t' = t := add_functional hInf b c hbc.2.1 t' t hbt hbc
  have hvv : v' = v := add_functional hInf a t hat.2.1 v' v (htt ▸ hat') hat
  exact ⟨u, hab, hvv ▸ huv⟩

theorem add_cancel_right (hInf : Classicism.P.AxiomOfInfinity σ)
    (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    ∀ a b c, AddGraph a n c → AddGraph b n c → a = b := by
  refine (hn (fun i => FiniteCardinality i ∧
    ∀ a b c, AddGraph a i c → AddGraph b i c → a = b) ⟨?_, ?_⟩).2
  · refine ⟨finiteCardinality_zero, ?_⟩
    intro a b c ha hb
    exact (add_at_zero a c ha).symm.trans (add_at_zero b c hb)
  · intro i hi
    refine ⟨finiteCardinality_suc i hi.1, ?_⟩
    intro a b c ha hb
    obtain ⟨u, hu, hau, hcu⟩ := add_at_suc hInf a i c hi.1 ha
    obtain ⟨v, hv, hbv, hcv⟩ := add_at_suc hInf b i c hi.1 hb
    have huv := frege_infinity_suc_injective hInf u v hu hv (hcu.symm.trans hcv)
    exact hi.2 a b u hau (huv.symm ▸ hbv)

theorem add_cancel_left (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c d : (σ → Prop) → Prop) (hab : AddGraph a b d) (hac : AddGraph a c d) :
    b = c := add_cancel_right hInf a hab.1 b c d (add_comm a b d hab) (add_comm a c d hac)

theorem add_eq_zero (a b : (σ → Prop) → Prop) (h : AddGraph a b (ZeroCard σ)) :
    a = ZeroCard σ ∧ b = ZeroCard σ := by
  cases add_cases a b (ZeroCard σ) h with
  | inl hz => exact ⟨hz.2.symm, hz.1⟩
  | inr hs =>
    obtain ⟨i, j, hi, hj, hij, hbi, hz⟩ := hs
    exact False.elim (frege_zero_ne_suc j hz)

theorem number_cases (n : (σ → Prop) → Prop) (hn : FiniteCardinality n) :
    n = ZeroCard σ ∨ ∃ i, FiniteCardinality i ∧ n = SucCard i := by
  refine (hn (fun i => FiniteCardinality i ∧
    (i = ZeroCard σ ∨ ∃ j, FiniteCardinality j ∧ i = SucCard j)) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, Or.inl rfl⟩
  · intro i hi
    exact ⟨finiteCardinality_suc i hi.1, Or.inr ⟨i, hi.1, rfl⟩⟩

def LE (a b : (σ → Prop) → Prop) : Prop := ∃ c, AddGraph a c b

def LT (a b : (σ → Prop) → Prop) : Prop := LE (SucCard a) b

theorem le_refl (a : (σ → Prop) → Prop) (ha : FiniteCardinality a) : LE a a :=
  ⟨ZeroCard σ, add_zero a ha⟩

theorem zero_le (a : (σ → Prop) → Prop) (ha : FiniteCardinality a) : LE (ZeroCard σ) a :=
  ⟨a, add_zero_left a ha⟩

theorem le_fields (a b : (σ → Prop) → Prop) (h : LE a b) :
    FiniteCardinality a ∧ FiniteCardinality b :=
  h.elim (fun c hc => ⟨hc.1, hc.2.2.1⟩)

theorem le_zero (a : (σ → Prop) → Prop) (h : LE a (ZeroCard σ)) : a = ZeroCard σ :=
  h.elim (fun b hb => (add_eq_zero a b hb).1)

theorem le_suc (a b : (σ → Prop) → Prop) (h : LE a b) : LE (SucCard a) (SucCard b) :=
  h.elim (fun c hc => ⟨c, add_suc_left a c b hc⟩)

theorem le_of_suc_le (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a) (hb : FiniteCardinality b)
    (h : LE (SucCard a) (SucCard b)) : LE a b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd, hcad, hbd⟩ :=
    add_at_suc hInf c a (SucCard b) ha (add_comm (SucCard a) c (SucCard b) hc)
  have he : b = d := frege_infinity_suc_injective hInf b d hb hd hbd
  exact ⟨c, he.symm ▸ add_comm c a d hcad⟩

theorem le_trans (a b c : (σ → Prop) → Prop) (hab : LE a b) (hbc : LE b c) : LE a c := by
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hbc
  obtain ⟨k, hk, hak⟩ := add_assoc_forward a i j b c hi hj
  exact ⟨k, hak⟩

theorem le_total (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) : LE a b ∨ LE b a := by
  refine (ha (fun i => FiniteCardinality i ∧
    ∀ j, FiniteCardinality j → LE i j ∨ LE j i) ⟨?_, ?_⟩).2 b hb
  · exact ⟨finiteCardinality_zero, fun j hj => Or.inl (zero_le j hj)⟩
  · intro i hi
    refine ⟨finiteCardinality_suc i hi.1, ?_⟩
    intro j hj
    cases number_cases j hj with
    | inl hj0 => exact Or.inr (hj0.symm ▸ zero_le (SucCard i) (finiteCardinality_suc i hi.1))
    | inr hs =>
      obtain ⟨k, hk, hjk⟩ := hs
      exact (hi.2 k hk).elim
        (fun h => Or.inl (hjk.symm ▸ le_suc i k h))
        (fun h => Or.inr (hjk.symm ▸ le_suc k i h))

theorem le_antisymm (hInf : Classicism.P.AxiomOfInfinity σ)
    (a : (σ → Prop) → Prop) (ha : FiniteCardinality a) :
    ∀ b, FiniteCardinality b → LE a b → LE b a → a = b := by
  refine (ha (fun i => FiniteCardinality i ∧ ∀ j, FiniteCardinality j →
    LE i j → LE j i → i = j) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, fun j _ _ hj => (le_zero j hj).symm⟩
  · intro i hi
    refine ⟨finiteCardinality_suc i hi.1, ?_⟩
    intro j hj hij hji
    cases number_cases j hj with
    | inl hj0 =>
      have hz : SucCard i = ZeroCard σ := le_zero (SucCard i) (hj0 ▸ hij)
      exact False.elim (frege_zero_ne_suc i hz.symm)
    | inr hs =>
      obtain ⟨k, hk, hjk⟩ := hs
      have hik := le_of_suc_le hInf i k hi.1 hk (hjk ▸ hij)
      have hki := le_of_suc_le hInf k i hk hi.1 (hjk ▸ hji)
      exact (congrArg SucCard (hi.2 k hk hik hki)).trans hjk.symm

theorem not_suc_le_self (hInf : Classicism.P.AxiomOfInfinity σ)
    (a : (σ → Prop) → Prop) (ha : FiniteCardinality a) : ¬ LE (SucCard a) a := by
  refine (ha (fun i => FiniteCardinality i ∧ ¬ LE (SucCard i) i) ⟨?_, ?_⟩).2
  · refine ⟨finiteCardinality_zero, ?_⟩
    intro h
    exact frege_zero_ne_suc (ZeroCard σ) (le_zero _ h).symm
  · intro i hi
    refine ⟨finiteCardinality_suc i hi.1, ?_⟩
    intro h
    exact hi.2 (le_of_suc_le hInf (SucCard i) i (finiteCardinality_suc i hi.1) hi.1 h)

end Classicism.Research.ProbabilityNaturalOrder
