import Classicism.Results.Research.FregeInfinity

/-!
# Addition and multiplication as internal relational graphs

Direct source: `research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md`,
§3 (unpaginated original research, `misc`). This is an explicit impredicative
implementation of the zero/successor recurrence argument used there.

The graphs are least admitted binary relations closed under their recurrences.
Their totality uses internal number induction; their functionality additionally
uses quantified Infinity through literal successor injectivity. There is no
external Nat recursion, choice of operations, or individual-output function.
-/

namespace Classicism.Research.FregeArithmeticGraphs

variable {σ : Type} [Ty σ]

/-- AddGraph a b c expresses a + b = c. -/
def AddGraph (a b c : (σ → Prop) → Prop) : Prop :=
  FiniteCardinality a ∧ FiniteCardinality b ∧ FiniteCardinality c ∧
    ∀ R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop,
      R (ZeroCard σ) a →
      (∀ i j, FiniteCardinality i → FiniteCardinality j →
        R i j → R (SucCard i) (SucCard j)) → R b c

theorem add_zero (a : (σ → Prop) → Prop) (ha : FiniteCardinality a) :
    AddGraph a (ZeroCard σ) a :=
  ⟨ha, finiteCardinality_zero, ha, fun _ hzero _ => hzero⟩

theorem add_suc (a b c : (σ → Prop) → Prop) (h : AddGraph a b c) :
    AddGraph a (SucCard b) (SucCard c) :=
  ⟨h.1, finiteCardinality_suc b h.2.1, finiteCardinality_suc c h.2.2.1,
    fun R hzero hstep => hstep b c h.2.1 h.2.2.1 (h.2.2.2 R hzero hstep)⟩

theorem add_total (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) : ∃ c, AddGraph a b c := by
  apply hb (fun i => ∃ j, AddGraph a i j)
  refine ⟨⟨a, add_zero a ha⟩, ?_⟩
  intro i hi
  obtain ⟨j, hij⟩ := hi
  exact ⟨SucCard j, add_suc a i j hij⟩

theorem add_cases (a b c : (σ → Prop) → Prop) (h : AddGraph a b c) :
    (b = ZeroCard σ ∧ c = a) ∨ ∃ i j,
      FiniteCardinality i ∧ FiniteCardinality j ∧ AddGraph a i j ∧
        b = SucCard i ∧ c = SucCard j := by
  have hstrong := h.2.2.2 (fun i j => AddGraph a i j ∧
    ((i = ZeroCard σ ∧ j = a) ∨ ∃ k l,
      FiniteCardinality k ∧ FiniteCardinality l ∧ AddGraph a k l ∧
        i = SucCard k ∧ j = SucCard l))
    ⟨add_zero a h.1, Or.inl ⟨rfl, rfl⟩⟩
    (fun i j hi hj hij => ⟨add_suc a i j hij.1,
      Or.inr ⟨i, j, hi, hj, hij.1, rfl, rfl⟩⟩)
  exact hstrong.2

theorem add_at_zero (a c : (σ → Prop) → Prop)
    (h : AddGraph a (ZeroCard σ) c) : c = a :=
  (add_cases a (ZeroCard σ) c h).elim And.right
    (fun hs => hs.elim fun i hi => hi.elim fun _ hij =>
      (frege_zero_ne_suc i hij.2.2.2.1).elim)

theorem add_at_suc (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c : (σ → Prop) → Prop) (hb : FiniteCardinality b)
    (h : AddGraph a (SucCard b) c) :
    ∃ d, FiniteCardinality d ∧ AddGraph a b d ∧ c = SucCard d := by
  apply (add_cases a (SucCard b) c h).elim
  · intro hz
    exact (frege_zero_ne_suc b hz.1.symm).elim
  · intro hs
    obtain ⟨i, j, hi, hj, hij, hbi, hcj⟩ := hs
    have he : b = i := frege_infinity_suc_injective hInf b i hb hi hbi
    exact ⟨j, hj, he.symm ▸ hij, hcj⟩

theorem add_functional (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b : (σ → Prop) → Prop) (hb : FiniteCardinality b) :
    ∀ c d, AddGraph a b c → AddGraph a b d → c = d := by
  refine (hb (fun i => FiniteCardinality i ∧
    ∀ c d, AddGraph a i c → AddGraph a i d → c = d) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, fun c d hc hd =>
      (add_at_zero a c hc).trans (add_at_zero a d hd).symm⟩
  · intro i hi
    refine ⟨finiteCardinality_suc i hi.1, ?_⟩
    intro c d hc hd
    obtain ⟨u, _, hau, hcu⟩ := add_at_suc hInf a i c hi.1 hc
    obtain ⟨v, _, hav, hdv⟩ := add_at_suc hInf a i d hi.1 hd
    exact hcu.trans ((congrArg SucCard (hi.2 u v hau hav)).trans hdv.symm)

/-- MulGraph a b c expresses a * b = c, with addition in the step rule. -/
def MulGraph (a b c : (σ → Prop) → Prop) : Prop :=
  FiniteCardinality a ∧ FiniteCardinality b ∧ FiniteCardinality c ∧
    ∀ R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop,
      R (ZeroCard σ) (ZeroCard σ) →
      (∀ i j k, FiniteCardinality i → FiniteCardinality j → FiniteCardinality k →
        R i j → AddGraph a j k → R (SucCard i) k) → R b c

theorem mul_zero (a : (σ → Prop) → Prop) (ha : FiniteCardinality a) :
    MulGraph a (ZeroCard σ) (ZeroCard σ) :=
  ⟨ha, finiteCardinality_zero, finiteCardinality_zero, fun _ hzero _ => hzero⟩

theorem mul_suc (a b c d : (σ → Prop) → Prop)
    (h : MulGraph a b c) (ha : AddGraph a c d) : MulGraph a (SucCard b) d :=
  ⟨h.1, finiteCardinality_suc b h.2.1, ha.2.2.1,
    fun R hzero hstep => hstep b c d h.2.1 h.2.2.1 ha.2.2.1
      (h.2.2.2 R hzero hstep) ha⟩

theorem mul_total (a b : (σ → Prop) → Prop) (ha : FiniteCardinality a)
    (hb : FiniteCardinality b) : ∃ c, MulGraph a b c := by
  apply hb (fun i => ∃ j, MulGraph a i j)
  refine ⟨⟨ZeroCard σ, mul_zero a ha⟩, ?_⟩
  intro i hi
  obtain ⟨j, hij⟩ := hi
  obtain ⟨k, hak⟩ := add_total a j ha hij.2.2.1
  exact ⟨k, mul_suc a i j k hij hak⟩

theorem mul_cases (a b c : (σ → Prop) → Prop) (h : MulGraph a b c) :
    (b = ZeroCard σ ∧ c = ZeroCard σ) ∨ ∃ i j,
      FiniteCardinality i ∧ FiniteCardinality j ∧ MulGraph a i j ∧
        b = SucCard i ∧ AddGraph a j c := by
  have hstrong := h.2.2.2 (fun i j => MulGraph a i j ∧
    ((i = ZeroCard σ ∧ j = ZeroCard σ) ∨ ∃ k l,
      FiniteCardinality k ∧ FiniteCardinality l ∧ MulGraph a k l ∧
        i = SucCard k ∧ AddGraph a l j))
    ⟨mul_zero a h.1, Or.inl ⟨rfl, rfl⟩⟩
    (fun i j k hi hj _ hij ha => ⟨mul_suc a i j k hij.1 ha,
      Or.inr ⟨i, j, hi, hj, hij.1, rfl, ha⟩⟩)
  exact hstrong.2

theorem mul_at_zero (a c : (σ → Prop) → Prop)
    (h : MulGraph a (ZeroCard σ) c) : c = ZeroCard σ :=
  (mul_cases a (ZeroCard σ) c h).elim And.right
    (fun hs => hs.elim fun i hi => hi.elim fun _ hij =>
      (frege_zero_ne_suc i hij.2.2.2.1).elim)

theorem mul_at_suc (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b c : (σ → Prop) → Prop) (hb : FiniteCardinality b)
    (h : MulGraph a (SucCard b) c) :
    ∃ d, FiniteCardinality d ∧ MulGraph a b d ∧ AddGraph a d c := by
  apply (mul_cases a (SucCard b) c h).elim
  · intro hz
    exact (frege_zero_ne_suc b hz.1.symm).elim
  · intro hs
    obtain ⟨i, j, hi, hj, hij, hbi, haj⟩ := hs
    have he : b = i := frege_infinity_suc_injective hInf b i hb hi hbi
    exact ⟨j, hj, he.symm ▸ hij, haj⟩

theorem mul_functional (hInf : Classicism.P.AxiomOfInfinity σ)
    (a b : (σ → Prop) → Prop) (hb : FiniteCardinality b) :
    ∀ c d, MulGraph a b c → MulGraph a b d → c = d := by
  refine (hb (fun i => FiniteCardinality i ∧
    ∀ c d, MulGraph a i c → MulGraph a i d → c = d) ⟨?_, ?_⟩).2
  · exact ⟨finiteCardinality_zero, fun c d hc hd =>
      (mul_at_zero a c hc).trans (mul_at_zero a d hd).symm⟩
  · intro i hi
    refine ⟨finiteCardinality_suc i hi.1, ?_⟩
    intro c d hc hd
    obtain ⟨u, hu, hmu, hac⟩ := mul_at_suc hInf a i c hi.1 hc
    obtain ⟨v, _, hmv, had⟩ := mul_at_suc hInf a i d hi.1 hd
    have he : u = v := hi.2 u v hmu hmv
    exact add_functional hInf a u hu c d hac (he.symm ▸ had)

end Classicism.Research.FregeArithmeticGraphs
