import StrongPossibilityConsequencesC
import Classicism.Syntax.FiniteChoiceBasis
import Classicism.Syntax.StrongPossibility
import Classicism.Syntax.Pure
import Classicism.Results.SentenceSchemas.PossibilityDistinctness

/-!
# Finite-proof reflection for Max, and the exact conditional SP diagram

Source: notes/sp-diagram-hat-audit.md §§2–3 and
notes/strong-possibility-degree.md §§2–4. The underlying Max reflection is
already reported in Bacon–Dorr, Classicism, 1 July 2022 draft §2.6 p.42.
The present finite-support derivation is the session proof (source id misc).

`maximalist_reflects` has NO consistency or model hypothesis. It extracts the
finite list of optional axioms from the actual derivation, discharges their
conjunction, proves its ordinary-possibility reflection, and necessitates only
the resulting C theorem. No optional axiom is necessitated.

The SP-diagram results keep Con(Max) as an explicit formal-library dependency
and Con(SP) as the genuinely open consistency hypothesis. They classify the
BoxNe diagram only; they do not assert an effective theoremhood complexity.
-/

namespace Classicism.Research.StrongPossibilityConsequences.Reflection

open Classicism.Research.StrongPossibilityConsequences

theorem dia_top_reflect : ◇ True → True := fun _ => True.intro

theorem dia_conj_reflect (p q : Prop) :
    (◇ p → p) → (◇ q → q) → ◇ (p ∧ q) → p ∧ q :=
  fun hp hq hd => ⟨hp (dia_and_left p q hd), hq (dia_and_right p q hd)⟩

theorem dia_reflect_compose (p q : Prop) :
    (◇ p → p) → (p → q) → ◇ p → q := fun hp hpq hd => hpq (hp hd)

theorem boxNe_witness (q p : Prop) : q → □ (◇ q → p) → P.BoxNe p :=
  fun hq hbox => ⟨q, hq, hbox⟩

theorem diaNe_ne {σ : Type} [Ty σ] (x y : σ) : P.DiaNe (x ≠ y) → x ≠ y :=
  diaNe_reflect _ (decidesNe_neg _ (decidesNe_eq x y))

theorem diaNe_not (p : Prop) : P.DiaNe (¬ p) → ¬ P.BoxNe p := by
  change (¬ P.BoxNe (¬ ¬ p)) → ¬ P.BoxNe p
  rw [not_not_eq]
  exact fun h => h

#classicism_check dia_top_reflect dia_conj_reflect dia_reflect_compose
  boxNe_witness diaNe_ne diaNe_not
#classicism_types dia_top_reflect dia_conj_reflect dia_reflect_compose
  boxNe_witness diaNe_ne diaNe_not
#classicism_derive dia_top_reflect dia_conj_reflect dia_reflect_compose
  boxNe_witness diaNe_ne diaNe_not

end Classicism.Research.StrongPossibilityConsequences.Reflection

namespace Classicism.Meta.Research.StrongPossibilityConsequences.Reflection

open AxiomSet
open Classicism.Research.StrongPossibilityConsequences.Reflection

variable {Sig : Signature}

def boxNe (p : Sentence Sig) : Sentence Sig :=
  Term.exists' (σ := Ty.t)
    (Term.conj Term.v0 (Term.box (Term.imp (Term.dia Term.v0) p.weaken)))

def conjunction : List (Sentence Sig) → Sentence Sig
  | [] => Term.top
  | a :: L => Term.conj a (conjunction L)

theorem conjunction_intro {Ax : AxiomSet Sig} :
    ∀ L : List (Sentence Sig), (∀ a ∈ L, Theorem Ax a) → Theorem Ax (conjunction L)
  | [], _ => Derivable.top
  | a :: L, h => Derivable.andI (h a (List.mem_cons_self))
      (conjunction_intro L (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem conjunction_elim {Ax : AxiomSet Sig} {Δ : List (Sentence Sig)} :
    ∀ L : List (Sentence Sig), Derivable Ax Δ (conjunction L) →
      ∀ a ∈ L, Derivable Ax Δ a
  | [], _, _, h => False.elim (List.not_mem_nil h)
  | b :: L, h, a, ha => by
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      exact Derivable.andE₁ h
    · exact conjunction_elim L (Derivable.andE₂ h) a ha

private theorem promote {p : Sentence Sig} (h : C.TheoremMinus p) : C.Theorem p :=
  Derivable.mono (fun _ ha => ha.elim) h

theorem conjunction_reflects : ∀ L : List (Sentence Sig),
    (∀ a ∈ L, C.Theorem (Term.imp (Term.dia a) a)) →
      C.Theorem (Term.imp (Term.dia (conjunction L)) (conjunction L))
  | [], _ => promote (C.TheoremMinus.ofPure dia_top_reflect.derivable)
  | a :: L, h =>
    Theorem.mp₂ (promote (Derivable.allE₂β
      (C.TheoremMinus.ofPure dia_conj_reflect.derivable) a (conjunction L)))
      (h a (List.mem_cons_self))
      (conjunction_reflects L (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem maximalist_axiom_reflects {a : Sentence Sig}
    (ha : (maximalist : AxiomSet Sig) a) : C.Theorem (Term.imp (Term.dia a) a) := by
  rcases ha with ha | ⟨_, σ, x, y, _, rfl⟩
  · exact ha.elim
  · exact promote (Derivable.allE₂β
      (C.TheoremMinus.ofPure (Classicism.dia_ne_imp_ne.derivable σ)) x y)

/-- Actual finite-proof persistence. No semantic completeness is used. -/
theorem maximalist_reflects {p : Sentence Sig}
    (hp : Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) p) :
    Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) (boxNe p) := by
  obtain ⟨L, hL, hd⟩ := FiniteChoiceBasis.finiteSupport hp
  have hconj : Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) (conjunction L) :=
    conjunction_intro L (fun a ha => Theorem.ax (hL a ha))
  have hcut : single (conjunction L) ⟹ FiniteChoiceBasis.ofList L := by
    intro a ha
    exact conjunction_elim L
      (Theorem.ax (Ax := single (conjunction L)) rfl) a ha
  have himp : C.Theorem (Term.imp (conjunction L) p) :=
    Theorem.deduction (fun h => h) (Derivable.cut hcut hd)
  have hreflect := conjunction_reflects L (fun a ha => maximalist_axiom_reflects (hL a ha))
  have hclosed : C.Theorem (Term.imp (Term.dia (conjunction L)) p) :=
    Theorem.mp₂ (promote (Derivable.allE₂β
      (C.TheoremMinus.ofPure dia_reflect_compose.derivable) (conjunction L) p))
      hreflect himp
  exact Theorem.mp₂ (Theorem.ofCMinus (Derivable.allE₂β
    (C.TheoremMinus.ofPure boxNe_witness.derivable) (conjunction L) p))
    hconj (Theorem.ofC (C.Theorem.nec hclosed))

theorem consistent_add_theorem {Ax : AxiomSet Sig} {p : Sentence Sig}
    (hcon : Consistent Ax) (hp : Theorem (C.axioms ∪ Ax) p) :
    Consistent (Ax ∪ single p) := by
  apply Consistent.of_entails (Ax₁ := Ax) ?_ hcon
  intro a ha
  rcases ha with ha | ha
  · exact Theorem.ax ha
  · change a = p at ha
    subst a
    exact hp

theorem diaNe_closedTypes {Γ : Ctx} (p : Formula Sig Γ) :
    (Term.diaNe p).closedTypes = p.closedTypes := by
  simp [Term.diaNe, Term.weaken, Term.closedTypes_rename]

/-- Con(Max) is known in the ordinary research, but still requires its
genuine-model implementation. It is not inferred from Con(SP). -/
theorem strongPossibility_entails_maximalist
    (hM : Consistent (maximalist : AxiomSet Sig)) :
    strongPossibility Sig ⟹ maximalist := by
  intro a ha
  rcases ha with ha | ⟨hc, σ, x, y, hn, rfl⟩
  · exact ha.elim
  · have hmax : (maximalist : AxiomSet Sig) (Term.neg (Term.eq' x y)) :=
      Or.inr ⟨hc, σ, x, y, hn, rfl⟩
    have hcon := consistent_add_theorem hM (Theorem.ax hmax)
    have hd : Theorem (C.axioms ∪ strongPossibility Sig)
        (Term.diaNe (Term.neg (Term.eq' x y))) :=
      Theorem.ax ⟨by rw [diaNe_closedTypes]; exact hc, _, hcon, rfl⟩
    exact Theorem.mp (Theorem.ofCMinus (Derivable.allE₂β
      (C.TheoremMinus.ofPure (diaNe_ne.derivable σ)) x y)) hd

theorem sp_reflects_maximalist (hM : Consistent (maximalist : AxiomSet Sig))
    {p : Sentence Sig} (hp : Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) p) :
    Theorem (C.axioms ∪ strongPossibility Sig) (boxNe p) :=
  Derivable.cut (strongPossibility_entails_maximalist hM) (maximalist_reflects hp)

/-- The negative half does not need Con(Max) or Con(SP). It constructs the
licensed D(not p) axiom directly from non-theoremhood and deduction. -/
theorem sp_refutes_boxNe_of_not_maximalist {p : Sentence Sig}
    (hc : p.closedTypes = true)
    (hn : ¬ Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) p) :
    Theorem (C.axioms ∪ strongPossibility Sig) (Term.neg (boxNe p)) := by
  have hd : Theorem (C.axioms ∪ strongPossibility Sig) (Term.diaNe (Term.neg p)) :=
    Theorem.ax ⟨by rw [diaNe_closedTypes]; simpa using hc,
      Term.neg p, consistent_neg_of_not_theorem hn, rfl⟩
  exact Theorem.mp (Theorem.ofCMinus (Derivable.allEβ
    (C.TheoremMinus.ofPure diaNe_not.derivable) p)) hd

theorem sp_boxNe_diagram (hM : Consistent (maximalist : AxiomSet Sig))
    (hSP : Consistent (strongPossibility Sig)) {p : Sentence Sig}
    (hc : p.closedTypes = true) :
    Theorem (C.axioms ∪ strongPossibility Sig) (boxNe p) ↔
      Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) p := by
  constructor
  · intro h
    classical
    apply Classical.byContradiction
    intro hn
    exact hSP (Derivable.notE h (sp_refutes_boxNe_of_not_maximalist hc hn))
  · exact sp_reflects_maximalist hM

theorem sp_not_boxNe_diagram (hM : Consistent (maximalist : AxiomSet Sig))
    (hSP : Consistent (strongPossibility Sig)) {p : Sentence Sig}
    (hc : p.closedTypes = true) :
    Theorem (C.axioms ∪ strongPossibility Sig) (Term.neg (boxNe p)) ↔
      ¬ Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) p :=
  ⟨fun hn hp => hSP (Derivable.notE (sp_reflects_maximalist hM hp) hn),
    sp_refutes_boxNe_of_not_maximalist hc⟩

#print axioms maximalist_reflects
#print axioms sp_boxNe_diagram
#print axioms sp_not_boxNe_diagram

end Classicism.Meta.Research.StrongPossibilityConsequences.Reflection
