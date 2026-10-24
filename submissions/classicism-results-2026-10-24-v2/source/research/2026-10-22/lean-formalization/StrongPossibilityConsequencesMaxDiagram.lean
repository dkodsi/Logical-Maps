import Classicism.Syntax.SentenceSchemas

/-!
# The exact identity diagram above Max and stabilization of distinctness

Ordinary metalogic, with actual derivations in the existing C calculus.
Sources: research/2026-10-22/notes/max-degree.md §§4, 11, 13.3;
comparison-handoff-20261022.md §7 (session deductions, source id misc).

This proves the unconditional implication for EVERY consistent extension of
Max: it adds no closed-type identity to C, decides every finite Boolean
combination of such identities, and recomputing relative distinctness gives
exactly the original schema. It does not assume the desired identity-diagram
conclusion, a standard arithmetic model, a coding theorem, or SP consistency.
No effective complexity classification is claimed without its coding bridge.
-/

namespace Classicism.Meta.Research.StrongPossibilityConsequences.MaxDiagram

open AxiomSet

variable {Sig : Signature}

/-- A consistent theory entailing Max has exactly C's closed-type identities. -/
theorem identity_iff {Ax : AxiomSet Sig} (hcon : Consistent Ax)
    (hmax : Ax ⟹ maximalist) {σ : Ty} (x y : Term Sig [] σ)
    (hc : (Term.eq' x y).closedTypes = true) :
    Theorem (C.axioms ∪ Ax) (Term.eq' x y) ↔ C.Theorem (Term.eq' x y) := by
  constructor
  · intro he
    classical
    apply Classical.byContradiction
    intro hn
    have hn' : ¬ Theorem (C.axioms ∪ (empty : AxiomSet Sig)) (Term.eq' x y) :=
      fun h => hn (Derivable.mono (fun _ ha => ha.elim id False.elim) h)
    have hd := hmax _ (Or.inr (distinctness_mem hc hn'))
    exact hcon (Derivable.notE he hd)
  · exact Theorem.ofC

/-- Relative distinctness stabilizes above original Max. This is equality of
the actual axiom predicates, including their closed-type restriction. -/
theorem distinctness_eq {Ax : AxiomSet Sig} (hcon : Consistent Ax)
    (hmax : Ax ⟹ maximalist) : distinctness Ax = distinctness (empty : AxiomSet Sig) := by
  funext a
  apply propext
  constructor
  · rintro ⟨hc, σ, x, y, hn, rfl⟩
    refine ⟨hc, σ, x, y, ?_, rfl⟩
    intro h
    exact hn (Theorem.ofC (Derivable.mono (fun _ ha => ha.elim id False.elim) h))
  · rintro ⟨hc, σ, x, y, hn, rfl⟩
    refine ⟨hc, σ, x, y, ?_, rfl⟩
    intro h
    exact hn (Theorem.ofC ((identity_iff hcon hmax x y (by simpa using hc)).mp h))

/-- Re-maximalizing adds no consequences to a consistent extension of Max. -/
theorem entails_max {Ax : AxiomSet Sig} (hcon : Consistent Ax)
    (hmax : Ax ⟹ maximalist) : Ax ⟹ max Ax := by
  intro a ha
  rcases ha with ha | ha
  · exact Theorem.ax ha
  · rw [distinctness_eq hcon hmax] at ha
    exact hmax a (Or.inr ha)

theorem max_theorem_iff {Ax : AxiomSet Sig} (hcon : Consistent Ax)
    (hmax : Ax ⟹ maximalist) (p : Sentence Sig) :
    Theorem (C.axioms ∪ max Ax) p ↔ Theorem (C.axioms ∪ Ax) p :=
  ⟨Derivable.cut (entails_max hcon hmax),
    Derivable.mono (fun _ ha => ha.elim Or.inl (fun h => Or.inr (Or.inl h)))⟩

theorem max_consistent {Ax : AxiomSet Sig} (hcon : Consistent Ax)
    (hmax : Ax ⟹ maximalist) : Consistent (max Ax) :=
  Consistent.of_entails (entails_max hcon hmax) hcon

/-- A typed closed identity in the paper's language. -/
structure ClosedIdentity (Sig : Signature) where
  ty : Ty
  left : Term Sig [] ty
  right : Term Sig [] ty
  closed : (Term.eq' left right).closedTypes = true

def ClosedIdentity.formula (i : ClosedIdentity Sig) : Sentence Sig :=
  Term.eq' i.left i.right

/-- Finitary Boolean combinations only. Implication and iff can be expressed
with these constructors; there is no infinitary conjunction here. -/
inductive IdentityBoolean (Sig : Signature) where
  | atom : ClosedIdentity Sig → IdentityBoolean Sig
  | neg : IdentityBoolean Sig → IdentityBoolean Sig
  | conj : IdentityBoolean Sig → IdentityBoolean Sig → IdentityBoolean Sig
  | disj : IdentityBoolean Sig → IdentityBoolean Sig → IdentityBoolean Sig

def IdentityBoolean.formula : IdentityBoolean Sig → Sentence Sig
  | .atom i => i.formula
  | .neg b => Term.neg b.formula
  | .conj b c => Term.conj b.formula c.formula
  | .disj b c => Term.disj b.formula c.formula

/-- The finite truth table whose atomic answers are C theoremhood. This is
not asserted computable: effective coding/reducibility is a separate task. -/
def IdentityBoolean.truth : IdentityBoolean Sig → Prop
  | .atom i => C.Theorem i.formula
  | .neg b => ¬ b.truth
  | .conj b c => b.truth ∧ c.truth
  | .disj b c => b.truth ∨ c.truth

theorem IdentityBoolean.closedTypes (b : IdentityBoolean Sig) :
    b.formula.closedTypes = true := by
  induction b with
  | atom i => exact i.closed
  | neg b ih => simpa [formula] using ih
  | conj b c ihb ihc => simp [formula, ihb, ihc]
  | disj b c ihb ihc => simp [formula, ihb, ihc]

/-- Max proves the truth-table answer, and proves its negation when false.
This is a structural induction constructing derivations, not an assumption
that a completion decides the formula. It does not require Con(Max). -/
theorem IdentityBoolean.decides (b : IdentityBoolean Sig) :
    (b.truth → Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) b.formula) ∧
    (¬ b.truth → Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) (Term.neg b.formula)) := by
  classical
  induction b with
  | atom i =>
    constructor
    · exact Theorem.ofC
    · intro hn
      exact Theorem.ax (Or.inr (distinctness_mem i.closed
        (fun h => hn (Derivable.mono (fun _ ha => ha.elim id False.elim) h))))
  | neg b ih =>
    constructor
    · exact ih.2
    · intro hn
      have hb : b.truth := Classical.byContradiction hn
      exact Derivable.notI (Derivable.weaken₁ (ih.1 hb)) Derivable.hyp₀
  | conj b c ihb ihc =>
    constructor
    · rintro ⟨hb, hc⟩
      exact Derivable.andI (ihb.1 hb) (ihc.1 hc)
    · intro hn
      by_cases hb : b.truth
      · have hc : ¬ c.truth := fun hc => hn ⟨hb, hc⟩
        exact Derivable.notI (Derivable.andE₂ Derivable.hyp₀)
          (Derivable.weaken₁ (ihc.2 hc))
      · exact Derivable.notI (Derivable.andE₁ Derivable.hyp₀)
          (Derivable.weaken₁ (ihb.2 hb))
  | disj b c ihb ihc =>
    constructor
    · intro h
      exact h.elim (fun hb => Derivable.orI₁ (ihb.1 hb))
        (fun hc => Derivable.orI₂ (ihc.1 hc))
    · intro hn
      have hb := ihb.2 (fun hb => hn (Or.inl hb))
      have hc := ihc.2 (fun hc => hn (Or.inr hc))
      apply Derivable.notI (q := Term.bot)
      · exact Derivable.orE Derivable.hyp₀
          (Derivable.notE Derivable.hyp₀ (Derivable.weaken₁ (Derivable.weaken₁ hb)))
          (Derivable.notE Derivable.hyp₀ (Derivable.weaken₁ (Derivable.weaken₁ hc)))
      · exact Derivable.notI (Derivable.andE₁ Derivable.hyp₀)
          (Derivable.andE₂ Derivable.hyp₀)

/-- Every consistent extension of Max has the same entire finite Boolean
identity fragment, not just the same atomic identities. -/
theorem IdentityBoolean.theorem_iff (b : IdentityBoolean Sig)
    {Ax : AxiomSet Sig} (hcon : Consistent Ax) (hmax : Ax ⟹ maximalist) :
    Theorem (C.axioms ∪ Ax) b.formula ↔ b.truth := by
  constructor
  · intro h
    classical
    apply Classical.byContradiction
    intro hn
    exact hcon (Derivable.notE h (Derivable.cut hmax (b.decides.2 hn)))
  · intro h
    exact Derivable.cut hmax (b.decides.1 h)

#print axioms identity_iff
#print axioms distinctness_eq
#print axioms entails_max
#print axioms max_theorem_iff
#print axioms max_consistent
#print axioms IdentityBoolean.closedTypes
#print axioms IdentityBoolean.decides
#print axioms IdentityBoolean.theorem_iff

end Classicism.Meta.Research.StrongPossibilityConsequences.MaxDiagram
