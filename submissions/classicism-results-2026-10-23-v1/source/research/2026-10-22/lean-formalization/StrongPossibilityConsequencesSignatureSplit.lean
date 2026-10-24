import StrongPossibilityConsequencesStability
import Classicism.Results.SentenceSchemas.PossibilityDistinctness
import Classicism.Syntax.Conservativity
import Classicism.Semantics.Denotation

/-!
# Two explicit singleton models split the finite Fregean cell in signature Max

Source: notes/audit-signature-to-pure-sp-20261022.md §3 and
notes/audit-profile-20261022.md §6.2 (session deduction, source id misc).

The semantic witnesses here are CONSTRUCTED full extensional interpretations:
one individual, and all relational constants top or all bottom. They establish
both required C-consistency side conditions for every relational constant,
including in infinite signatures. The conclusion is an actual derivation of
not Atom(F and E1) in signature Max. There is no assumed splitter/model in
that theorem. The separate pure-profile Max+Atom(F and E1) model is not supplied
by this file; hence the full pure-SP/signature-SP incompatibility is not claimed.
-/

namespace Classicism.Meta.Research.StrongPossibilityConsequences.SignatureSplit

open AxiomSet

variable {Sig : Signature}

def fregean (Sig : Signature) : Sentence Sig :=
  Term.forall' (σ := Ty.t) (Term.forall' (σ := Ty.t)
    (Term.imp (Term.iff Term.v1 Term.v0) (Term.eq' Term.v1 Term.v0)))

def oneIndividual (Sig : Signature) : Sentence Sig :=
  Term.forall' (σ := Ty.e) (Term.forall' (σ := Ty.e) (Term.eq' Term.v1 Term.v0))

def cell (Sig : Signature) : Sentence Sig :=
  Term.conj (fregean Sig) (oneIndividual Sig)

/-- Atom at t, expanding the library's algebraic-order definition. -/
def atom (w : Sentence Sig) : Sentence Sig :=
  Term.forall' (σ := Ty.t)
    (Term.iff
      (Term.conj (Term.eq' w.weaken (Term.disj Term.v0 w.weaken))
        (Term.neg (Term.eq' Term.v0 w.weaken)))
      (Term.eq' (Term.neg Term.v0) (Term.disj Term.v0 (Term.neg Term.v0))))

theorem cell_closedTypes : (cell Sig).closedTypes = true := rfl

theorem atom_closedTypes {w : Sentence Sig} (hw : w.closedTypes = true) :
    (atom w).closedTypes = true := by
  simp [atom, Term.weaken, Term.closedTypes_rename, hw]

/-! These are ordinary semantic models, so ordinary Lean propositional
extensionality and choice in their metatheory are appropriate. -/

def singletonValue (b : Prop) : (σ : Ty) → Ty.denote Unit σ
  | .e => ()
  | .var _ => ()
  | .rel ρ => RTy.constD Unit ρ b

def singleton (Sig : Signature) (b : Prop) : Interp Sig :=
  ⟨Unit, fun c => singletonValue b (Sig.typeOf c)⟩

instance (b : Prop) : Nonempty (singleton Sig b).D := ⟨()⟩

theorem cell_holds (b : Prop) : (cell Sig).holds (singleton Sig b) := by
  classical
  constructor
  · intro p q
    change (¬ ((¬ p ∨ q) ∧ (¬ q ∨ p))) ∨ p = q
    by_cases h : (¬ p ∨ q) ∧ (¬ q ∨ p)
    · exact Or.inr (propext ⟨fun hp => h.1.resolve_left (fun hn => hn hp),
        fun hq => h.2.resolve_left (fun hn => hn hq)⟩)
    · exact Or.inl h
  · intro x y
    change (x : Unit) = (y : Unit)
    exact @Subsingleton.elim Unit inferInstance x y

theorem top_denote {Γ : Ctx} (I : Interp Sig) (env : Env I.D Γ) :
    (Term.top : Formula Sig Γ).denote I env = True := by
  apply propext
  exact ⟨fun _ => True.intro, fun _ => Classical.em _⟩

theorem topR_denote {Γ : Ctx} (I : Interp Sig) (env : Env I.D Γ) (ρ : RTy) :
    (Term.topR ρ : Term Sig Γ ρ).denote I env = RTy.constD I.D ρ True :=
  congrArg (RTy.constD I.D ρ) (top_denote I env)

theorem constD_false_ne_true (D : Type) [Nonempty D] :
    ∀ ρ : RTy, RTy.constD D ρ False ≠ RTy.constD D ρ True := by
  intro ρ
  induction ρ using RTy.induction with
  | t => exact fun h => Eq.mpr h True.intro
  | arr σ ρ ih =>
    intro h
    exact ih (congrFun h (Classical.choice (Ty.denote_nonempty D σ)))

def namedTop (c : Sig.Const) {ρ : RTy} (h : Sig.typeOf c = Ty.rel ρ) : Sentence Sig :=
  Term.eq' (h ▸ Term.const c) (Term.topR ρ)

private theorem closedTypes_cast {Γ : Ctx} {σ τ : Ty} (h : σ = τ)
    (t : Term Sig Γ σ) : (h ▸ t).closedTypes = t.closedTypes := by
  cases h
  rfl

private theorem denote_cast {Γ : Ctx} {σ τ : Ty} (h : σ = τ)
    (t : Term Sig Γ σ) (I : Interp Sig) (env : Env I.D Γ) :
    (h ▸ t).denote I env = (h ▸ t.denote I env) := by
  cases h
  rfl

private theorem singletonValue_cast (b : Prop) {σ τ : Ty} (h : σ = τ) :
    (h ▸ singletonValue b σ) = singletonValue b τ := by
  cases h
  rfl

theorem namedTop_closedTypes (c : Sig.Const) {ρ : RTy}
    (h : Sig.typeOf c = Ty.rel ρ) (hρ : ρ.Closed) :
    (namedTop c h).closedTypes = true := by
  have hc : (h ▸ Term.const c : Term Sig [] (Ty.rel ρ)).closedTypes = decide ρ.Closed := by
    rw [closedTypes_cast]
    change decide (Sig.typeOf c).Closed = decide ρ.Closed
    rw [h]
    rfl
  simp [namedTop, hc, Term.topR, Term.closedTypes, hρ]

theorem named_denote (b : Prop) (c : Sig.Const) {ρ : RTy}
    (h : Sig.typeOf c = Ty.rel ρ) :
    (h ▸ Term.const c : Term Sig [] (Ty.rel ρ)).denote (singleton Sig b) .nil =
      RTy.constD Unit ρ b := by
  rw [denote_cast]
  exact singletonValue_cast b h

theorem namedTop_holds (c : Sig.Const) {ρ : RTy} (h : Sig.typeOf c = Ty.rel ρ) :
    (namedTop c h).holds (singleton Sig True) := by
  change (h ▸ Term.const c : Term Sig [] (Ty.rel ρ)).denote (singleton Sig True) .nil =
    (Term.topR ρ : Term Sig [] (Ty.rel ρ)).denote (singleton Sig True) .nil
  rw [named_denote, topR_denote]
  rfl

theorem namedTop_fails (c : Sig.Const) {ρ : RTy} (h : Sig.typeOf c = Ty.rel ρ) :
    ¬ (namedTop c h).holds (singleton Sig False) := by
  change ¬ (h ▸ Term.const c : Term Sig [] (Ty.rel ρ)).denote (singleton Sig False) .nil =
    (Term.topR ρ : Term Sig [] (Ty.rel ρ)).denote (singleton Sig False) .nil
  rw [named_denote, topR_denote]
  exact constD_false_ne_true Unit ρ

/-- The first actual model: F and E1 and c=top. -/
theorem positive_cell_consistent (c : Sig.Const) {ρ : RTy}
    (h : Sig.typeOf c = Ty.rel ρ) :
    Consistent (single (Term.conj (cell Sig) (namedTop c h))) :=
  Consistent.of_interp (singleton Sig True) (by
    intro a ha
    change a = Term.conj (cell Sig) (namedTop c h) at ha
    subst a
    exact ⟨cell_holds True, namedTop_holds c h⟩)

/-- The second actual model: F and E1 and c≠top. -/
theorem negative_cell_consistent (c : Sig.Const) {ρ : RTy}
    (h : Sig.typeOf c = Ty.rel ρ) :
    Consistent (single (Term.conj (cell Sig) (Term.neg (namedTop c h)))) :=
  Consistent.of_interp (singleton Sig False) (by
    intro a ha
    change a = Term.conj (cell Sig) (Term.neg (namedTop c h)) at ha
    subst a
    exact ⟨cell_holds False, namedTop_fails c h⟩)

/-- A signature with a relational constant refutes atomhood of the pure
one-individual Fregean cell, using exactly the preceding two models. -/
theorem maximalist_not_atom_cell_at (c : Sig.Const) {ρ : RTy}
    (h : Sig.typeOf c = Ty.rel ρ) (hρ : ρ.Closed) :
    Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) (Term.neg (atom (cell Sig))) := by
  have hp : Theorem (C.axioms ∪ (maximalist : AxiomSet Sig))
      (Term.dia (Term.conj (cell Sig) (namedTop c h))) :=
    maximalist_entails_possibility _ (possibility_mem
      (by simp [cell_closedTypes, namedTop_closedTypes c h hρ])
      (Consistent.empty_union (positive_cell_consistent c h)))
  have hn : Theorem (C.axioms ∪ (maximalist : AxiomSet Sig))
      (Term.dia (Term.conj (cell Sig) (Term.neg (namedTop c h)))) :=
    maximalist_entails_possibility _ (possibility_mem
      (by simp [cell_closedTypes, namedTop_closedTypes c h hρ])
      (Consistent.empty_union (negative_cell_consistent c h)))
  have core := Derivable.allE₂β (Theorem.ofCMinus (Ax := (maximalist : AxiomSet Sig))
    (C.TheoremMinus.ofPure
      Classicism.Research.StrongPossibilityConsequences.atom_no_split.derivable))
    (cell Sig) (namedTop c h)
  -- `False` in the last implication is quoted as negation of its antecedent.
  have core' : Theorem (C.axioms ∪ (maximalist : AxiomSet Sig))
      (Term.imp (atom (cell Sig))
        (Term.imp (Term.dia (Term.conj (cell Sig) (namedTop c h)))
          (Term.neg (Term.dia (Term.conj (cell Sig) (Term.neg (namedTop c h))))))) := core
  exact Derivable.notI (Derivable.weaken₁ hn)
    (Derivable.impE (Derivable.impE (Derivable.weaken₁ core') Derivable.hyp₀)
      (Derivable.weaken₁ hp))

theorem maximalist_not_atom_cell (hS : Sig.Admitted) :
    Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) (Term.neg (atom (cell Sig))) := by
  obtain ⟨c, hc⟩ := hS.2
  match h : Sig.typeOf c, hc, hS.1 c with
  | .e, hc, _ => exact absurd rfl hc
  | .rel ρ, _, hcl => exact maximalist_not_atom_cell_at c h hcl
  | .var i, _, hcl => exact absurd hcl (Ty.not_closed_var i)

theorem maximalist_add_atom_inconsistent (hS : Sig.Admitted) :
    ¬ Consistent ((maximalist : AxiomSet Sig) ∪ single (atom (cell Sig))) := by
  intro hcon
  apply hcon
  exact Derivable.notE (Theorem.ax (Or.inr rfl))
    (Derivable.mono (fun _ ha => ha.elim Or.inl (fun h => Or.inr (Or.inl h)))
      (maximalist_not_atom_cell hS))

#print axioms maximalist_not_atom_cell
#print axioms positive_cell_consistent
#print axioms negative_cell_consistent

end Classicism.Meta.Research.StrongPossibilityConsequences.SignatureSplit
