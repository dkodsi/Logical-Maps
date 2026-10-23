import Classicism.Results.Research.MaxAtomicitySyntax

/-!
# Finite first-order membership formulas as finite pure C terms

Direct source: `research/2026-10-22/followup/max-atomicity-selector-audit.md`, §§3–5.
This is a syntax compiler and a proof of its closed-type discipline. It does not
instantiate the full Jech–Shelah construction, assert semantic absoluteness, or
provide a non-theorem certificate. Natural-number recursion here is recursion
in the METALANGUAGE on finite syntax, not a type quantifier in C.
-/

namespace Classicism.Meta.Research.MaxAtomicitySetSyntax

open MaxAtomicitySyntax

/-- Finite first-order formulas with equality and membership, using de Bruijn
variables. The new variable at a quantifier is index zero. No infinitary case. -/
inductive SetFormula : Nat → Type
  | bot {n : Nat} : SetFormula n
  | top {n : Nat} : SetFormula n
  | eq {n : Nat} : Fin n → Fin n → SetFormula n
  | mem {n : Nat} : Fin n → Fin n → SetFormula n
  | neg {n : Nat} : SetFormula n → SetFormula n
  | conj {n : Nat} : SetFormula n → SetFormula n → SetFormula n
  | disj {n : Nat} : SetFormula n → SetFormula n → SetFormula n
  | imp {n : Nat} : SetFormula n → SetFormula n → SetFormula n
  | iff {n : Nat} : SetFormula n → SetFormula n → SetFormula n
  | all {n : Nat} : SetFormula (n + 1) → SetFormula n
  | ex {n : Nat} : SetFormula (n + 1) → SetFormula n

def liftEnv {n : Nat} {Γ : Ctx} (ρ : Fin n → PT Γ U) :
    Fin (n + 1) → PT ((U : Ty) :: Γ) U :=
  Fin.cases Term.v0 (fun i => (ρ i).weaken)

def translate {n : Nat} (φ : SetFormula n) {Γ : Ctx}
    (E : PT Γ ER) (ρ : Fin n → PT Γ U) : Formula Signature.pure Γ :=
  match φ with
  | .bot => Term.bot
  | .top => Term.top
  | .eq i j => Term.eq' (ρ i) (ρ j)
  | .mem i j => member E (ρ i) (ρ j)
  | .neg p => Term.neg (translate p E ρ)
  | .conj p q => Term.conj (translate p E ρ) (translate q E ρ)
  | .disj p q => Term.disj (translate p E ρ) (translate q E ρ)
  | .imp p q => Term.imp (translate p E ρ) (translate q E ρ)
  | .iff p q => Term.iff (translate p E ρ) (translate q E ρ)
  | .all p => Term.forall' (σ := U) (translate p E.weaken (liftEnv ρ))
  | .ex p => Term.exists' (σ := U) (translate p E.weaken (liftEnv ρ))

theorem liftEnv_closedTypes {n : Nat} {Γ : Ctx} (ρ : Fin n → PT Γ U)
    (hρ : ∀ i, (ρ i).closedTypes = true) :
    ∀ i, (liftEnv ρ i).closedTypes = true := by
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    change ((ρ j).weaken (τ := U)).closedTypes = true
    simpa only [Term.weaken, Term.closedTypes_rename] using hρ j

/-- The compiler never introduces a type variable or a forbidden output type.
This is a metatheorem about intrinsically typed C terms, not a C theorem. -/
theorem translate_closedTypes {n : Nat} (φ : SetFormula n) :
    ∀ {Γ : Ctx} (E : PT Γ ER) (ρ : Fin n → PT Γ U),
      E.closedTypes = true → (∀ i, (ρ i).closedTypes = true) →
      (translate φ E ρ).closedTypes = true := by
  induction φ with
  | bot => intros; rfl
  | top => intros; rfl
  | eq i j =>
    intro Γ E ρ hE hρ
    simp only [translate, Term.closedTypes_eq', hρ i, hρ j]
    rfl
  | mem i j =>
    intro Γ E ρ hE hρ
    change ((E.closedTypes && (ρ i).closedTypes) && (ρ j).closedTypes) = true
    simp only [hE, hρ i, hρ j, Bool.true_and]
  | neg p ih =>
    intro Γ E ρ hE hρ
    simpa only [translate, Term.closedTypes_neg] using ih E ρ hE hρ
  | conj p q ihp ihq =>
    intro Γ E ρ hE hρ
    simp only [translate, Term.closedTypes_conj, ihp E ρ hE hρ,
      ihq E ρ hE hρ, Bool.true_and]
  | disj p q ihp ihq =>
    intro Γ E ρ hE hρ
    simp only [translate, Term.closedTypes_disj, ihp E ρ hE hρ,
      ihq E ρ hE hρ, Bool.true_and]
  | imp p q ihp ihq =>
    intro Γ E ρ hE hρ
    simp only [translate, Term.closedTypes_imp, ihp E ρ hE hρ,
      ihq E ρ hE hρ, Bool.true_and]
  | iff p q ihp ihq =>
    intro Γ E ρ hE hρ
    simp only [translate, Term.closedTypes_iff, ihp E ρ hE hρ,
      ihq E ρ hE hρ, Bool.true_and]
  | all p ih =>
    intro Γ E ρ hE hρ
    change (translate p E.weaken (liftEnv ρ)).closedTypes = true
    exact ih E.weaken (liftEnv ρ)
      (by simpa only [Term.weaken, Term.closedTypes_rename] using hE)
      (liftEnv_closedTypes ρ hρ)
  | ex p ih =>
    intro Γ E ρ hE hρ
    change (translate p E.weaken (liftEnv ρ)).closedTypes = true
    exact ih E.weaken (liftEnv ρ)
      (by simpa only [Term.weaken, Term.closedTypes_rename] using hE)
      (liftEnv_closedTypes ρ hρ)

private abbrev binaryCtx : Ctx := [(U : Ty), (U : Ty), (ER : Ty)]

/-- In the final body, index 0 denotes c and index 1 denotes G. -/
private def binaryEnv : Fin 2 → PT binaryCtx U :=
  Fin.cases Term.v1 (Fin.cases Term.v0 Fin.elim0)

private theorem binaryEnv_closedTypes : ∀ i, (binaryEnv i).closedTypes = true := by
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro k; exact Fin.elim0 k

/-- λE c G. φ_E(c,G). This is a term, not a new logical constant. A future
concrete JSCode formula can be supplied here without changing the language. -/
def quoteBinary (φ : SetFormula 2) :
    Term Signature.pure [] ((ER : Ty) ⇒ (U : Ty) ⇒ (U : Ty) ⇒ RTy.t) :=
  .lam (.lam (.lam (translate φ Term.v2 binaryEnv)))

theorem quoteBinary_closedTypes (φ : SetFormula 2) :
    (quoteBinary φ).closedTypes = true := by
  change (translate φ (Term.v2 : PT binaryCtx ER) binaryEnv).closedTypes = true
  exact translate_closedTypes φ Term.v2 binaryEnv rfl binaryEnv_closedTypes

theorem quoteBinary_pure (φ : SetFormula 2) : (quoteBinary φ).pure = true :=
  (quoteBinary φ).pure_of_pureSig

end Classicism.Meta.Research.MaxAtomicitySetSyntax

#print axioms Classicism.Meta.Research.MaxAtomicitySetSyntax.translate_closedTypes
#print axioms Classicism.Meta.Research.MaxAtomicitySetSyntax.quoteBinary_closedTypes
#print axioms Classicism.Meta.Research.MaxAtomicitySetSyntax.quoteBinary_pure
