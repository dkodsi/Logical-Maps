import Classicism.Results.Research.AnalyticRigidificationCertificates

/-!
# Reuse of the certified rigidification quotation

The type of `rigidify_possible.derivable` already contains the exact real and
rigid-real existence formulas.  Extract those syntax trees instead of
quoting and reflecting the large definitions again.  Only safe definitions and
reflexive equality proofs are declared; the kernel checks every declaration.
No semantic reflection, axiom, or new shallow-to-deep translation is performed.

The source and attribution are those of `AnalyticRigidification`: Goodsell /
Claude Fable 5.1, with the explicitly authorized nonempty completeness reading.
-/

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

namespace Classicism.Research.Analytic

/-- The matrix of the seven outer existentials in rigid-real existence. -/
def RealCore {σ : Type} [Ty σ] (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (zero one : σ) (N : σ → Prop) : Prop :=
  RigidStr X le add mul N ∧ □ (Real X le add mul zero one N)

end Classicism.Research.Analytic

open Lean Meta Elab Command

namespace Classicism.Meta.Analytic.ReuseQuotation

/-- Remove administrative wrappers only; never recursively normalize a term. -/
private partial def strip : Expr → Expr
  | .mdata _ b => strip b
  | .letE _ _ v b _ => strip (b.instantiate1 v)
  | e => e

private def args? (e : Expr) (n : Name) (arity : Nat) : Option (Array Expr) :=
  let e := strip e
  if e.isAppOfArity n arity then some e.getAppArgs else none

private def mismatch {α : Type} (expected : String) (e : Expr) : MetaM α := do
  let e := strip e
  let head := match e.getAppFn with
    | .const n _ => n.toString
    | _ => "nonconstant expression"
  throwError "analytic quotation reuse: expected {expected}; found {head} with {e.getAppArgs.size} arguments"

private def application (e : Expr) : MetaM (Expr × Expr) := do
  let some a := args? e ``Classicism.Meta.Term.app 6
    | mismatch "Term.app" e
  pure (a[4]!, a[5]!)

private def negation (e : Expr) : MetaM Expr := do
  if let some a := args? e ``Classicism.Meta.Term.neg 3 then return a[2]!
  let (f, p) ← application e
  unless (args? f ``Classicism.Meta.Term.not 2).isSome do
    mismatch "Term.not at the head of a negation" f
  pure p

private def disjunction (e : Expr) : MetaM (Expr × Expr) := do
  if let some a := args? e ``Classicism.Meta.Term.disj 4 then
    return (a[2]!, a[3]!)
  let (f, q) ← application e
  let (op, p) ← application f
  unless (args? op ``Classicism.Meta.Term.or 2).isSome do
    mismatch "Term.or at the head of a disjunction" op
  pure (p, q)

private def implication (e : Expr) : MetaM (Expr × Expr) := do
  if let some a := args? e ``Classicism.Meta.Term.imp 4 then
    return (a[2]!, a[3]!)
  let (np, q) ← disjunction e
  pure (← negation np, q)

private def equality (e : Expr) : MetaM (Expr × Expr) := do
  if let some a := args? e ``Classicism.Meta.Term.eq' 5 then
    return (a[3]!, a[4]!)
  let (f, q) ← application e
  let (op, p) ← application f
  unless (args? op ``Classicism.Meta.Term.eq 3).isSome do
    mismatch "Term.eq at the head of an equality" op
  pure (p, q)

private def possibility (e : Expr) : MetaM Expr := do
  if let some a := args? e ``Classicism.Meta.Term.dia 3 then return a[2]!
  let (p, q) ← equality (← negation e)
  let qt ← whnf (← inferType q)
  let some qa := args? qt ``Classicism.Meta.Term 3
    | mismatch "a Term type for the right side of the possibility equality" qt
  let bottom := mkApp2 (mkConst ``Classicism.Meta.Term.bot) qa[0]! qa[1]!
  unless ← isDefEq q bottom do
    mismatch "Term.bot on the right side of the possibility equality" q
  pure p

private def existentialBody (e : Expr) : MetaM Expr := do
  if let some a := args? e ``Classicism.Meta.Term.exists' 4 then return a[3]!
  let (op, f) ← application e
  let some ea := args? op ``Classicism.Meta.Term.ex 3
    | mismatch "Term.ex at the head of an existential" op
  let some la := args? f ``Classicism.Meta.Term.lam 5
    | mismatch "Term.lam as the predicate of an existential" f
  unless ← isDefEq ea[2]! la[2]! do
    throwError "analytic quotation reuse: existential and lambda binder types differ"
  pure la[4]!

private def declareDefinition (n : Name) (xs : Array Expr) (body : Expr) : MetaM Expr := do
  let value ← mkLambdaFVars xs body
  let type ← inferType value
  let dv : DefinitionVal :=
    { name := n, levelParams := [], type := type, value := value,
      hints := .abbrev, safety := .safe }
  withOptions (Elab.async.set · false) do addDecl (.defnDecl dv)
  pure (mkAppN (mkConst n) xs)

/-- `Eq.refl lhs` is checked against the stated equality, so the kernel also
checks that the reconstructed expression is definitionally the copied one. -/
private def declareShape (n : Name) (xs : Array Expr) (lhs rhs : Expr) : MetaM Unit := do
  let type ← mkForallFVars xs (← mkEq lhs rhs)
  let value ← mkLambdaFVars xs (← mkEqRefl lhs)
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := n, levelParams := [], type := type, value := value })

run_cmd liftTermElabM do
  let certificate := ``Classicism.Research.Analytic.rigidify_possible.derivable
  let info ← getConstInfo certificate
  unless info.levelParams.isEmpty do
    throwError "analytic quotation reuse: unexpected universe parameters"
  forallTelescope info.type fun xs conclusion => do
    unless xs.size == 1 do
      throwError "analytic quotation reuse: expected one metalogical type parameter"
    unless ← isDefEq (← inferType xs[0]!) (mkConst ``Classicism.Meta.Ty) do
      throwError "analytic quotation reuse: parameter is not a metalogical Ty"
    let some ca := args? conclusion ``Classicism.Meta.Theorem 3
      | mismatch "Theorem Sig Ax S as the certificate's result type" conclusion
    let quoted := ca[2]!
    let quotedRef ← declareDefinition
      (``Classicism.Research.Analytic.rigidify_possible ++ `quoted) xs quoted
    -- The translator emits `.derivable` alone.  Its result type is the source
    -- of this new `.quoted`, and the original proof certifies the copied syntax.
    let quotedTheorem := mkAppN (mkConst ``Classicism.Meta.Theorem)
      #[ca[0]!, ca[1]!, quotedRef]
    let quotedType ← mkForallFVars xs quotedTheorem
    let quotedProof ← mkLambdaFVars xs (mkAppN (mkConst certificate) xs)
    withOptions (Elab.async.set · false) do
      addDecl (.thmDecl
        { name := ``Classicism.Research.Analytic.rigidify_possible ++ `quoted_derivable,
          levelParams := [], type := quotedType, value := quotedProof })
    -- The four premises are C5 and necessary RC at arities one, two and three.
    let mut premises : Array Expr := #[]
    let mut tail := quoted
    for _ in [:4] do
      let (p, q) ← implication tail
      premises := premises.push p
      tail := q
    let (possibleReal, rigidReal) ← implication tail
    let real ← possibility possibleReal
    let realRef ← declareDefinition
      (``Classicism.Research.Analytic.HasReal ++ `term) xs real
    let rigidRef ← declareDefinition
      (``Classicism.Research.Analytic.HasRigidReal ++ `term) xs rigidReal
    -- The existential order is X, le, add, mul, zero, one, N.  The inherited
    -- intrinsically typed contexts retain that order without renaming.
    let mut body := rigidReal
    for _ in [:7] do body ← existentialBody body
    let bodyRef ← declareDefinition
      (``Classicism.Research.Analytic.RealCore ++ `body) xs body
    let mut core := body
    for _ in [:7] do core ← mkAppM ``Classicism.Meta.Term.lam #[core]
    let coreRef ← declareDefinition
      (``Classicism.Research.Analytic.RealCore ++ `term) xs core
    -- Provenance: reassemble exactly the already certified theorem quotation.
    let mut rebuilt ← mkAppM ``Classicism.Meta.Term.imp
      #[← mkAppM ``Classicism.Meta.Term.dia #[realRef], rigidRef]
    for p in premises.reverse do
      rebuilt ← mkAppM ``Classicism.Meta.Term.imp #[p, rebuilt]
    declareShape (``Classicism.Research.Analytic.rigidify_possible ++ `reuse_eq)
      xs quotedRef rebuilt
    let mut existsBody := bodyRef
    for _ in [:7] do existsBody ← mkAppM ``Classicism.Meta.Term.exists' #[existsBody]
    declareShape (``Classicism.Research.Analytic.HasRigidReal ++ `exists_body)
      xs rigidRef existsBody
    let mut lambdaBody := bodyRef
    for _ in [:7] do lambdaBody ← mkAppM ``Classicism.Meta.Term.lam #[lambdaBody]
    declareShape (``Classicism.Research.Analytic.RealCore ++ `term_body)
      xs coreRef lambdaBody

end Classicism.Meta.Analytic.ReuseQuotation

#print axioms Classicism.Research.Analytic.rigidify_possible.reuse_eq
#print axioms Classicism.Research.Analytic.rigidify_possible.quoted_derivable
#print axioms Classicism.Research.Analytic.HasRigidReal.exists_body
#print axioms Classicism.Research.Analytic.RealCore.term_body
