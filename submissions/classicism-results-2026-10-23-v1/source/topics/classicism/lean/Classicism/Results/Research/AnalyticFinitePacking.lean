import Classicism.Syntax.Blocks

/-!
# Finite conjunctions and simultaneous existential witnesses

Syntactic support for the finite-arity analytic schema. The list and its length
belong to the metatheory. Each generated formula contains only a finite block of
ordinary quantifiers, in the list's source order, followed by a conjunction.

These proofs use only the existing natural-deduction rules and work over any
signature and axiom set. In particular, witness packing introduces no choice,
comprehension, persistence, or infinitary logical assumption.
-/

namespace Classicism.Meta.Analytic

variable {Sig : Signature} {Ax : AxiomSet Sig}

/-- A finite, right-associated conjunction; the empty conjunction is true. -/
def finiteConj {Γ : Ctx} : List (Formula Sig Γ) → Formula Sig Γ
  | [] => Term.top
  | p :: ps => Term.conj p (finiteConj ps)

@[simp] theorem finiteConj_subst {Γ Θ : Ctx} (s : Sub Sig Γ Θ)
    (ps : List (Formula Sig Γ)) :
    (finiteConj ps).subst s = finiteConj (ps.map (Term.subst s)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change Term.conj (p.subst s) ((finiteConj ps).subst s) =
      Term.conj (p.subst s) (finiteConj (ps.map (Term.subst s)))
    rw [ih]

@[simp] theorem finiteConj_rename {Γ Θ : Ctx} (r : Ren Γ Θ)
    (ps : List (Formula Sig Γ)) :
    (finiteConj ps).rename r = finiteConj (ps.map (Term.rename r)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change Term.conj (p.rename r) ((finiteConj ps).rename r) =
      Term.conj (p.rename r) (finiteConj (ps.map (Term.rename r)))
    rw [ih]

/-- Assemble individually derived conjuncts without changing the premise set. -/
theorem finiteConj_intro {Γ : Ctx} {Δ : List (Formula Sig Γ)}
    : (ps : List (Formula Sig Γ)) →
      (∀ p, p ∈ ps → Derivable Ax Δ p) →
      Derivable Ax Δ (finiteConj ps)
  | [], _ => Derivable.top
  | p :: ps, h =>
    Derivable.andI (h p (List.mem_cons_self ..))
      (finiteConj_intro ps (fun q hq => h q (List.mem_cons_of_mem _ hq)))

/-- Assemble the conjunction after substituting the explicit witness tuple. -/
theorem finiteConj_instantiated {Γ Θ : Ctx} {Δ : List (Formula Sig Θ)}
    (ps : List (Formula Sig Γ)) (s : Sub Sig Γ Θ)
    (h : ∀ p, p ∈ ps → Derivable Ax Δ (p.subst s)) :
    Derivable Ax Δ ((finiteConj ps).subst s) := by
  rw [finiteConj_subst]
  apply finiteConj_intro
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact h p hp

/-- Introduce one simultaneous existential block for the explicit witnesses.
The order in `σs` is the outer-to-inner order of the resulting quantifiers. -/
theorem existsBlock_finiteConj (σs : List Ty) {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} (as : Terms Sig Γ σs)
    (ps : List (Formula Sig (Ctx.block σs Γ)))
    (h : ∀ p, p ∈ ps →
      Derivable Ax Δ (p.subst (Sub.consBlock as Sub.id))) :
    Derivable Ax Δ (Term.existsBlock σs (finiteConj ps)) :=
  Derivable.exIBlock σs as (finiteConj_instantiated ps _ h)

/-- Put a premise independent of the witnesses inside an existential block.
This is the finite prenex step used for the rigid-real guard. -/
theorem existsBlock_conj_left (σs : List Ty) {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} {base : Formula Sig Γ}
    {p : Formula Sig (Ctx.block σs Γ)}
    (hbase : Derivable Ax Δ base)
    (hp : Derivable Ax Δ (Term.existsBlock σs p)) :
    Derivable Ax Δ (Term.existsBlock σs
      (Term.conj (base.rename (Ren.wkBlock σs)) p)) :=
  Derivable.exEBlock σs hp
    (Derivable.exIBlock_vars σs (Derivable.andI
      (Derivable.weaken (Derivable.rename (Ren.wkBlock σs) hbase)
        (List.subset_cons_self _ _))
      Derivable.hyp₀))

/-- Package a fixed guard and all finite conjuncts under the same witnesses. -/
theorem existsBlock_guarded_finiteConj (σs : List Ty) {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} (as : Terms Sig Γ σs)
    (base : Formula Sig Γ)
    (ps : List (Formula Sig (Ctx.block σs Γ)))
    (hbase : Derivable Ax Δ base)
    (h : ∀ p, p ∈ ps →
      Derivable Ax Δ (p.subst (Sub.consBlock as Sub.id))) :
    Derivable Ax Δ (Term.existsBlock σs
      (Term.conj (base.rename (Ren.wkBlock σs)) (finiteConj ps))) :=
  existsBlock_conj_left σs hbase (existsBlock_finiteConj σs as ps h)

/-! ## Packing separately obtained witnesses -/

/-- A finite list of independent predicates, each with its own witness type.
The predicate bodies may share the variables of `Γ`, but no witness variable
from another member of the list occurs in them. -/
inductive Predicates (Sig : Signature) (Γ : Ctx) : List Ty → Type
  | nil : Predicates Sig Γ []
  | cons {σ : Ty} {σs : List Ty} : Formula Sig (σ :: Γ) →
      Predicates Sig Γ σs → Predicates Sig Γ (σ :: σs)

namespace Predicates

/-- Rename the shared parameters while preserving each witness variable. -/
def rename {Γ Θ : Ctx} (r : Ren Γ Θ) :
    ∀ {σs : List Ty}, Predicates Sig Γ σs → Predicates Sig Θ σs
  | [], .nil => .nil
  | _ :: _, .cons b bs => .cons (b.rename (Ren.lift r)) (rename r bs)

theorem rename_rename {Γ Θ Ξ : Ctx} (r : Ren Θ Ξ) (s : Ren Γ Θ) :
    ∀ {σs : List Ty} (ps : Predicates Sig Γ σs),
      rename r (rename s ps) = rename (Ren.comp r s) ps
  | [], .nil => rfl
  | _ :: _, .cons b bs => by
    simp only [rename, Term.rename_rename, ← Ren.lift_comp, rename_rename r s bs]

/-- All predicates at their own variables, in the common witness-block context. -/
def body : ∀ {σs : List Ty} {Γ : Ctx},
    Predicates Sig Γ σs → Formula Sig (Ctx.block σs Γ)
  | [], _, .nil => Term.top
  | σ :: σs, Γ, .cons b bs =>
      Term.conj (b.rename (Ren.wkBlock σs))
        (body (σs := σs) (Γ := σ :: Γ) (rename (Ren.shift (σ := σ)) bs))

/-- The exact simultaneous existential block, in the order of the predicates. -/
def pack {σs : List Ty} {Γ : Ctx} (ps : Predicates Sig Γ σs) : Formula Sig Γ :=
  Term.existsBlock σs (body ps)

private theorem wkBlock_natural : ∀ (σs : List Ty) {Γ Θ : Ctx} (r : Ren Γ Θ),
    Ren.comp (Ren.liftBlock σs r) (Ren.wkBlock σs) =
      Ren.comp (Ren.wkBlock σs) r
  | [], _, _, _ => rfl
  | σ :: σs, _, _, r => by
    funext τ v
    exact congrFun (congrFun (wkBlock_natural σs (Ren.lift r)) τ) (Var.succ v)

theorem body_rename : ∀ {σs : List Ty} {Γ Θ : Ctx} (r : Ren Γ Θ)
    (ps : Predicates Sig Γ σs),
    body (rename r ps) = (body ps).rename (Ren.liftBlock σs r)
  | [], _, _, _, .nil => rfl
  | σ :: σs, Γ, Θ, r, .cons b bs => by
    change Term.conj ((b.rename (Ren.lift r)).rename (Ren.wkBlock σs))
      (body (rename Ren.shift (rename r bs))) =
      Term.conj ((b.rename (Ren.wkBlock σs)).rename (Ren.liftBlock σs (Ren.lift r)))
        ((body (rename Ren.shift bs)).rename (Ren.liftBlock σs (Ren.lift r)))
    congr 1
    · rw [Term.rename_rename, Term.rename_rename, wkBlock_natural]
    · rw [← body_rename (σs := σs) (Γ := σ :: Γ) (Θ := σ :: Θ)
        (Ren.lift (σ := σ) r) (rename (Ren.shift (σ := σ)) bs)]
      simp only [rename_rename] <;> rfl

theorem pack_rename {σs : List Ty} {Γ Θ : Ctx} (r : Ren Γ Θ)
    (ps : Predicates Sig Γ σs) :
    pack (rename r ps) = (pack ps).rename r := by
  rw [pack, pack, Term.rename_existsBlock, body_rename]

/-- Every predicate has a witness, derived under the same hypotheses. -/
def AllExistentials {Ax : AxiomSet Sig} {Γ : Ctx} (Δ : List (Formula Sig Γ)) :
    ∀ {σs : List Ty}, Predicates Sig Γ σs → Prop
  | [], .nil => True
  | _ :: σs, .cons b bs =>
      Derivable Ax Δ (Term.exists' b) ∧ AllExistentials (Ax := Ax) Δ (σs := σs) bs

/-- Finite independent existential derivations give one simultaneous block.
The proof uses existential elimination and introduction, with no choice rule. -/
theorem pack_of_exists : ∀ {σs : List Ty} {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} (ps : Predicates Sig Γ σs),
    AllExistentials (Ax := Ax) Δ ps → Derivable Ax Δ (pack ps)
  | [], _, _, .nil, _ => Derivable.top
  | σ :: σs, Γ, Δ, .cons b bs, h => by
    have htail := pack_of_exists (σs := σs) (Γ := Γ) (Δ := Δ) bs h.2
    apply Derivable.exEBlock [σ] h.1
    apply Derivable.exIBlock_vars [σ]
    change Derivable Ax (b :: Hyps.weaken Δ)
      (Term.existsBlock σs
        (Term.conj (b.rename (Ren.wkBlock σs)) (body (rename Ren.shift bs))))
    have htail' : Derivable Ax (b :: Hyps.weaken Δ) (pack (rename Ren.shift bs)) := by
      rw [pack_rename]
      exact Derivable.weaken (Derivable.rename Ren.shift htail) (List.subset_cons_self _ _)
    exact existsBlock_conj_left σs Derivable.hyp₀ htail'

end Predicates

end Classicism.Meta.Analytic

#print axioms Classicism.Meta.Analytic.Predicates.pack_of_exists
#print axioms Classicism.Meta.Analytic.existsBlock_conj_left
