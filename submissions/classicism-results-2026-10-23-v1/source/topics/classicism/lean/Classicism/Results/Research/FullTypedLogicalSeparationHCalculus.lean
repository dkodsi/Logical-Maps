import Classicism.Syntax.Derivation

/-!
# A Subst-free H calculus for full logical separation

Direct source: `research/2026-10-23/operator-characterizations/h-logical-observer-strengthening.txt`,
sections 1--3 (misc, 23 October 2026, unpaginated).

This independently generated proof relation has precisely H's natural-deduction
rules, structural weakening admissible, contextual beta/eta/delta conversion,
and Existence at e. It has NO Subst, Equivalence, necessitation, extensionality,
or Functionality constructor. Importing the existing syntax does not identify
this relation with `Meta.Derivable`, which already contains Classicism.

Context-indexed axioms permit naming local axiom instances; no renaming or
substitution stability of a supplied axiom family is assumed implicitly.
-/

namespace Classicism.Research.FullTypedLogicalSeparationH
open Classicism.Meta

abbrev Axioms (Sig : Signature) := ∀ {Γ : Ctx}, Formula Sig Γ → Prop
abbrev NoAxioms (Sig : Signature) : Axioms Sig := fun {_} _ => False
variable {Sig : Signature}

inductive Derives (Ax : Axioms Sig) : ∀ {Γ : Ctx}, List (Formula Sig Γ) → Formula Sig Γ → Prop
  /-- A hypothesis. -/
  | hyp {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} :
      p ∈ Δ → Derives Ax Δ p
  /-- An axiom of the theory, at any context. -/
  | ax {Γ : Ctx} {Δ : List (Formula Sig Γ)} {a : Formula Sig Γ} :
      Ax a → Derives Ax Δ a
  /-- H's sole non-rule logical axiom: existence at e. -/
  | existence {Γ : Ctx} {Δ : List (Formula Sig Γ)} :
      Derives Ax Δ (Term.exists' (σ := Ty.e) (Term.eq' Term.v0 Term.v0))
  /-- `∧`-introduction. -/
  | andI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derives Ax Δ p → Derives Ax Δ q → Derives Ax Δ (Term.conj p q)
  /-- `∧`-elimination, left. -/
  | andE₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derives Ax Δ (Term.conj p q) → Derives Ax Δ p
  /-- `∧`-elimination, right. -/
  | andE₂ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derives Ax Δ (Term.conj p q) → Derives Ax Δ q
  /-- `∨`-introduction, left. -/
  | orI₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derives Ax Δ p → Derives Ax Δ (Term.disj p q)
  /-- `∨`-introduction, right. -/
  | orI₂ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derives Ax Δ q → Derives Ax Δ (Term.disj p q)
  /-- `∨`-elimination: by cases. -/
  | orE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q r : Formula Sig Γ} :
      Derives Ax Δ (Term.disj p q) → Derives Ax (p :: Δ) r → Derives Ax (q :: Δ) r →
      Derives Ax Δ r
  /-- `¬`-introduction: what yields a contradiction is false. -/
  | notI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derives Ax (p :: Δ) q → Derives Ax (p :: Δ) (Term.neg q) → Derives Ax Δ (Term.neg p)
  /-- `¬`-elimination: from a contradiction, anything. -/
  | notE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derives Ax Δ p → Derives Ax Δ (Term.neg p) → Derives Ax Δ q
  /-- Excluded middle, which makes the propositional fragment classical. -/
  | em {Γ : Ctx} {Δ : List (Formula Sig Γ)} (p : Formula Sig Γ) :
      Derives Ax Δ (Term.disj p (Term.neg p))
  /-- `UI`: `∀σ F → F A`, for any predicate term `F`. -/
  | allE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)} :
      Derives Ax Δ (.app (.all σ) F) → (a : Term Sig Γ σ) → Derives Ax Δ (.app F a)
  /-- `Gen`: from `b`, derived with a fresh variable and hypotheses not mentioning it,
  `∀v. b`. -/
  | allI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {b : Formula Sig (σ :: Γ)} :
      Derives Ax (Hyps.weaken Δ) b → Derives Ax Δ (Term.forall' b)
  /-- `EG`: `F A → ∃σ F`. -/
  | exI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)}
      (a : Term Sig Γ σ) : Derives Ax Δ (.app F a) → Derives Ax Δ (.app (.ex σ) F)
  /-- `Inst`: from `∃σ F`, and `r` derived from `F v` for a fresh `v`, `r`. -/
  | exE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)}
      {r : Formula Sig Γ} :
      Derives Ax Δ (.app (.ex σ) F) →
      Derives Ax (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ) r.weaken →
      Derives Ax Δ r
  /-- `Ref`: `A = A`. -/
  | refl {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} (a : Term Sig Γ σ) :
      Derives Ax Δ (Term.eq' a a)
  /-- `LL`: from `A = B` and `F A`, `F B`. -/
  | ll {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {a b : Term Sig Γ σ}
      (F : Term Sig Γ (σ ⇒ RTy.t)) :
      Derives Ax Δ (Term.eq' a b) → Derives Ax Δ (.app F a) → Derives Ax Δ (.app F b)
  /-- `β`, `η` and `δ`: derivability transfers along conversion. -/
  | conv {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derives Ax Δ p → p ≡ q → Derives Ax Δ q

namespace Derives

theorem weaken {Ax : Axioms Sig} : ∀ {Γ : Ctx} {Δ Δ' : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derives Ax Δ p → Δ ⊆ Δ' → Derives Ax Δ' p
  | _, _, _, _, hyp h, hs => hyp (hs h)
  | _, _, _, _, ax h, _ => ax h
  | _, _, _, _, existence, _ => existence
  | _, _, _, _, andI h₁ h₂, hs => andI (weaken h₁ hs) (weaken h₂ hs)
  | _, _, _, _, andE₁ h, hs => andE₁ (weaken h hs)
  | _, _, _, _, andE₂ h, hs => andE₂ (weaken h hs)
  | _, _, _, _, orI₁ h, hs => orI₁ (weaken h hs)
  | _, _, _, _, orI₂ h, hs => orI₂ (weaken h hs)
  | _, _, _, _, orE h h₁ h₂, hs =>
    orE (weaken h hs) (weaken h₁ (List.cons_subset_cons _ hs)) (weaken h₂ (List.cons_subset_cons _ hs))
  | _, _, _, _, notI h₁ h₂, hs =>
    notI (weaken h₁ (List.cons_subset_cons _ hs)) (weaken h₂ (List.cons_subset_cons _ hs))
  | _, _, _, _, notE h₁ h₂, hs => notE (weaken h₁ hs) (weaken h₂ hs)
  | _, _, _, _, em p, _ => em p
  | _, _, _, _, allE h a, hs => allE (weaken h hs) a
  | _, _, _, _, allI h, hs => allI (weaken h (List.map_subset_of_subset _ hs))
  | _, _, _, _, exI a h, hs => exI a (weaken h hs)
  | _, _, _, _, exE h h', hs =>
    exE (weaken h hs) (weaken h' (List.cons_subset_cons _ (List.map_subset_of_subset _ hs)))
  | _, _, _, _, refl a, _ => refl a
  | _, _, _, _, ll F h₁ h₂, hs => ll F (weaken h₁ hs) (weaken h₂ hs)
  | _, _, _, _, conv h c, hs => conv (weaken h hs) c


theorem rename {Ax : Axioms Sig}
    (hAx : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {a : Formula Sig Γ}, Ax a → Ax (a.rename r)) : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {Δ' : List (Formula Sig Γ)}
    {p : Formula Sig Γ}, Derives Ax Δ' p → Derives Ax (Hyps.rename r Δ') (p.rename r)
  | _, _, r, _, _, hyp h => hyp (List.mem_map.2 ⟨_, h, rfl⟩)
  | _, _, r, _, _, ax h => ax (hAx r h)
  | _, _, _, _, _, existence => existence
  | _, _, r, _, _, andI h₁ h₂ => andI (rename hAx r h₁) (rename hAx r h₂)
  | _, _, r, _, _, andE₁ h => andE₁ (rename hAx r h)
  | _, _, r, _, _, andE₂ h => andE₂ (rename hAx r h)
  | _, _, r, _, _, orI₁ h => orI₁ (rename hAx r h)
  | _, _, r, _, _, orI₂ h => orI₂ (rename hAx r h)
  | _, _, r, _, _, orE h h₁ h₂ => orE (rename hAx r h) (rename hAx r h₁) (rename hAx r h₂)
  | _, _, r, _, _, notI h₁ h₂ => notI (rename hAx r h₁) (rename hAx r h₂)
  | _, _, r, _, _, notE h₁ h₂ => notE (rename hAx r h₁) (rename hAx r h₂)
  | _, _, r, _, _, em p => em _
  | _, _, r, _, _, allE h a => allE (rename hAx r h) (a.rename r)
  | _, _, r, _, _, allI h => by
    have := rename hAx (Ren.lift r) h
    rw [← Hyps.weaken_rename] at this
    exact allI this
  | _, _, r, _, _, exI a h => exI (a.rename r) (rename hAx r h)
  | _, _, r, Δ', _, exE (σ := σ) (F := F) (r := q) h h' => by
    have this := rename hAx (Ren.lift r) h'
    have e₁ : Hyps.rename (Ren.lift r) (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ')
        = Term.app (F.rename r).weaken (.var .zero) :: Hyps.weaken (Hyps.rename r Δ') := by
      simp only [Hyps.rename, List.map_cons, Hyps.weaken_rename, Term.weaken_rename]
      rfl
    have e₂ : q.weaken.rename (Ren.lift r) = (q.rename r).weaken (τ := σ) :=
      (Term.weaken_rename (τ := σ) r q).symm
    rw [e₁, e₂] at this
    exact exE (rename hAx r h) this
  | _, _, r, _, _, refl a => refl _
  | _, _, r, _, _, ll F h₁ h₂ => ll (F.rename r) (rename hAx r h₁) (rename hAx r h₂)
  | _, _, r, _, _, conv h c => conv (rename hAx r h) (Conv.rename r c)


/-- Changing proper axioms preserves H derivations; no C rule is involved. -/
theorem monoAx {Ax Ax' : Axioms Sig}
    (hA : ∀ {Γ : Ctx} {p : Formula Sig Γ}, Ax p → Ax' p) :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derives Ax Δ p → Derives Ax' Δ p
  | _, _, _, .hyp h => .hyp h
  | _, _, _, .ax h => .ax (hA h)
  | _, _, _, .existence => .existence
  | _, _, _, .andI h k => .andI (monoAx hA h) (monoAx hA k)
  | _, _, _, .andE₁ h => .andE₁ (monoAx hA h)
  | _, _, _, .andE₂ h => .andE₂ (monoAx hA h)
  | _, _, _, .orI₁ h => .orI₁ (monoAx hA h)
  | _, _, _, .orI₂ h => .orI₂ (monoAx hA h)
  | _, _, _, .orE h k l => .orE (monoAx hA h) (monoAx hA k) (monoAx hA l)
  | _, _, _, .notI h k => .notI (monoAx hA h) (monoAx hA k)
  | _, _, _, .notE h k => .notE (monoAx hA h) (monoAx hA k)
  | _, _, _, .em p => .em p
  | _, _, _, .allE h a => .allE (monoAx hA h) a
  | _, _, _, .allI h => .allI (monoAx hA h)
  | _, _, _, .exI a h => .exI a (monoAx hA h)
  | _, _, _, .exE h k => .exE (monoAx hA h) (monoAx hA k)
  | _, _, _, .refl a => .refl a
  | _, _, _, .ll F h k => .ll F (monoAx hA h) (monoAx hA k)
  | _, _, _, .conv h c => .conv (monoAx hA h) c

theorem rename_noAx {Γ Δ : Ctx} (r : Ren Γ Δ)
    {Ξ : List (Formula Sig Γ)} {p : Formula Sig Γ}
    (h : Derives (NoAxioms Sig) Ξ p) :
    Derives (NoAxioms Sig) (Hyps.rename r Ξ) (p.rename r) :=
  rename (Ax := NoAxioms Sig) (fun {_ _} _ {_} hFalse => False.elim hFalse) r h



variable {Ax : Axioms Sig}

/-- A hypothesis just added. -/
theorem hyp₀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} :
    Derives Ax (p :: Δ) p := hyp (List.mem_cons_self ..)

/-- Add one hypothesis. -/
theorem weaken₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ}
    (h : Derives Ax Δ p) : Derives Ax (q :: Δ) p :=
  weaken h (List.subset_cons_self _ _)

variable {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ}

/-- `→`-introduction, by excluded middle on the antecedent. -/
theorem impI (h : Derives Ax (p :: Δ) q) : Derives Ax Δ (Term.imp p q) :=
  orE (em p) (orI₂ h) (orI₁ hyp₀)

/-- `→`-elimination, modus ponens. -/
theorem impE (h : Derives Ax Δ (Term.imp p q)) (hp : Derives Ax Δ p) : Derives Ax Δ q :=
  orE h (notE (weaken₁ hp) hyp₀) hyp₀

theorem iffI (h₁ : Derives Ax (p :: Δ) q) (h₂ : Derives Ax (q :: Δ) p) :
    Derives Ax Δ (Term.iff p q) :=
  andI (impI h₁) (impI h₂)

theorem iffE₁ (h : Derives Ax Δ (Term.iff p q)) (hp : Derives Ax Δ p) : Derives Ax Δ q :=
  impE (andE₁ h) hp

theorem iffE₂ (h : Derives Ax Δ (Term.iff p q)) (hq : Derives Ax Δ q) : Derives Ax Δ p :=
  impE (andE₂ h) hq

/-- `⊤` is a theorem of every theory: it is an instance of excluded middle. -/
theorem top : Derives Ax Δ Term.top := em _

/-- From `⊥`, anything. -/
theorem botE (h : Derives Ax Δ Term.bot) : Derives Ax Δ p := notE (andE₁ h) (andE₂ h)

/-- Symmetry of identity, from `Ref` and `LL` at the predicate `λz. z = a`. -/
theorem eqSymm {σ : Ty} {a b : Term Sig Γ σ} (h : Derives Ax Δ (Term.eq' a b)) :
    Derives Ax Δ (Term.eq' b a) :=
  have h₁ : Derives Ax Δ (.app (.lam (Term.eq' (.var .zero) a.weaken)) b) :=
    ll (.lam (Term.eq' (.var .zero) a.weaken)) h
      (conv (refl a) (Conv.symm (by
        have := Conv.beta (Sig := Sig) (Γ := Γ) (Term.eq' (.var .zero) a.weaken) a
        simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)))
  conv h₁ (by
    have := Conv.beta (Sig := Sig) (Γ := Γ) (Term.eq' (.var .zero) a.weaken) b
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)

/-! ### Leibniz's Law in the forms the translator meets

The strict layer's proofs are equational: Lean's `congrArg`, `Eq.trans`, `Eq.symm`,
`Eq.mpr` and `congrFun` are each `LL` at a particular predicate, and these are their
derivations. Each ends in a `conv` that β-reduces the predicate's application. -/

/-- Transitivity: from `a = b` and `b = c`, `a = c`, by `LL` at `λz. a = z`. -/
theorem eqTrans {σ : Ty} {a b c : Term Sig Γ σ} (h₁ : Derives Ax Δ (Term.eq' a b))
    (h₂ : Derives Ax Δ (Term.eq' b c)) : Derives Ax Δ (Term.eq' a c) :=
  have h : Derives Ax Δ (.app (.lam (Term.eq' a.weaken (.var .zero))) c) :=
    ll (.lam (Term.eq' a.weaken (.var .zero))) h₂ (conv h₁ (Conv.symm (by
      have := Conv.beta' (Sig := Sig) (Γ := Γ) (Term.eq' a.weaken (.var .zero)) b
      simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)))
  conv h (by
    have := Conv.beta' (Sig := Sig) (Γ := Γ) (Term.eq' a.weaken (.var .zero)) c
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)

/-- Congruence: from `a = b`, `F a = F b`, by `LL` at `λz. F a = F z`. This is Lean's
`congrArg`. -/
theorem eqCongr {σ : Ty} {ρ : RTy} (F : Term Sig Γ (σ ⇒ ρ)) {a b : Term Sig Γ σ}
    (h : Derives Ax Δ (Term.eq' a b)) :
    Derives Ax Δ (Term.eq' (.app F a) (.app F b)) :=
  have h' : Derives Ax Δ (.app (.lam (Term.eq' (.app F.weaken a.weaken) (.app F.weaken (.var .zero)))) b) :=
    ll _ h (conv (refl (.app F a)) (Conv.symm (by
      have := Conv.beta' (Sig := Sig) (Γ := Γ)
        (Term.eq' (.app F.weaken a.weaken) (.app F.weaken (.var .zero))) a
      simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)))
  conv h' (by
    have := Conv.beta' (Sig := Sig) (Γ := Γ)
      (Term.eq' (.app F.weaken a.weaken) (.app F.weaken (.var .zero))) b
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)

/-- From `f = g`, `f a = g a`, by `LL` at `λz. f a = z a`. This is Lean's `congrFun`. -/
theorem eqCongrFun {σ : Ty} {ρ : RTy} {f g : Term Sig Γ (σ ⇒ ρ)}
    (h : Derives Ax Δ (Term.eq' f g)) (a : Term Sig Γ σ) :
    Derives Ax Δ (Term.eq' (.app f a) (.app g a)) :=
  have h' : Derives Ax Δ (.app (.lam (Term.eq' (.app f.weaken a.weaken) (.app (.var .zero) a.weaken))) g) :=
    ll _ h (conv (refl (.app f a)) (Conv.symm (by
      have := Conv.beta' (Sig := Sig) (Γ := Γ)
        (Term.eq' (.app f.weaken a.weaken) (.app (.var .zero) a.weaken)) f
      simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)))
  conv h' (by
    have := Conv.beta' (Sig := Sig) (Γ := Γ)
      (Term.eq' (.app f.weaken a.weaken) (.app (.var .zero) a.weaken)) g
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)

/-- From `p = q` and `p`, `q`: `LL` at the identity predicate `λz. z`. Lean's `Eq.mp`. -/
theorem eqMp {p q : Formula Sig Γ} (h : Derives Ax Δ (Term.eq' p q)) (hp : Derives Ax Δ p) :
    Derives Ax Δ q :=
  conv (ll (.lam (.var .zero)) h (conv hp (Conv.symm (Conv.beta' (.var .zero) p))))
    (Conv.beta' (.var .zero) q)

/-- From `p = q` and `q`, `p`. Lean's `Eq.mpr`. -/
theorem eqMpr {p q : Formula Sig Γ} (h : Derives Ax Δ (Term.eq' p q)) (hq : Derives Ax Δ q) :
    Derives Ax Δ p :=
  eqMp (eqSymm h) hq

theorem allEβ {σ : Ty} {b : Formula Sig (σ :: Γ)} (h : Derives Ax Δ (Term.forall' b))
    (a : Term Sig Γ σ) : Derives Ax Δ (b.instantiate a) :=
  conv (allE h a) (Conv.beta' b a)

theorem exIβ {σ : Ty} {b : Formula Sig (σ :: Γ)} (a : Term Sig Γ σ)
    (h : Derives Ax Δ (b.instantiate a)) : Derives Ax Δ (Term.exists' b) :=
  exI a (conv h (Conv.symm (Conv.beta' b a)))

theorem llβ {σ : Ty} {a b : Term Sig Γ σ} (P : Formula Sig (σ :: Γ))
    (h₁ : Derives Ax Δ (Term.eq' a b)) (h₂ : Derives Ax Δ (P.instantiate a)) :
    Derives Ax Δ (P.instantiate b) :=
  conv (ll (.lam P) h₁ (conv h₂ (Conv.symm (Conv.beta' P a)))) (Conv.beta' P b)

theorem eqCongrβ {σ : Ty} {ρ : RTy} (B : Term Sig (σ :: Γ) ρ) {a b : Term Sig Γ σ}
    (h : Derives Ax Δ (Term.eq' a b)) :
    Derives Ax Δ (Term.eq' (B.instantiate a) (B.instantiate b)) :=
  have h' := eqCongr (.lam B) h
  conv h' (Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.beta' B a)) (Conv.beta' B b))

theorem eqCongrFunβ {σ : Ty} {ρ : RTy} {b₁ b₂ : Term Sig (σ :: Γ) ρ}
    (h : Derives Ax Δ (Term.eq' (Term.lam b₁) (Term.lam b₂))) (a : Term Sig Γ σ) :
    Derives Ax Δ (Term.eq' (b₁.instantiate a) (b₂.instantiate a)) :=
  have h' := eqCongrFun h a
  conv h' (Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.beta' b₁ a)) (Conv.beta' b₂ a))


end Derives

end Classicism.Research.FullTypedLogicalSeparationH
