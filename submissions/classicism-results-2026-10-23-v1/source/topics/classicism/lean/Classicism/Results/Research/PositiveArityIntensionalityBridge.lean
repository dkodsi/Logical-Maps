import Classicism.Results.Research.BetaIdentityContextualClosure

/-!
# Positive-arity Intensionality suffices for full contextual conversion

Original independent metatheory, 23 October 2026; direct source `misc`.

This file introduces a raw judgement calculus, not C's existing derivability relation.
Its only extensionality rule is positive-arity Intensionality, with an explicitly
boxed, fully quantified coextension premise. NULLARY (propositional) Intensionality
is absent. It has ordinary equality rules,
propositional equality elimination, generalization and theorem-only necessitation.
There is no primitive zeta, eta, abstraction congruence or conversion rule.

Primitive lambda term formation and arbitrary-output beta identities are assumptions
of this component. It does not construct lambda syntax from a lambda-free base.
The calculus has NO lists of formula hypotheses: Gen and Nec concern theorems only.
Its universal binder is primitive in Judgement and does not use beta conversion for
its introduction. No K, T or Barcan rule is assumed.
-/

namespace Classicism.Meta.Research.BetaIdentity.PositiveArityModalBridge

/-- The fragment of raw logical judgements needed by the independent bridge. -/
inductive Judgement (Sig : Signature) : Ctx → Type
  | equal {Γ : Ctx} {τ : Ty} (a b : Term Sig Γ τ) : Judgement Sig Γ
  | iff {Γ : Ctx} (p q : Term Sig Γ RTy.t) : Judgement Sig Γ
  | all {Γ : Ctx} (σ : Ty) (p : Judgement Sig (σ :: Γ)) : Judgement Sig Γ
  | box {Γ : Ctx} (p : Judgement Sig Γ) : Judgement Sig Γ

variable {Sig : Signature}

/-- Structural renaming of raw judgements, including the primitive binder. -/
def Judgement.rename : {Γ Δ : Ctx} → Ren Γ Δ → Judgement Sig Γ → Judgement Sig Δ
  | _, _, r, .equal a b => .equal (a.rename r) (b.rename r)
  | _, _, r, .iff p q => .iff (p.rename r) (q.rename r)
  | _, _, r, .all σ p => .all σ (p.rename (Ren.lift r))
  | _, _, r, .box p => .box (p.rename r)

/-- Coextension explicitly quantifies every remaining relational argument and
compares the fully applied truth-valued terms. -/
def coextension : (ρ : RTy) → {Γ : Ctx} →
    Term Sig Γ ρ → Term Sig Γ ρ → Judgement Sig Γ
  | .t, _, p, q => .iff p q
  | .arr σ ρ, _, f, g => .all σ
      (coextension ρ (.app f.weaken (.var .zero)) (.app g.weaken (.var .zero)))

/-- An independent theorem-only proof calculus. Positive-arity Intensionality is the stated
logical assumption; theorem-level zeta will be proved from it. -/
inductive Proof : {Γ : Ctx} → Judgement Sig Γ → Prop
  | refl {Γ : Ctx} {τ : Ty} (a : Term Sig Γ τ) : Proof (.equal a a)
  | symm {Γ : Ctx} {τ : Ty} {a b : Term Sig Γ τ} :
      Proof (.equal a b) → Proof (.equal b a)
  | trans {Γ : Ctx} {τ : Ty} {a b c : Term Sig Γ τ} :
      Proof (.equal a b) → Proof (.equal b c) → Proof (.equal a c)
  | app {Γ : Ctx} {σ : Ty} {ρ : RTy}
      {f g : Term Sig Γ (σ ⇒ ρ)} {a b : Term Sig Γ σ} :
      Proof (.equal f g) → Proof (.equal a b) → Proof (.equal (.app f a) (.app g b))
  | beta {Γ : Ctx} {σ : Ty} {ρ : RTy}
      (b : Term Sig (σ :: Γ) ρ) (a : Term Sig Γ σ) :
      Proof (.equal (.app (.lam b) a) (b.instantiate a))
  | rename {Γ Δ : Ctx} {p : Judgement Sig Γ} (r : Ren Γ Δ) :
      Proof p → Proof (p.rename r)
  | eq_iff {Γ : Ctx} {p q : Term Sig Γ RTy.t} :
      Proof (.equal p q) → Proof (.iff p q)
  | gen {Γ : Ctx} {σ : Ty} {p : Judgement Sig (σ :: Γ)} :
      Proof p → Proof (.all σ p)
  | nec {Γ : Ctx} {p : Judgement Sig Γ} : Proof p → Proof (.box p)
  | intensionality {Γ : Ctx} {σ : Ty} {ρ : RTy}
      {f g : Term Sig Γ (σ ⇒ ρ)} :
      Proof (.box (coextension (σ ⇒ ρ) f g)) → Proof (.equal f g)

/-- Equality yields fully quantified material coextension, by induction on the
relational output type. No extensionality or modal rule is used here. -/
theorem equality_coextension (ρ : RTy) : ∀ {Γ : Ctx} {a b : Term Sig Γ ρ},
    Proof (.equal a b) → Proof (coextension ρ a b) := by
  induction ρ using RTy.induction with
  | t =>
    intro Γ a b h
    exact Proof.eq_iff h
  | arr σ ρ ih =>
    intro Γ a b h
    exact Proof.gen (ih (Proof.app (Proof.rename Ren.shift h)
      (Proof.refl (.var .zero))))

/-- The fresh-variable identity rule is DERIVED: first generalize the whole
coextension tuple, then necessitate, then use positive-arity Intensionality. -/
theorem zeta_eq {Γ : Ctx} {σ : Ty} {ρ : RTy} {f g : Term Sig Γ (σ ⇒ ρ)}
    (h : Proof (.equal (.app f.weaken (.var .zero)) (.app g.weaken (.var .zero)))) :
    Proof (.equal f g) :=
  Proof.intensionality (Proof.nec (Proof.gen (equality_coextension ρ h)))

/-- Eliminate every primitive zeta use from the earlier beta-identity calculus
by translating it to the independently derived modal bridge. -/
theorem of_eqProof {Γ : Ctx} {τ : Ty} {a b : Term Sig Γ τ}
    (h : EqProof a b) : Proof (.equal a b) := by
  induction h with
  | refl a => exact Proof.refl a
  | symm _ ih => exact Proof.symm ih
  | trans _ _ ih₁ ih₂ => exact Proof.trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact Proof.app ih₁ ih₂
  | beta b a => exact Proof.beta b a
  | zeta _ ih => exact zeta_eq ih

/-- Full contextual beta/eta identities in the independent theorem calculus
with beta identities, Gen, Nec and positive-arity Intensionality. -/
theorem contextual_conversion {Γ : Ctx} {τ : Ty} {a b : Term Sig Γ τ}
    (h : ContextConversion a b) : Proof (.equal a b) :=
  of_eqProof (contextual_conversion_sound h)

/-- The truth-valued form of full contextual conversion is material equivalence.
This uses equality elimination at truth type, not nullary Intensionality. -/
theorem contextual_equivalence {Γ : Ctx} {p q : Term Sig Γ RTy.t}
    (h : ContextConversion p q) : Proof (.iff p q) :=
  Proof.eq_iff (contextual_conversion h)

#print axioms equality_coextension
#print axioms zeta_eq
#print axioms of_eqProof
#print axioms contextual_conversion
#print axioms contextual_equivalence

end Classicism.Meta.Research.BetaIdentity.PositiveArityModalBridge
