import Classicism.Syntax.Term

/-!
# Recursive syntax of the actual-world core

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
sections 2--3 and 7 (original research, misc, 22 October 2026, unpaginated).

These are metalinguistic constructions on the existing `Ty`, `RTy`, and
`Term` syntax. Every constructed predicate and translated term is an actual
term of that language. No external function domain is inserted. Type variables
are treated as base sorts; interpretation claims concern closed types.

This module supplies the recursive syntax and its renaming laws. It does not
yet claim the semantic induction establishing membership of every translated
term in the current core, or preservation of beta/eta conversion. In particular,
mere typing of `translate` is not the missing interpretation theorem.
-/

namespace Classicism.Meta.ActualityCoreSyntax

variable {Sig : Signature}

mutual
  /-- Membership in the current core at an original type. -/
  def domain (σ : Ty) {Γ : Ctx} (w : Formula Sig Γ) :
      Term Sig Γ (σ ⇒ RTy.t) :=
    match σ with
    | .e => .lam w.weaken
    | .var _ => .lam w.weaken
    | .rel ρ => .lam (Term.conj w.weaken
        (Term.leR ρ .v0 (support ρ w.weaken)))

  /-- The supported top at a relational type, recursively restricting every
  argument to its own core domain. -/
  def support (ρ : RTy) {Γ : Ctx} (w : Formula Sig Γ) : Term Sig Γ ρ :=
    match ρ with
    | .t => w
    | .arr σ τ => .lam (.app (.app (.andR τ)
        (.app (.constR τ) (.app (domain σ w.weaken) .v0)))
        (support τ w.weaken))
end

/-- Normalization at a relational type is intersection with its supported top. -/
def cut (ρ : RTy) {Γ : Ctx} (w : Formula Sig Γ) (a : Term Sig Γ ρ) :
    Term Sig Γ ρ := .app (.app (.andR ρ) (support ρ w)) a

/-- Individuals are unchanged. Relational objects are normalized. This is a
metalinguistic case distinction, not an individual-output function type. -/
def normalize (σ : Ty) {Γ : Ctx} (w : Formula Sig Γ) (a : Term Sig Γ σ) :
    Term Sig Γ σ :=
  match σ with
  | .e => a
  | .var _ => a
  | .rel ρ => cut ρ w a

/-- A core universal quantifier first restricts its bound variable, then cuts
the resulting operation to the core predicate domain. -/
def universal (σ : Ty) {Γ : Ctx} (w : Formula Sig Γ) :
    Term Sig Γ ((σ ⇒ RTy.t) ⇒ RTy.t) :=
  cut _ w (.lam (Term.forall' (Term.imp
    (.app (domain σ w.weaken.weaken) .v0) (.app .v1 .v0))))

/-- The corresponding existential quantifier. -/
def existential (σ : Ty) {Γ : Ctx} (w : Formula Sig Γ) :
    Term Sig Γ ((σ ⇒ RTy.t) ⇒ RTy.t) :=
  cut _ w (.lam (Term.exists' (Term.conj
    (.app (domain σ w.weaken.weaken) .v0) (.app .v1 .v0))))

/-- Translate every constructor of the actual intrinsically typed language.
Relational outputs are normalized at application as well as abstraction, so
domain membership is built into the translation. Application preservation
still requires the section theorem: it cannot be inferred from typing alone.
The local extensional box is the identity on core truth values, lifted
pointwise. Using the ambient box here would instead test identity with the
ambient top, which is generally the wrong truth value for this core. -/
def translate : ∀ {Γ : Ctx} {σ : Ty},
    Formula Sig Γ → Term Sig Γ σ → Term Sig Γ σ
  | _, _, _, .var v => .var v
  | _, _, w, .const c => normalize (Sig.typeOf c) w (.const c)
  | _, _, w, .app f a => cut _ w (.app (translate w f) (translate w a))
  | _, _, w, .lam b => cut _ w (.lam (translate w.weaken b))
  | _, _, w, .and => cut _ w .and
  | _, _, w, .or => cut _ w .or
  | _, _, w, .not => cut _ w .not
  | _, _, w, .all σ => universal σ w
  | _, _, w, .ex σ => existential σ w
  | _, _, w, .eq σ => cut _ w (.eq σ)
  | _, _, w, .constR ρ => cut _ w (.constR ρ)
  | _, _, w, .negR ρ => cut _ w (.negR ρ)
  | _, _, w, .andR ρ => cut _ w (.andR ρ)
  | _, _, w, .orR ρ => cut _ w (.orR ρ)
  | _, _, w, .coextR ρ => cut _ w (.coextR ρ)
  | _, _, w, .inclR ρ => cut _ w (.inclR ρ)
  | _, _, w, .boxR ρ => cut _ w (.lam (.var .zero))

/-- All the variables of a context, retaining their actual type indices. -/
def variables : (Γ : Ctx) → List (Σ σ : Ty, Var Γ σ)
  | [] => []
  | σ :: Γ => ⟨σ, .zero⟩ ::
      (variables Γ).map (fun ⟨τ, v⟩ => ⟨τ, .succ v⟩)

/-- A context is interpreted by requiring each original variable to belong
to its recursively defined core domain. These are formulas in the original
context, not an external assignment of full function spaces. -/
def context (Γ : Ctx) (w : Formula Sig Γ) : List (Formula Sig Γ) :=
  (variables Γ).map (fun ⟨σ, v⟩ => .app (domain σ w) (.var v))

theorem mem_variables {Γ : Ctx} {σ : Ty} (v : Var Γ σ) :
    ⟨σ, v⟩ ∈ variables Γ := by
  induction v with
  | zero => exact List.mem_cons_self
  | succ v ih =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

theorem mem_context {Γ : Ctx} {σ : Ty} (w : Formula Sig Γ) (v : Var Γ σ) :
    .app (domain σ w) (.var v) ∈ context Γ w :=
  List.mem_map.mpr ⟨⟨σ, v⟩, mem_variables v, rfl⟩

/-- Renaming past a binder preserves the supplied world parameter. -/
theorem rename_weaken {Γ Δ : Ctx} {σ τ : Ty}
    (r : Ren Γ Δ) (a : Term Sig Γ σ) :
    (a.weaken (τ := τ)).rename (Ren.lift r) = (a.rename r).weaken := by
  simp only [Term.weaken, Term.rename_rename]
  rfl

mutual
  theorem domain_rename (σ : Ty) {Γ Δ : Ctx}
      (w : Formula Sig Γ) (r : Ren Γ Δ) :
      (domain σ w).rename r = domain σ (w.rename r) := by
    cases σ with
    | e => simp only [domain, Term.rename_lam, rename_weaken]
    | var _ => simp only [domain, Term.rename_lam, rename_weaken]
    | rel ρ =>
      simp only [domain, Term.conj, Term.leR, Term.eq', Term.rename_lam,
        Term.rename_app, Term.rename_and, Term.rename_eq, Term.rename_orR,
        Term.rename_var, Ren.lift_zero, rename_weaken, support_rename ρ]

  theorem support_rename (ρ : RTy) {Γ Δ : Ctx}
      (w : Formula Sig Γ) (r : Ren Γ Δ) :
      (support ρ w).rename r = support ρ (w.rename r) := by
    cases ρ with
    | t => rfl
    | arr σ τ =>
      simp only [support, Term.rename_lam, Term.rename_app,
        Term.rename_andR, Term.rename_constR, Term.rename_var,
        Ren.lift_zero, domain_rename σ, support_rename τ, rename_weaken]
end

theorem cut_rename (ρ : RTy) {Γ Δ : Ctx} (w : Formula Sig Γ)
    (a : Term Sig Γ ρ) (r : Ren Γ Δ) :
    (cut ρ w a).rename r = cut ρ (w.rename r) (a.rename r) := by
  simp only [cut, Term.rename_app, Term.rename_andR, support_rename]

theorem normalize_rename (σ : Ty) {Γ Δ : Ctx} (w : Formula Sig Γ)
    (a : Term Sig Γ σ) (r : Ren Γ Δ) :
    (normalize σ w a).rename r = normalize σ (w.rename r) (a.rename r) := by
  cases σ with
  | e => rfl
  | var _ => rfl
  | rel ρ => exact cut_rename ρ w a r

theorem universal_rename (σ : Ty) {Γ Δ : Ctx} (w : Formula Sig Γ)
    (r : Ren Γ Δ) :
    (universal σ w).rename r = universal σ (w.rename r) := by
  simp only [universal, cut_rename, Term.rename_lam, Term.forall', Term.imp,
    Term.disj, Term.neg, Term.rename_app, Term.rename_all, Term.rename_or,
    Term.rename_not, Term.rename_var, Ren.lift_zero, Ren.lift_succ,
    domain_rename, rename_weaken]

theorem existential_rename (σ : Ty) {Γ Δ : Ctx} (w : Formula Sig Γ)
    (r : Ren Γ Δ) :
    (existential σ w).rename r = existential σ (w.rename r) := by
  simp only [existential, cut_rename, Term.rename_lam, Term.exists', Term.conj,
    Term.rename_app, Term.rename_ex, Term.rename_and, Term.rename_var,
    Ren.lift_zero, Ren.lift_succ, domain_rename, rename_weaken]

/-- Translation commutes with arbitrary context renaming, including weakening
under quantifiers and abstractions. This concerns syntax, not an appeal to
extensionality of the object language. -/
theorem translate_rename : ∀ {Γ Δ : Ctx} {σ : Ty} (w : Formula Sig Γ)
    (a : Term Sig Γ σ) (r : Ren Γ Δ),
    (translate w a).rename r = translate (w.rename r) (a.rename r)
  | _, _, _, _, .var _, _ => rfl
  | _, _, _, w, .const c, r => normalize_rename _ w (.const c) r
  | _, _, _, w, .app f a, r => by
    simp only [translate, cut_rename, Term.rename_app, translate_rename w f r,
      translate_rename w a r]
  | _, _, _, w, .lam b, r => by
    simp only [translate, cut_rename, Term.rename_lam,
      translate_rename w.weaken b (Ren.lift r), rename_weaken]
  | _, _, _, w, .and, r => cut_rename _ w .and r
  | _, _, _, w, .or, r => cut_rename _ w .or r
  | _, _, _, w, .not, r => cut_rename _ w .not r
  | _, _, _, w, .all σ, r => universal_rename σ w r
  | _, _, _, w, .ex σ, r => existential_rename σ w r
  | _, _, _, w, .eq σ, r => cut_rename _ w (.eq σ) r
  | _, _, _, w, .constR ρ, r => cut_rename _ w (.constR ρ) r
  | _, _, _, w, .negR ρ, r => cut_rename _ w (.negR ρ) r
  | _, _, _, w, .andR ρ, r => cut_rename _ w (.andR ρ) r
  | _, _, _, w, .orR ρ, r => cut_rename _ w (.orR ρ) r
  | _, _, _, w, .coextR ρ, r => cut_rename _ w (.coextR ρ) r
  | _, _, _, w, .inclR ρ, r => cut_rename _ w (.inclR ρ) r
  | _, _, _, w, .boxR ρ, r => cut_rename _ w (.lam (.var .zero)) r

end Classicism.Meta.ActualityCoreSyntax
