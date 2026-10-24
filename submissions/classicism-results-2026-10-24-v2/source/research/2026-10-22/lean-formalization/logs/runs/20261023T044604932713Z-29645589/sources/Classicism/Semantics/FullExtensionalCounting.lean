import Classicism.Semantics.FullExtensionalInfinity
import Mathlib.Data.List.FinRange

/-!
# Actual counting syntax in the full one-world interpretation

Adapts the already existing Semantics/Counting.lean block/tuple argument to
`Term.denote`, without assuming a categorical model bridge. It proves the exact
Infinity-schema instances in the Nat single-predicate model. All induction here
is external syntax/finite-tuple metatheory, not induction asserted within C.

Source: central-questions-audit.md, MN's individual Infinity-schema verdict
(original research, unpaginated, misc). The proof organization follows the
existing Semantics/Counting.lean, block environments through holds_count.
-/

namespace Classicism.Meta.FullExtensional
noncomputable section
variable {Sig : Signature}

def blockEnv {E : Type} {σ : Ty} : ∀ (n : Nat) {Γ : Ctx},
    (Fin n → σ.denote E) → Env E Γ → Env E (Ctx.block (List.replicate n σ) Γ)
  | 0, _, _, env => env
  | n + 1, _, f, env => blockEnv n (fun i => f i.succ) (.cons (f 0) env)

theorem blockEnv_var {E : Type} {σ : Ty} : ∀ (n : Nat) {Γ : Ctx}
    (f : Fin n → σ.denote E) (env : Env E Γ) {τ : Ty} (v : Var Γ τ),
    (Ren.wkBlock (List.replicate n σ) _ v).denote (blockEnv n f env) = v.denote env
  | 0, _, _, _, _, _ => rfl
  | n + 1, _, f, env, _, v => blockEnv_var n (fun i => f i.succ) (.cons (f 0) env) (.succ v)

def semList (I : Interp Sig) {Γ : Ctx} {σ : Ty} : ∀ n : Nat,
    Terms Sig Γ (List.replicate n σ) → Env I.D Γ → List (σ.denote I.D)
  | 0, _, _ => []
  | n + 1, xs, env => xs.head.denote I env :: semList I n xs.tail env

theorem semList_vars (I : Interp Sig) {σ : Ty} : ∀ (n : Nat) {Γ : Ctx}
    (f : Fin n → σ.denote I.D) (env : Env I.D Γ),
    semList I n (Terms.vars (List.replicate n σ) Γ) (blockEnv n f env) = List.ofFn f
  | 0, _, _, _ => rfl
  | n + 1, Γ, f, env => by
    rw [List.ofFn_succ, ← semList_vars I n (fun i => f i.succ) (.cons (f 0) env)]
    change ((Term.var .zero : Term Sig (σ :: Γ) σ).rename (Ren.wkBlock (List.replicate n σ))).denote I
      (blockEnv n (fun i => f i.succ) (.cons (f 0) env)) :: _ = _
    rw [Term.denote_rename]
    congr 1
    change Var.denote Var.zero (Ren.denote _ _) = _
    rw [Var.denote_ren, blockEnv_var]

theorem denote_existsBlock (I : Interp Sig) {σ : Ty} : ∀ (n : Nat) {Γ : Ctx}
    (p : Formula Sig (Ctx.block (List.replicate n σ) Γ)) (env : Env I.D Γ),
    (Term.existsBlock (List.replicate n σ) p).denote I env ↔
      ∃ f : Fin n → σ.denote I.D, p.denote I (blockEnv n f env)
  | 0, _, _, _ => ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩
  | n + 1, _, p, env => by
    change (∃ x, (Term.existsBlock (List.replicate n σ) p).denote I (.cons x env)) ↔ _
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨f, hf⟩ := (denote_existsBlock I n p (.cons x env)).1 hx
      exact ⟨Fin.cons x f, hf⟩
    · rintro ⟨f, hf⟩
      exact ⟨f 0, (denote_existsBlock I n p (.cons (f 0) env)).2 ⟨fun i => f i.succ, hf⟩⟩

theorem denote_neAll (I : Interp Sig) {Γ : Ctx} {σ : Ty} (env : Env I.D Γ)
    (a : Term Sig Γ σ) : ∀ (n : Nat) (xs : Terms Sig Γ (List.replicate n σ)),
    (Term.neAll a n xs).denote I env ↔ ∀ v ∈ semList I n xs env, a.denote I env ≠ v
  | 0, _ => ⟨fun _ _ h => nomatch h, fun _ => Classical.em _⟩
  | n + 1, xs => by
    change (a.denote I env ≠ xs.head.denote I env ∧ (Term.neAll a n xs.tail).denote I env) ↔ _
    rw [denote_neAll I env a n xs.tail]
    simp [semList]

theorem denote_distinct (I : Interp Sig) {Γ : Ctx} {σ : Ty} (env : Env I.D Γ) :
    ∀ (n : Nat) (xs : Terms Sig Γ (List.replicate n σ)),
    (Term.distinct n xs).denote I env ↔ (semList I n xs env).Nodup
  | 0, _ => ⟨fun _ => List.nodup_nil, fun _ => Classical.em _⟩
  | n + 1, xs => by
    change ((Term.neAll xs.head n xs.tail).denote I env ∧
      (Term.distinct n xs.tail).denote I env) ↔ _
    rw [denote_neAll, denote_distinct]
    simp only [semList, List.nodup_cons]
    exact and_congr_left' ⟨fun H hm => H _ hm rfl, fun H v hv e => H (e ▸ hv)⟩

theorem denote_count (I : Interp Sig) (σ : Ty) (n : Nat) :
    (Term.existsBlock (List.replicate n σ)
      (Term.distinct n (Terms.vars (List.replicate n σ) []))).holds I ↔
      ∃ f : Fin n → σ.denote I.D, Function.Injective f := by
  change (Term.existsBlock (List.replicate n σ) _).denote I .nil ↔ _
  rw [denote_existsBlock]
  apply exists_congr
  intro f
  rw [denote_distinct, semList_vars, List.nodup_ofFn]

theorem nat_infinitySchema_e :
    (AxiomSet.infinityE SinglePredicateFull.signature).holds SinglePredicateFull.natModel := by
  rintro _ ⟨n, _, rfl⟩
  apply (denote_count SinglePredicateFull.natModel Ty.e n).2
  exact ⟨fun i => i.val, fun _ _ h => Fin.ext h⟩

end
end Classicism.Meta.FullExtensional
