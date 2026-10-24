import Classicism.Semantics.BooleanValuedSoundness

/-!
# Designated truth at a Boolean atom

Ordinary external metatheory. A designated atom supplies ordinary quantifier
truth, including an actual witness for a designated-true existential. Optional
axioms need only be true at that atom. Subst's logical-only side derivations
still use Boolean-valued soundness to obtain equality under every assignment;
we never turn an optional designated truth into equality with Boolean top.

Source: full-boolean-valued-atom-and-atomless.md §§1–2, 4 (unpaginated), whose
construction provenance is preserved in BooleanValued.lean. The proofs here
are original formalization (misc); no forcing or selector result is assumed.
-/

namespace Classicism.Meta.BooleanValued
noncomputable section

variable {Sig : Signature} {B : Type} [CompleteBooleanAlgebra B]

/-- A nonzero atom, stated without relying on a second library's atom convention. -/
def TruthAtom (a : B) : Prop :=
  a ≠ ⊥ ∧ ∀ b : B, b ≤ a → b = ⊥ ∨ b = a

theorem atom_not_bot {a : B} (ha : TruthAtom a) : ¬ a ≤ ⊥ :=
  fun h => ha.1 (le_antisymm h bot_le)

theorem atom_crisp {a : B} (ha : TruthAtom a) {A : Type} (x y : A) :
    a ≤ (crisp x y : B) ↔ x = y := by
  classical
  by_cases e : x = y
  · subst y
    simp
  · rw [crisp_of_ne e]
    exact ⟨fun h => (atom_not_bot ha h).elim, fun h => (e h).elim⟩

theorem atom_compl {a : B} (ha : TruthAtom a) (p : B) :
    a ≤ pᶜ ↔ ¬ a ≤ p := by
  constructor
  · intro hn hp
    exact atom_not_bot ha (contradiction_bound a p hp hn)
  · intro hn
    have hz : a ⊓ p = ⊥ := by
      rcases ha.2 (a ⊓ p) inf_le_left with hz | he
      · exact hz
      · have hp : a ≤ p := by rw [← he]; exact inf_le_right
        exact (hn hp).elim
    have hb : a ⊓ p ≤ ⊥ := by simpa [hz]
    simpa using (inf_residuation a p ⊥).1 hb

theorem atom_inf (a p q : B) : a ≤ p ⊓ q ↔ a ≤ p ∧ a ≤ q :=
  ⟨fun h => ⟨le_trans h inf_le_left, le_trans h inf_le_right⟩,
    fun h => le_inf h.1 h.2⟩

theorem atom_sup {a : B} (ha : TruthAtom a) (p q : B) :
    a ≤ p ⊔ q ↔ a ≤ p ∨ a ≤ q := by
  classical
  constructor
  · intro h
    by_cases hp : a ≤ p
    · exact Or.inl hp
    · by_cases hq : a ≤ q
      · exact Or.inr hq
      · have hpn := (atom_compl ha p).2 hp
        have hqn := (atom_compl ha q).2 hq
        have hz : a ≤ ⊥ := join_elimination a p q ⊥ h
          (contradiction_bound (p ⊓ a) p inf_le_left (le_trans inf_le_right hpn))
          (contradiction_bound (q ⊓ a) q inf_le_left (le_trans inf_le_right hqn))
        exact (atom_not_bot ha hz).elim
  · intro h
    exact h.elim (fun h => le_trans h le_sup_left) (fun h => le_trans h le_sup_right)

theorem atom_iInf {A : Type} (a : B) (F : A → B) :
    a ≤ (⨅ x, F x) ↔ ∀ x, a ≤ F x :=
  ⟨fun h x => le_trans h (iInf_le F x), fun h => le_iInf h⟩

/-- Complete primeness is proved from atomicity and Boolean completeness. -/
theorem atom_iSup {a : B} (ha : TruthAtom a) {A : Type} (F : A → B) :
    a ≤ (⨆ x, F x) ↔ ∃ x, a ≤ F x := by
  classical
  constructor
  · intro h
    by_contra hn
    have hF : ∀ x, F x ⊓ a ≤ ⊥ := by
      intro x
      have hc : a ≤ (F x)ᶜ :=
        (atom_compl ha (F x)).2 (fun hx => hn ⟨x, hx⟩)
      exact contradiction_bound (F x ⊓ a) (F x) inf_le_left (le_trans inf_le_right hc)
    exact atom_not_bot ha (supremum_elimination a F ⊥ h hF)
  · rintro ⟨x, hx⟩
    exact le_trans hx (le_iSup F x)

def HoldsAt (I : Interpretation Sig B) (a : B) {Γ : Ctx}
    (p : Formula Sig Γ) (env : IEnv (Dom I.E B) Γ) : Prop := a ≤ eval I p env

def ContextHoldsAt (I : Interpretation Sig B) (a : B) {Γ : Ctx}
    (Δ : List (Formula Sig Γ)) (env : IEnv (Dom I.E B) Γ) : Prop :=
  ∀ p ∈ Δ, HoldsAt I a p env

def AxiomsHoldAt (I : Interpretation Sig B) (a : B) (Ax : AxiomSet Sig) : Prop :=
  ∀ p, Ax p → HoldsAt I a p .nil

theorem context_holds_weaken (I : Interpretation Sig B) (a : B) {Γ : Ctx} {σ : Ty}
    (Δ : List (Formula Sig Γ)) (x : Dom I.E B σ) (env : IEnv (Dom I.E B) Γ)
    (h : ContextHoldsAt I a Δ env) :
    ContextHoldsAt I a (Hyps.weaken Δ) (.cons x env) := by
  intro p hp
  rw [Hyps.weaken, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  change a ≤ eval I q.weaken (.cons x env)
  rw [eval_weaken]
  exact h q hq

theorem context_holds_cons (I : Interpretation Sig B) (a : B) {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} {env : IEnv (Dom I.E B) Γ}
    (hp : HoldsAt I a p env) (hΔ : ContextHoldsAt I a Δ env) :
    ContextHoldsAt I a (p :: Δ) env := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hp
  · exact hΔ q hq

/-- All rules preserve designated truth of optional axioms and local premises.
Only logical axioms are fed to Boolean-top soundness in the Subst branch. -/
theorem sound_at (I : Interpretation Sig B) [Nonempty I.E] {a : B} (ha : TruthAtom a) :
    ∀ {Ax : AxiomSet Sig}, AxiomsHoldAt I a Ax →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}, Derivable Ax Δ p →
      ∀ env : IEnv (Dom I.E B) Γ, ContextHoldsAt I a Δ env → HoldsAt I a p env
  | _, _, _, _, _, .hyp h, _, hΔ => hΔ _ h
  | _, hAx, _, _, _, .ax h, env, _ => by
    unfold HoldsAt
    rw [eval_close]
    exact hAx _ h
  | _, hAx, _, _, _, .andI h₁ h₂, env, hΔ =>
    le_inf (sound_at I ha hAx h₁ env hΔ) (sound_at I ha hAx h₂ env hΔ)
  | _, hAx, _, _, _, .andE₁ h, env, hΔ =>
    le_trans (sound_at I ha hAx h env hΔ) inf_le_left
  | _, hAx, _, _, _, .andE₂ h, env, hΔ =>
    le_trans (sound_at I ha hAx h env hΔ) inf_le_right
  | _, hAx, _, _, _, .orI₁ h, env, hΔ =>
    le_trans (sound_at I ha hAx h env hΔ) le_sup_left
  | _, hAx, _, _, _, .orI₂ h, env, hΔ =>
    le_trans (sound_at I ha hAx h env hΔ) le_sup_right
  | _, hAx, _, _, _, .orE h h₁ h₂, env, hΔ =>
    ((atom_sup ha _ _).1 (sound_at I ha hAx h env hΔ)).elim
      (fun hp => sound_at I ha hAx h₁ env (context_holds_cons I a hp hΔ))
      (fun hq => sound_at I ha hAx h₂ env (context_holds_cons I a hq hΔ))
  | _, hAx, _, _, _, .notI h₁ h₂, env, hΔ => by
    apply (atom_compl ha _).2
    intro hp
    have hΔ' := context_holds_cons I a hp hΔ
    exact atom_not_bot ha (contradiction_bound a _
      (sound_at I ha hAx h₁ env hΔ') (sound_at I ha hAx h₂ env hΔ'))
  | _, hAx, _, _, _, .notE h₁ h₂, env, hΔ =>
    (atom_not_bot ha (contradiction_bound a _
      (sound_at I ha hAx h₁ env hΔ) (sound_at I ha hAx h₂ env hΔ))).elim
  | _, _, _, _, _, .em p, env, _ => by
    change a ≤ eval I p env ⊔ (eval I p env)ᶜ
    simp
  | _, hAx, _, _, _, .allE h t, env, hΔ =>
    le_trans (sound_at I ha hAx h env hΔ) (iInf_le _ (eval I t env))
  | _, hAx, _, _, _, .allI h, env, hΔ =>
    le_iInf fun x => sound_at I ha hAx h (.cons x env) (context_holds_weaken I a _ x env hΔ)
  | _, hAx, _, _, _, .exI t h, env, hΔ =>
    le_trans (sound_at I ha hAx h env hΔ) (le_iSup _ (eval I t env))
  | _, hAx, _, _, _, .exE (F := F) (r := r) h h', env, hΔ => by
    obtain ⟨x, hx⟩ := (atom_iSup ha (eval I F env)).1 (sound_at I ha hAx h env hΔ)
    have hx' : HoldsAt I a (Term.app F.weaken (Term.var Var.zero)) (.cons x env) := by
      change a ≤ eval I F.weaken (.cons x env) x
      rw [eval_weaken]
      exact hx
    have hr := sound_at I ha hAx h' (.cons x env)
      (context_holds_cons I a hx' (context_holds_weaken I a _ x env hΔ))
    change a ≤ eval I r.weaken (.cons x env) at hr
    rw [eval_weaken] at hr
    exact hr
  | _, _, _, _, _, .refl t, env, _ => by
    change a ≤ crisp (eval I t env) (eval I t env)
    simp
  | _, hAx, _, _, _, .ll (a := t) (b := u) F h₁ h₂, env, hΔ => by
    have e := (atom_crisp ha (eval I t env) (eval I u env)).1
      (sound_at I ha hAx h₁ env hΔ)
    have hf := sound_at I ha hAx h₂ env hΔ
    change a ≤ eval I F env (eval I t env) at hf
    rw [e] at hf
    exact hf
  | _, hAx, _, _, _, .conv h c, env, hΔ => by
    unfold HoldsAt
    rw [← conv_value I c env]
    exact sound_at I ha hAx h env hΔ
  | Ax, hAx, _, _, _, .subst (P := P) (Q := Q) K h₁ h₂ h₃, env, hΔ => by
    have hL : AxiomsValid I Ax.logical := fun p hp => C_axioms_valid I p hp.2
    have e : ∀ env', eval I P env' = eval I Q env' := by
      intro env'
      apply le_antisymm
      · simpa [contextValue] using sound I hL h₁ env'
      · simpa [contextValue] using sound I hL h₂ env'
    unfold HoldsAt
    rw [← hole_value I K e env]
    exact sound_at I ha hAx h₃ env hΔ

theorem theorem_holds_at (I : Interpretation Sig B) [Nonempty I.E]
    {a : B} (ha : TruthAtom a) {Ax : AxiomSet Sig} (hAx : AxiomsHoldAt I a Ax)
    {p : Sentence Sig} (h : Theorem Ax p) : HoldsAt I a p .nil :=
  sound_at I ha hAx h .nil (fun _ h => nomatch h)

theorem C_axioms_hold_at (I : Interpretation Sig B) [Nonempty I.E] (a : B) :
    AxiomsHoldAt I a C.axioms := by
  intro p hp
  change a ≤ eval I p .nil
  rw [C_axioms_valid I p hp]
  exact le_top

end
end Classicism.Meta.BooleanValued
