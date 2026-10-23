import Classicism.Semantics.BooleanValued

/-!
# Soundness of the actual C calculus in a full complete Boolean algebra

Ordinary external metatheory, not a shallow C derivation. Soundness is the
inequality `meet(values of hypotheses) ≤ value(conclusion)`; merely assuming
that each hypothesis has value top is insufficient for the induction.
In particular, disjunction and existential elimination use Boolean algebra
distributivity, not a claim that a join has a witness with value top.

The Subst case uses exactly `Derivable`'s two logical-only side derivations.
Their singleton-context inequalities give equality at every assignment;
`hole_value` then transfers values even when the hole lies under binders.
The existence axiom is discharged from external nonemptiness of the e-domain.

Sources: full-boolean-valued-atom-and-atomless.md §2, and
max-atomicity-selector-audit.md §9 (unpaginated local notes). Construction
provenance is preserved in BooleanValued.lean. The present rule-by-rule proof
is original formalization (misc).
-/

namespace Classicism.Meta.BooleanValued
noncomputable section

variable {Sig : Signature} {B : Type} [CompleteBooleanAlgebra B]

/-- Finite conjunction of the actual derivation's hypothesis values. -/
def contextValue (I : Interpretation Sig B) {Γ : Ctx} :
    List (Formula Sig Γ) → IEnv (Dom I.E B) Γ → B
  | [], _ => ⊤
  | p :: Δ, env => eval I p env ⊓ contextValue I Δ env

theorem context_le_member (I : Interpretation Sig B) {Γ : Ctx}
    {p : Formula Sig Γ} : ∀ (Δ : List (Formula Sig Γ)), p ∈ Δ →
      ∀ env : IEnv (Dom I.E B) Γ, contextValue I Δ env ≤ eval I p env
  | [], h, _ => nomatch h
  | q :: Δ, h, env => by
    rcases List.mem_cons.1 h with e | h
    · subst e
      exact inf_le_left
    · exact le_trans inf_le_right (context_le_member I Δ h env)

theorem context_weaken (I : Interpretation Sig B) {Γ : Ctx} {σ : Ty}
    (Δ : List (Formula Sig Γ)) (x : Dom I.E B σ) (env : IEnv (Dom I.E B) Γ) :
    contextValue I (Hyps.weaken Δ) (.cons x env) = contextValue I Δ env := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih =>
    change eval I p.weaken (.cons x env) ⊓ contextValue I (Hyps.weaken Δ) (.cons x env) = _
    rw [eval_weaken, ih]
    rfl

/-- Elementary Boolean residuation, used to avoid an infinitary-witness inference. -/
theorem inf_residuation (a b c : B) : a ⊓ b ≤ c ↔ a ≤ bᶜ ⊔ c := by
  constructor
  · intro h
    calc
      a = a ⊓ (b ⊔ bᶜ) := by simp
      _ = (a ⊓ b) ⊔ (a ⊓ bᶜ) := by rw [inf_sup_left]
      _ ≤ c ⊔ bᶜ := sup_le_sup h inf_le_right
      _ = bᶜ ⊔ c := sup_comm _ _
  · intro h
    calc
      a ⊓ b ≤ (bᶜ ⊔ c) ⊓ b := inf_le_inf_right b h
      _ = (bᶜ ⊓ b) ⊔ (c ⊓ b) := by rw [inf_sup_right]
      _ = c ⊓ b := by simp
      _ ≤ c := inf_le_left

theorem join_elimination (d p q r : B) (h : d ≤ p ⊔ q)
    (hp : p ⊓ d ≤ r) (hq : q ⊓ d ≤ r) : d ≤ r := by
  have hs : p ⊔ q ≤ dᶜ ⊔ r :=
    sup_le ((inf_residuation p d r).1 hp) ((inf_residuation q d r).1 hq)
  have ht := (inf_residuation (p ⊔ q) d r).2 hs
  calc
    d = d ⊓ d := (inf_idem d).symm
    _ ≤ (p ⊔ q) ⊓ d := inf_le_inf_right d h
    _ ≤ r := ht

theorem supremum_elimination {A : Type} (d : B) (F : A → B) (r : B)
    (h : d ≤ ⨆ x, F x) (hF : ∀ x, F x ⊓ d ≤ r) : d ≤ r := by
  have hs : (⨆ x, F x) ≤ dᶜ ⊔ r :=
    iSup_le fun x => (inf_residuation (F x) d r).1 (hF x)
  have ht := (inf_residuation (⨆ x, F x) d r).2 hs
  calc
    d = d ⊓ d := (inf_idem d).symm
    _ ≤ (⨆ x, F x) ⊓ d := inf_le_inf_right d h
    _ ≤ r := ht

theorem contradiction_bound (d p : B) (hp : d ≤ p) (hn : d ≤ pᶜ) : d ≤ ⊥ := by
  have h := le_inf hp hn
  simpa using h

theorem negation_introduction (d p q : B)
    (hq : p ⊓ d ≤ q) (hn : p ⊓ d ≤ qᶜ) : d ≤ pᶜ := by
  have hz : d ⊓ p ≤ ⊥ := by
    simpa [inf_comm] using contradiction_bound (p ⊓ d) q hq hn
  simpa using (inf_residuation d p ⊥).1 hz

def AxiomsValid (I : Interpretation Sig B) (Ax : AxiomSet Sig) : Prop :=
  ∀ a, Ax a → eval I a .nil = ⊤

/-- Rule-by-rule soundness, including the real logical-side-condition Subst rule. -/
theorem sound (I : Interpretation Sig B) :
    ∀ {Ax : AxiomSet Sig}, AxiomsValid I Ax →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}, Derivable Ax Δ p →
      ∀ env : IEnv (Dom I.E B) Γ, contextValue I Δ env ≤ eval I p env
  | _, _, _, _, _, .hyp h, env => context_le_member I _ h env
  | _, hAx, _, _, _, .ax h, env => by
    rw [eval_close, hAx _ h]
    exact le_top
  | _, hAx, _, _, _, .andI h₁ h₂, env =>
    le_inf (sound I hAx h₁ env) (sound I hAx h₂ env)
  | _, hAx, _, _, _, .andE₁ h, env => le_trans (sound I hAx h env) inf_le_left
  | _, hAx, _, _, _, .andE₂ h, env => le_trans (sound I hAx h env) inf_le_right
  | _, hAx, _, _, _, .orI₁ h, env => le_trans (sound I hAx h env) le_sup_left
  | _, hAx, _, _, _, .orI₂ h, env => le_trans (sound I hAx h env) le_sup_right
  | _, hAx, _, _, _, .orE h h₁ h₂, env =>
    join_elimination _ _ _ _ (sound I hAx h env)
      (sound I hAx h₁ env) (sound I hAx h₂ env)
  | _, hAx, _, _, _, .notI h₁ h₂, env =>
    negation_introduction _ _ _ (sound I hAx h₁ env) (sound I hAx h₂ env)
  | _, hAx, _, _, _, .notE h₁ h₂, env =>
    le_trans (contradiction_bound _ _ (sound I hAx h₁ env) (sound I hAx h₂ env)) bot_le
  | _, _, _, _, _, .em p, env => by
    change contextValue I _ env ≤ eval I p env ⊔ (eval I p env)ᶜ
    simp
  | _, hAx, _, _, _, .allE h a, env =>
    le_trans (sound I hAx h env) (iInf_le _ (eval I a env))
  | _, hAx, _, _, _, .allI h, env => by
    apply le_iInf
    intro x
    have hx := sound I hAx h (.cons x env)
    rw [context_weaken] at hx
    exact hx
  | _, hAx, _, _, _, .exI a h, env =>
    le_trans (sound I hAx h env) (le_iSup _ (eval I a env))
  | _, hAx, _, _, _, .exE (F := F) (r := r) h h', env => by
    apply supremum_elimination _ (eval I F env) _ (sound I hAx h env)
    intro x
    have hx := sound I hAx h' (.cons x env)
    change eval I F.weaken (.cons x env) x ⊓
      contextValue I (Hyps.weaken _) (.cons x env) ≤ eval I r.weaken (.cons x env) at hx
    rw [eval_weaken, context_weaken, eval_weaken] at hx
    exact hx
  | _, _, _, _, _, .refl a, env => by
    change contextValue I _ env ≤ crisp (eval I a env) (eval I a env)
    rw [crisp_self]
    exact le_top
  | _, hAx, _, _, _, .ll (a := a) (b := b) F h₁ h₂, env => by
    classical
    by_cases e : eval I a env = eval I b env
    · have hf := sound I hAx h₂ env
      change contextValue I _ env ≤ eval I F env (eval I a env) at hf
      rw [e] at hf
      exact hf
    · have hz := sound I hAx h₁ env
      change contextValue I _ env ≤ crisp (eval I a env) (eval I b env) at hz
      rw [crisp_of_ne e] at hz
      exact le_trans hz bot_le
  | _, hAx, _, _, _, .conv h c, env => by
    rw [← conv_value I c env]
    exact sound I hAx h env
  | Ax, hAx, _, _, _, .subst (P := P) (Q := Q) K h₁ h₂ h₃, env => by
    have hL : AxiomsValid I Ax.logical := fun a ha => hAx a ha.1
    have e : ∀ env', eval I P env' = eval I Q env' := by
      intro env'
      apply le_antisymm
      · simpa [contextValue] using sound I hL h₁ env'
      · simpa [contextValue] using sound I hL h₂ env'
    rw [← hole_value I K e env]
    exact sound I hAx h₃ env

theorem theorem_value (I : Interpretation Sig B) {Ax : AxiomSet Sig}
    (hAx : AxiomsValid I Ax) {p : Sentence Sig} (h : Theorem Ax p) :
    eval I p .nil = ⊤ :=
  le_antisymm le_top (sound I hAx h .nil)

/-- The only logical axiom is true when the individual domain is nonempty. -/
theorem C_axioms_valid (I : Interpretation Sig B) [Nonempty I.E] :
    AxiomsValid I C.axioms := by
  intro a h
  rw [show a = existence_e from h]
  change (⨆ x : I.E, (crisp x x : B)) = ⊤
  apply le_antisymm le_top
  obtain ⟨x⟩ := ‹Nonempty I.E›
  calc
    ⊤ = (crisp x x : B) := (crisp_self x).symm
    _ ≤ ⨆ y : I.E, crisp y y := le_iSup (fun y : I.E => (crisp y y : B)) x

/-- C soundness is a conclusion, with no assumed soundness premise. -/
theorem C_sound (I : Interpretation Sig B) [Nonempty I.E]
    {p : Sentence Sig} (h : C.Theorem p) : eval I p .nil = ⊤ :=
  theorem_value I (C_axioms_valid I) h

theorem C_minus_sound (I : Interpretation Sig B)
    {p : Sentence Sig} (h : C.TheoremMinus p) : eval I p .nil = ⊤ :=
  theorem_value I (fun _ h => h.elim) h

/-- A non-top value is a genuine obstruction to C-theoremhood. -/
theorem not_C_theorem (I : Interpretation Sig B) [Nonempty I.E]
    {p : Sentence Sig} (hp : eval I p .nil ≠ ⊤) : ¬ C.Theorem p :=
  fun h => hp (C_sound I h)

theorem unequal_values_not_identity (I : Interpretation Sig B) [Nonempty I.E]
    [Nontrivial B] {σ : Ty} (a b : Term Sig [] σ)
    (hne : eval I a .nil ≠ eval I b .nil) : ¬ C.Theorem (Term.eq' a b) := by
  apply not_C_theorem I
  change (crisp (eval I a .nil) (eval I b .nil) : B) ≠ ⊤
  rw [crisp_of_ne hne]
  exact bot_ne_top

theorem bottom_not_C_theorem (I : Interpretation Sig B) [Nonempty I.E]
    [Nontrivial B] : ¬ C.Theorem (Term.bot : Sentence Sig) := by
  apply not_C_theorem I
  rw [eval_bot]
  exact bot_ne_top

end
end Classicism.Meta.BooleanValued
