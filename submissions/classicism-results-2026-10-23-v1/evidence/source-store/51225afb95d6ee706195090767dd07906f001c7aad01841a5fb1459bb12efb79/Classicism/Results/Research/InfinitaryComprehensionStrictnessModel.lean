import Classicism.Models.ChoiceFirstOrderAxiomTheory
import Classicism.Results.Research.InfinitaryComprehensionStrictness
import Classicism.Results.Research.InfinitaryComprehensionStrictnessTheory
import Classicism.Results.Research.InfinitaryComprehensionDiagonal

/-!
# Expanding a first-order Henkin hierarchy to the infinitary language

Source: `research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md`, Theorem 5.1, misc, 23 October 2026,
unpaginated. This is ordinary classical Lean metatheory.

Finite definable comprehension supplies application, two truth values and
the identity necessity operation. Every set-sized Boolean connective is
then interpreted using those same two propositions. No new predicate is
added to any relation domain. Thus the expanded grammar does not itself
force the infinitary Comprehension schema.

The first part is a generic construction from the actual finite-context
first-order comprehension schema, not an assumed expanded Henkin model.
All code in this research batch is awaiting compilation.
-/

namespace Classicism.Research.InfinitaryComprehension.Strictness

open Classicism.Meta
open Classicism.Meta.ChoiceFirstOrder
open Classicism.Meta.ChoiceFirstOrder.MathlibBridge
open Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory

/-- Atomicity stated directly for the admitted relation profiles. This does
not package arbitrary intersections or any other infinitary closure. -/
def ProfileAtomic (M : Henkin.Model) : Prop :=
  ∀ (Γ : Ctx) (R : M.Dom (RTy.ofArgs Γ)),
    (∃ xs w, M.truth (Henkin.uncurry M Γ R xs) w) →
    ∃ A : M.Dom (RTy.ofArgs Γ),
      (∃ xs w, M.truth (Henkin.uncurry M Γ A xs) w) ∧
      (∀ xs w, M.truth (Henkin.uncurry M Γ A xs) w →
        M.truth (Henkin.uncurry M Γ R xs) w) ∧
      ∀ B : M.Dom (RTy.ofArgs Γ),
        (∀ xs w, M.truth (Henkin.uncurry M Γ B xs) w →
          M.truth (Henkin.uncurry M Γ A xs) w) →
        (∀ xs w, ¬ M.truth (Henkin.uncurry M Γ B xs) w) ∨ B = A

namespace Expansion

variable (S : Structure) (hC : SmallComprehension S)

noncomputable def represent (Γ : Ctx) (ρ : RTy)
    (φ : SmallFormula (ρ.args ++ Γ)) (g : IEnv S.D Γ) : S.D (.rel ρ) :=
  Classical.choose (hC Γ ρ φ g)

theorem represent_spec (Γ : Ctx) (ρ : RTy)
    (φ : SmallFormula (ρ.args ++ Γ)) (g : IEnv S.D Γ) (a : Args S.D ρ) :
    S.rel ρ (represent S hC Γ ρ φ g) a ↔
      φ.Realize S (appendEnv (argsEnv ρ a) g) :=
  Classical.choose_spec (hC Γ ρ φ g) a

/-- Application is the finite definable section of the admitted relation. -/
def appMatrix (σ : Ty) (ρ : RTy) :
    SmallFormula (ρ.args ++ [σ, σ ⇒ ρ]) :=
  .rel (.arr σ ρ) (rightVar ρ.args (.succ .zero))
    (rightVar ρ.args .zero, prefixArgs [σ, σ ⇒ ρ] ρ)

noncomputable def app {σ : Ty} {ρ : RTy}
    (R : S.D (σ ⇒ ρ)) (x : S.D σ) : S.D ρ :=
  represent S hC [σ, σ ⇒ ρ] ρ (appMatrix σ ρ) (.cons x (.cons R .nil))

theorem app_spec {σ : Ty} {ρ : RTy}
    (R : S.D (σ ⇒ ρ)) (x : S.D σ) (a : Args S.D ρ) :
    S.rel ρ (app S hC R x) a ↔ S.rel (.arr σ ρ) R (x, a) := by
  rw [app, represent_spec]
  change S.rel (.arr σ ρ)
    ((appendEnv (argsEnv ρ a) (.cons x (.cons R .nil))).get
      (rightVar ρ.args (.succ .zero)))
    (((appendEnv (argsEnv ρ a) (.cons x (.cons R .nil))).get
      (rightVar ρ.args .zero)),
      mapArgs (fun _ v => (appendEnv (argsEnv ρ a)
        (.cons x (.cons R .nil))).get v) ρ (prefixArgs [σ, σ ⇒ ρ] ρ)) ↔ _
  rw [get_append_right, get_append_right, eval_prefixArgs]
  rfl

noncomputable def top : S.D Ty.t :=
  represent S hC [] .t (.neg .falsum) .nil

noncomputable def bot : S.D Ty.t :=
  represent S hC [] .t .falsum .nil

def trueAt (p : S.D Ty.t) : Prop := S.rel .t p PUnit.unit

theorem top_spec : trueAt S (top S hC) := by
  exact (represent_spec S hC [] .t (.neg .falsum) .nil PUnit.unit).2 (fun h => h)

theorem bot_spec : ¬ trueAt S (bot S hC) := by
  intro h
  exact (represent_spec S hC [] .t .falsum .nil PUnit.unit).1 h

noncomputable def value (p : Prop) : S.D Ty.t :=
  by
    classical
    exact if p then top S hC else bot S hC

theorem value_spec (p : Prop) : trueAt S (value S hC p) ↔ p := by
  classical
  by_cases hp : p
  · simp only [value, if_pos hp]
    exact ⟨fun _ => hp, fun _ => top_spec S hC⟩
  · simp only [value, if_neg hp]
    exact ⟨fun h => False.elim (bot_spec S hC h), fun h => False.elim (hp h)⟩

/-- Exactly two propositions, proved from profile extensionality. -/
theorem proposition_cases (p : S.D Ty.t) : p = top S hC ∨ p = bot S hC := by
  classical
  by_cases hp : trueAt S p
  · left
    apply S.rel_injective .t
    funext a
    cases a
    exact propext ⟨fun _ => top_spec S hC, fun _ => hp⟩
  · right
    apply S.rel_injective .t
    funext a
    cases a
    exact propext ⟨fun h => False.elim (hp h), fun h => False.elim (bot_spec S hC h)⟩

theorem top_ne_bot : top S hC ≠ bot S hC := by
  intro h
  exact bot_spec S hC (h ▸ top_spec S hC)

noncomputable def boxObj : S.D (RTy.t ⇒ RTy.t) :=
  represent S hC [] (.arr .t .t) (.rel .t .zero PUnit.unit) .nil

theorem box_spec (p : S.D Ty.t) :
    trueAt S (app S hC (boxObj S hC) p) ↔ trueAt S p := by
  unfold trueAt
  rw [app_spec, boxObj, represent_spec]
  rfl

/-- Actual interpretation of the whole infinitary grammar on unchanged sorts. -/
noncomputable def model : Henkin.Model where
  Dom := S.D
  World := PUnit
  truth p _ := trueAt S p
  app := app S hC
  top := top S hC
  bot := bot S hC
  neg p := value S hC (¬ trueAt S p)
  conj p q := value S hC (trueAt S p ∧ trueAt S q)
  disj p q := value S hC (trueAt S p ∨ trueAt S q)
  imp p q := value S hC (trueAt S p → trueAt S q)
  iff p q := value S hC (trueAt S p ↔ trueAt S q)
  eq a b := value S hC (a = b)
  boxObj := boxObj S hC
  iAnd _ p := value S hC (∀ i, trueAt S (p i))
  iOr _ p := value S hC (∃ i, trueAt S (p i))
  top_spec _ := top_spec S hC
  bot_spec _ := bot_spec S hC
  neg_spec p _ := value_spec S hC _
  conj_spec p q _ := value_spec S hC _
  disj_spec p q _ := value_spec S hC _
  imp_spec p q _ := value_spec S hC _
  iff_spec p q _ := value_spec S hC _
  eq_spec a b _ := value_spec S hC _
  box_spec p _ := (box_spec S hC p).trans
    ⟨fun h _ => h, fun h => h PUnit.unit⟩
  iAnd_spec _ p _ := value_spec S hC _
  iOr_spec _ p _ := value_spec S hC _

/-- Necessity is identity even for values of infinitary formulas. -/
theorem box_eq (p : S.D Ty.t) :
    (model S hC).app (model S hC).boxObj p = p := by
  apply S.rel_injective .t
  funext a
  cases a
  exact propext (box_spec S hC p)

/-- Both directions of modal collapse, hence in particular axiom 5. -/
theorem modal_collapse (p : (model S hC).Dom Ty.t) (w : (model S hC).World) :
    (model S hC).truth ((model S hC).app (model S hC).boxObj p) w ↔
      (model S hC).truth p w := box_spec S hC p

theorem axiom5 (p : (model S hC).Dom Ty.t) (w : (model S hC).World) :
    ¬ (model S hC).truth ((model S hC).app (model S hC).boxObj p) w →
      (model S hC).truth ((model S hC).app (model S hC).boxObj
        ((model S hC).neg ((model S hC).app (model S hC).boxObj p))) w := by
  intro hp
  exact (modal_collapse S hC _ w).2 (((model S hC).neg_spec _ w).2 hp)

noncomputable def argsOfEnv : (Γ : Ctx) → Henkin.Env (model S hC) Γ → Args S.D (RTy.ofArgs Γ)
  | [], _ => PUnit.unit
  | _ :: Γ, xs => (xs .zero, argsOfEnv Γ (Henkin.Env.tail xs))

noncomputable def envOfArgs : (Γ : Ctx) → Args S.D (RTy.ofArgs Γ) → Henkin.Env (model S hC) Γ
  | [], _ => Henkin.Env.nil
  | _ :: Γ, a => Henkin.Env.cons a.1 (envOfArgs Γ a.2)

theorem args_env : ∀ (Γ : Ctx) (a : Args S.D (RTy.ofArgs Γ)),
    argsOfEnv S hC Γ (envOfArgs S hC Γ a) = a
  | [], a => by cases a; rfl
  | _ :: Γ, a => by
    change (a.1, argsOfEnv S hC Γ (envOfArgs S hC Γ a.2)) = a
    rw [args_env Γ a.2]

theorem env_args : ∀ (Γ : Ctx) (xs : Henkin.Env (model S hC) Γ),
    @Eq (Henkin.Env (model S hC) Γ) (envOfArgs S hC Γ (argsOfEnv S hC Γ xs)) xs
  | [], xs => (Henkin.Env.nil_eta xs).symm
  | σ :: Γ, xs => by
    change @Eq (Henkin.Env (model S hC) (σ :: Γ))
      (Henkin.Env.cons (M := model S hC) (σ := σ) (xs .zero)
        (envOfArgs S hC Γ (argsOfEnv S hC Γ (Henkin.Env.tail xs)))) xs
    rw [env_args Γ (Henkin.Env.tail xs)]
    exact Henkin.Env.cons_eta xs

theorem uncurry_spec : ∀ (Γ : Ctx) (R : S.D (RTy.ofArgs Γ))
    (xs : Henkin.Env (model S hC) Γ) (w : PUnit),
    (model S hC).truth (Henkin.uncurry (model S hC) Γ R xs) w ↔
      S.rel (RTy.ofArgs Γ) R (argsOfEnv S hC Γ xs)
  | [], _, _, _ => Iff.rfl
  | σ :: Γ, R, xs, w => by
    change (model S hC).truth
      (Henkin.uncurry (model S hC) Γ (app S hC R (xs .zero)) (Henkin.Env.tail xs)) w ↔ _
    exact (uncurry_spec Γ (app S hC R (xs .zero)) (Henkin.Env.tail xs) w).trans
      (app_spec S hC (σ := σ) (ρ := RTy.ofArgs Γ) R
        (show S.D σ from xs .zero) (argsOfEnv S hC Γ (Henkin.Env.tail xs)))

theorem faithful : Henkin.Faithful (model S hC) := by
  intro Γ R T h
  apply S.rel_injective (RTy.ofArgs Γ)
  funext a
  apply propext
  have hh := (uncurry_spec S hC Γ R (envOfArgs S hC Γ a) PUnit.unit).symm.trans
    ((h (envOfArgs S hC Γ a) PUnit.unit).trans
      (uncurry_spec S hC Γ T (envOfArgs S hC Γ a) PUnit.unit))
  simpa only [args_env] using hh

theorem worldSeparated : Henkin.WorldSeparated (model S hC) := by
  intro w v h
  exact False.elim (h (@Subsingleton.elim PUnit inferInstance w v))

/-- Finite tuple equality is an ordinary finite first-order formula. -/
def tupleEqSmall {Γ : Ctx} : (ρ : RTy) →
    Args (fun σ => Var Γ σ) ρ → Args (fun σ => Var Γ σ) ρ → SmallFormula Γ
  | .t, _, _ => .neg .falsum
  | .arr _ ρ, a, b => .conj (.equal a.1 b.1) (tupleEqSmall ρ a.2 b.2)

theorem tupleEqSmall_spec {Γ : Ctx} (g : IEnv S.D Γ) :
    ∀ (ρ : RTy) (a b : Args (fun σ => Var Γ σ) ρ),
    (tupleEqSmall ρ a b).Realize S g ↔
      mapArgs (fun _ v => g.get v) ρ a = mapArgs (fun _ v => g.get v) ρ b
  | .t, a, b => by cases a; cases b; exact ⟨fun _ => rfl, fun _ h => h⟩
  | .arr σ ρ, a, b => by
    change (g.get a.1 = g.get b.1 ∧ (tupleEqSmall ρ a.2 b.2).Realize S g) ↔ _
    rw [tupleEqSmall_spec g ρ a.2 b.2]
    exact ⟨fun h => Prod.ext h.1 h.2,
      fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

include hC

theorem singleton_exists (ρ : RTy) (a : Args S.D ρ) :
    ∃ R : S.D (.rel ρ), ∀ b : Args S.D ρ, S.rel ρ R b ↔ b = a := by
  let φ : SmallFormula (ρ.args ++ ρ.args) := tupleEqSmall ρ
    (prefixArgs ρ.args ρ) (mapArgs (fun _ v => rightVar ρ.args v) ρ (blockArgs ρ))
  obtain ⟨R, hR⟩ := hC ρ.args ρ φ (argsEnv ρ a)
  refine ⟨R, fun b => (hR b).trans ?_⟩
  rw [tupleEqSmall_spec, eval_prefixArgs, mapArgs_comp]
  have hv : (fun (σ : Ty) (v : Var ρ.args σ) =>
      (appendEnv (argsEnv ρ b) (argsEnv ρ a)).get (rightVar ρ.args v)) =
      (fun (σ : Ty) (v : Var ρ.args σ) => (argsEnv ρ a).get v) := by
    funext σ v
    exact get_append_right (argsEnv ρ b) (argsEnv ρ a) v
  rw [hv, mapArgs_block]

/-- Ordinary pointwise Atomicity, at every finite relation type. The witness
is a represented singleton constructed by finite comprehension. -/
theorem relation_atomicity (ρ : RTy) (R : S.D (.rel ρ))
    (hR : ∃ a, S.rel ρ R a) :
    ∃ A : S.D (.rel ρ), (∃ a, S.rel ρ A a) ∧
      (∀ a, S.rel ρ A a → S.rel ρ R a) ∧
      ∀ B : S.D (.rel ρ), (∀ a, S.rel ρ B a → S.rel ρ A a) →
        (∀ a, ¬ S.rel ρ B a) ∨ B = A := by
  classical
  obtain ⟨a, ha⟩ := hR
  obtain ⟨A, hA⟩ := singleton_exists S hC ρ a
  refine ⟨A, ⟨a, (hA a).2 rfl⟩, ?_, ?_⟩
  · intro b hb
    exact ((hA b).1 hb).symm ▸ ha
  · intro B hB
    by_cases hb : ∃ b, S.rel ρ B b
    · right
      obtain ⟨b, hb⟩ := hb
      have hba := (hA b).1 (hB b hb)
      have hBa : S.rel ρ B a := hba ▸ hb
      apply S.rel_injective ρ
      funext c
      exact propext ⟨hB c, fun hc => ((hA c).1 hc).symm ▸ hBa⟩
    · left
      intro b h
      exact hb ⟨b, h⟩

theorem profile_atomic : ProfileAtomic (model S hC) := by
  intro Γ R hR
  obtain ⟨xs, w, hxs⟩ := hR
  obtain ⟨A, hA, hAR, hAtom⟩ := relation_atomicity S hC (RTy.ofArgs Γ) R
    ⟨argsOfEnv S hC Γ xs, (uncurry_spec S hC Γ R xs w).1 hxs⟩
  refine ⟨A, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hA
    refine ⟨envOfArgs S hC Γ a, PUnit.unit, ?_⟩
    apply (uncurry_spec S hC Γ A _ _).2
    simpa only [args_env] using ha
  · intro ys v hy
    exact (uncurry_spec S hC Γ R ys v).2
      (hAR _ ((uncurry_spec S hC Γ A ys v).1 hy))
  · intro B hBA
    have hb : ∀ a, S.rel (RTy.ofArgs Γ) B a → S.rel (RTy.ofArgs Γ) A a := by
      intro a ha
      have hBt : (model S hC).truth
          (Henkin.uncurry (model S hC) Γ B (envOfArgs S hC Γ a)) PUnit.unit := by
        apply (uncurry_spec S hC Γ B _ _).2
        simpa only [args_env] using ha
      have hAt := hBA (envOfArgs S hC Γ a) PUnit.unit hBt
      have hAa := (uncurry_spec S hC Γ A _ _).1 hAt
      simpa only [args_env] using hAa
    rcases hAtom B hb with hEmpty | hEq
    · exact Or.inl (fun ys v hy => hEmpty _ ((uncurry_spec S hC Γ B ys v).1 hy))
    · exact Or.inr hEq

/-- The finitary reduct really satisfies the existing C proof system. -/
theorem c_theorem_holds {p : Sentence Signature.pure} (hp : C.Theorem p) :
    (Classicism.Meta.ChoiceFirstOrder.Structure.model S).HoldsSentence p :=
  (Classicism.Meta.ChoiceFirstOrder.Structure.model S).theorem_holds
    (isModel_of_small_comprehension S hC) hp

theorem relation_nonempty (ρ : RTy) : Nonempty (S.D (.rel ρ)) :=
  ⟨represent S hC [] ρ .falsum .nil⟩

/-- A countable predicate domain can be enumerated by any infinite individual
domain. This is a metatheoretic enumeration used only to select the branches
of the concrete diagonal formula. -/
theorem predicate_enumeration [Countable (S.D (Ty.e ⇒ RTy.t))]
    [Infinite (S.D Ty.e)] :
    ∃ f : S.D Ty.e → S.D (Ty.e ⇒ RTy.t), Function.Surjective f := by
  classical
  obtain ⟨code⟩ := nonempty_embedding_nat (S.D (Ty.e ⇒ RTy.t))
  let embed : S.D (Ty.e ⇒ RTy.t) ↪ S.D Ty.e :=
    code.trans (Infinite.natEmbedding (S.D Ty.e))
  let fallback : S.D (Ty.e ⇒ RTy.t) :=
    Classical.choice (relation_nonempty S hC (.arr .e .t))
  let f : S.D Ty.e → S.D (Ty.e ⇒ RTy.t) := fun a =>
    if h : ∃ P, embed P = a then Classical.choose h else fallback
  refine ⟨f, fun P => ⟨embed P, ?_⟩⟩
  have h : ∃ Q, embed Q = embed P := ⟨P, rfl⟩
  change (if h : ∃ Q, embed Q = embed P then Classical.choose h else fallback) = P
  rw [dif_pos h]
  exact embed.injective (Classical.choose_spec h)

/-- Infinitary Comprehension fails in this actual expanded interpretation. -/
theorem not_comp [Countable (S.D (Ty.e ⇒ RTy.t))] [Infinite (S.D Ty.e)] :
    ¬ Henkin.Comp (model S hC) PUnit.unit := by
  obtain ⟨f, hf⟩ := predicate_enumeration S hC
  exact Henkin.no_comprehension_of_predicate_enumeration (model S hC) PUnit.unit f hf

end Expansion

/-- Every retained named natural lies in the recovered individual sort. -/
def reductNatural (S : ElementaryReduct) (hN : ∀ n, natural n ∈ S)
    (n : Nat) : Recovery.D S Ty.e :=
  ⟨⟨natural n, hN n⟩, by rfl⟩

theorem reductNatural_injective (S : ElementaryReduct) (hN : ∀ n, natural n ∈ S) :
    Function.Injective (reductNatural S hN) := by
  intro m n h
  apply natural_injective
  exact congrArg (fun x : Recovery.D S Ty.e => x.val.val) h

theorem reduct_individual_infinite (S : ElementaryReduct) (hN : ∀ n, natural n ∈ S) :
    Infinite (Recovery.D S Ty.e) :=
  Infinite.of_injective (reductNatural S hN) (reductNatural_injective S hN)

/-- The original finite typed hierarchy is recovered from the proved
first-order theory of the actual elementary substructure. -/
def reductStructure (S : ElementaryReduct) : Structure :=
  AxiomTheory.recoveredStructure S (reduct_theory S)

theorem reductComprehension (S : ElementaryReduct) :
    SmallComprehension (reductStructure S) :=
  AxiomTheory.recovered_smallComprehension S (reduct_theory S)

noncomputable def reductModel (S : ElementaryReduct) : Henkin.Model :=
  Expansion.model (reductStructure S) (reductComprehension S)

/-- Named consequences of the construction, with C soundness attached to the
same finite first-order hierarchy whose profiles define the expansion. -/
structure CountermodelCertificate (S : Structure) (hC : SmallComprehension S) : Prop where
  countable_sorts : ∀ σ, Countable (S.D σ)
  infinite_individuals : Infinite (S.D Ty.e)
  c_model : S.model.IsModel
  faithful : Henkin.Faithful (Expansion.model S hC)
  separated : Henkin.WorldSeparated (Expansion.model S hC)
  two_propositions : ∀ p : S.D Ty.t, p = Expansion.top S hC ∨ p = Expansion.bot S hC
  distinct_propositions : Expansion.top S hC ≠ Expansion.bot S hC
  box_identity : ∀ p : S.D Ty.t,
    (Expansion.model S hC).app (Expansion.model S hC).boxObj p = p
  atomicity : ProfileAtomic (Expansion.model S hC)
  failed_comprehension : ¬ Henkin.Comp (Expansion.model S hC) PUnit.unit

theorem reduct_certificate (S : ElementaryReduct) [Countable S]
    (hN : ∀ n, natural n ∈ S) :
    CountermodelCertificate (reductStructure S) (reductComprehension S) := by
  letI : Infinite ((reductStructure S).D Ty.e) := reduct_individual_infinite S hN
  letI : Countable ((reductStructure S).D (Ty.e ⇒ RTy.t)) :=
    inferInstanceAs (Countable (Recovery.D S (Ty.e ⇒ RTy.t)))
  exact {
    countable_sorts := fun σ => inferInstanceAs (Countable (Recovery.D S σ))
    infinite_individuals := inferInstance
    c_model := AxiomTheory.recovered_isModel S (reduct_theory S)
    faithful := Expansion.faithful _ _
    separated := Expansion.worldSeparated _ _
    two_propositions := Expansion.proposition_cases _ _
    distinct_propositions := Expansion.top_ne_bot _ _
    box_identity := Expansion.box_eq _ _
    atomicity := Expansion.profile_atomic _ _
    failed_comprehension := Expansion.not_comp _ _ }

/-- An existing countermodel in the same infinitary grammar. The hierarchy
is constructed by downward LS; no countable model or omitted support is a
hypothesis. The finite reduct is an actual C model, necessity is identity,
all relation profiles are atomic, but a concrete countable-disjunction
Comprehension instance fails. -/
theorem exists_strictness_certificate :
    ∃ (S : Structure) (hC : SmallComprehension S), CountermodelCertificate S hC := by
  obtain ⟨S, hS, hN⟩ := exists_countable_elementary_reduct
  letI : Countable S := hS
  exact ⟨reductStructure S, reductComprehension S, reduct_certificate S hN⟩

theorem exists_atomic_modal_collapse_not_comp :
    ∃ (M : Henkin.Model.{0}) (w : M.World),
      Infinite (M.Dom Ty.e) ∧ Countable (M.Dom (Ty.e ⇒ RTy.t)) ∧
      Henkin.Faithful M ∧ Henkin.WorldSeparated M ∧ ProfileAtomic M ∧
      (∀ p : M.Dom Ty.t, M.app M.boxObj p = p) ∧ ¬ Henkin.Comp M w := by
  obtain ⟨S, hC, h⟩ := exists_strictness_certificate
  exact ⟨Expansion.model S hC, PUnit.unit, h.infinite_individuals,
    h.countable_sorts _, h.faithful, h.separated, h.atomicity,
    h.box_identity, h.failed_comprehension⟩

#print axioms Expansion.model
#print axioms Expansion.faithful
#print axioms Expansion.relation_atomicity
#print axioms Expansion.profile_atomic
#print axioms Expansion.c_theorem_holds
#print axioms Expansion.not_comp
#print axioms reduct_certificate
#print axioms exists_strictness_certificate
#print axioms exists_atomic_modal_collapse_not_comp

end Classicism.Research.InfinitaryComprehension.Strictness
