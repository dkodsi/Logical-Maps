import Classicism.Results.Research.MaxAtomicityHCodeCharacterization
import Classicism.Results.Research.MaxAtomicityRigidTransport
import Classicism.Results.Research.MaxAtomicityCountableGenerator
import Classicism.Results.Research.MaxAtomicitySplitSemantics
import Classicism.Results.Research.MaxAtomicityEvalTools

/-!
# A finite pure selector from a coded canonical generating sequence

The parameter phi is one finite membership formula with free variables c,w,G:
the coded algebra carrier, the natural numbers, and the generator graph. No
constant naming the algebra, a well-order, or a selector is added to C.

The literal term quantifies over the universe code, the three coded sets, an
order isomorphism, and a natural index. It chooses the first generator splitting
p. An equality-to-top test makes each individual witness guard crisp BEFORE
the existential quantifiers are evaluated.

Formula adequacy is an explicit external obligation: successful codes must
present the fixed algebra order, ordinary natural-number predecessors, and
the fixed generator graph, and one successful presentation must exist. The
algebraic selector and its uniqueness are proved from those data and rigidity,
not inserted into the adequacy premise. The concrete JS formula is supplied
separately. Original proof/transcription: misc, 23 October 2026. Source awaits
the designated serial checker; this file alone is not the final certificate.
-/

namespace Classicism.Meta.Research.MaxAtomicityPureSelector

open BooleanValued MaxAtomicitySyntax MaxAtomicitySetSyntax MaxAtomicitySetSemantics
open MaxAtomicityHCodeSyntax MaxAtomicityHCodeSemantics MaxAtomicitySetFormulaTools
open MaxAtomicityRigidTransport MaxAtomicityCountableGenerator MaxAtomicityWellOrder

abbrev HU : RTy := Ty.t ⇒ U

private abbrev v3 {Γ : Ctx} {a b c d : Ty} : PT (d :: c :: b :: a :: Γ) a :=
  .var (.succ (.succ (.succ .zero)))
private abbrev v4 {Γ : Ctx} {a b c d e : Ty} : PT (e :: d :: c :: b :: a :: Γ) a :=
  .var (.succ (.succ (.succ (.succ .zero))))
private abbrev v5 {Γ : Ctx} {a b c d e f : Ty} : PT (f :: e :: d :: c :: b :: a :: Γ) a :=
  .var (.succ (.succ (.succ (.succ (.succ .zero)))))

def triple {D : Type*} (a b c : D) : Fin 3 → D :=
  Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0))

def sub {Γ : Ctx} (E : PT Γ ER) (a b : PT Γ U) : Formula Signature.pure Γ :=
  Term.forall' (σ := U)
    (Term.imp (member E.weaken Term.v0 a.weaken) (member E.weaken Term.v0 b.weaken))

def appGraph {Γ : Ctx} (E : PT Γ ER) (G a b : PT Γ U) : Formula Signature.pure Γ :=
  translate (graphApp (0 : Fin 3) 1 2) E (triple G a b)

def leProp {Γ : Ctx} (p q : Formula Signature.pure Γ) : Formula Signature.pure Γ :=
  Term.eq' (Term.conj p q) p

def splits {Γ : Ctx} (p q : Formula Signature.pure Γ) : Formula Signature.pure Γ :=
  Term.conj (Term.neg (Term.eq' (Term.conj p q) Term.bot))
    (Term.neg (Term.eq' (Term.conj p (Term.neg q)) Term.bot))

/-- The range, surjectivity, and order-reflection clauses are all explicit. -/
def isIso {Γ : Ctx} (E : PT Γ ER) (c : PT Γ U) (h : PT Γ HU) :
    Formula Signature.pure Γ :=
  Term.conj
    (Term.forall' (σ := Ty.t) (member E.weaken (.app h.weaken Term.v0) c.weaken))
    (Term.conj
      (Term.forall' (σ := U) (Term.imp (member E.weaken Term.v0 c.weaken)
        (Term.exists' (σ := Ty.t) (Term.eq' (.app h.weaken.weaken Term.v0) Term.v1))))
      (Term.forall' (σ := Ty.t) (Term.forall' (σ := Ty.t)
        (Term.iff (leProp Term.v1 Term.v0)
          (sub E.weaken.weaken (.app h.weaken.weaken Term.v1)
            (.app h.weaken.weaken Term.v0))))))

def earlierFail {Γ : Ctx} (E : PT Γ ER) (G n : PT Γ U)
    (h : PT Γ HU) (p : Formula Signature.pure Γ) : Formula Signature.pure Γ :=
  Term.forall' (σ := U) (Term.imp (member E.weaken Term.v0 n.weaken)
    (Term.forall' (σ := Ty.t)
      (Term.imp (appGraph E.weaken.weaken G.weaken.weaken Term.v1
        (.app h.weaken.weaken Term.v0)) (Term.neg (splits p.weaken.weaken Term.v0)))))

def rawGuard (phi : SetFormula 3) {Γ : Ctx}
    (E : PT Γ ER) (c w G : PT Γ U) (h : PT Γ HU) (n : PT Γ U)
    (p q : Formula Signature.pure Γ) : Formula Signature.pure Γ :=
  Term.conj (hCode E)
    (Term.conj (translate phi E (triple c w G))
      (Term.conj (isIso E c h)
        (Term.conj (member E n w)
          (Term.conj (appGraph E G n (.app h q))
            (Term.conj (splits p q) (earlierFail E G n h p))))))

def witnessGuard (phi : SetFormula 3) {Γ : Ctx}
    (E : PT Γ ER) (c w G : PT Γ U) (h : PT Γ HU) (n : PT Γ U)
    (p q : Formula Signature.pure Γ) : Formula Signature.pure Γ :=
  Term.eq' (rawGuard phi E c w G h n p q) Term.top

/-- The six witnesses are quantified at fixed closed types. -/
def selects (phi : SetFormula 3) {Γ : Ctx} (p q : Formula Signature.pure Γ) :
    Formula Signature.pure Γ :=
  Term.exists' (σ := ER) (Term.exists' (σ := U) (Term.exists' (σ := U)
    (Term.exists' (σ := U) (Term.exists' (σ := HU) (Term.exists' (σ := U)
      (witnessGuard phi v5 v4 v3 Term.v2 Term.v1 Term.v0
        p.weaken.weaken.weaken.weaken.weaken.weaken
        q.weaken.weaken.weaken.weaken.weaken.weaken))))))

/-- The actual closed pure t→t term; the final existential is Boolean-valued. -/
def selector (phi : SetFormula 3) : Term Signature.pure [] (Ty.t ⇒ RTy.t) :=
  .lam (Term.exists' (σ := Ty.t) (Term.conj (selects phi Term.v1 Term.v0) Term.v0))

theorem selector_pure (phi : SetFormula 3) : (selector phi).pure = true :=
  (selector phi).pure_of_pureSig

private theorem triple_property {D : Type*} (P : D → Prop) {a b c : D}
    (ha : P a) (hb : P b) (hc : P c) : ∀ i, P (triple a b c i) :=
  Fin.cases ha (Fin.cases hb (Fin.cases hc Fin.elim0))

theorem appGraph_closedTypes {Γ : Ctx} (E : PT Γ ER) (G a b : PT Γ U)
    (hE : E.closedTypes = true) (hG : G.closedTypes = true)
    (ha : a.closedTypes = true) (hb : b.closedTypes = true) :
    (appGraph E G a b).closedTypes = true :=
  translate_closedTypes _ E (triple G a b) hE
    (triple_property (fun t => t.closedTypes = true) hG ha hb)

private theorem weaken_closed {Γ : Ctx} {σ τ : Ty} (t : PT Γ σ)
    (h : t.closedTypes = true) : (t.weaken (τ := τ)).closedTypes = true := by
  simpa only [Term.weaken, Term.closedTypes_rename] using h

private theorem hCode_closedTypes {Γ : Ctx} (E : PT Γ ER)
    (hE : E.closedTypes = true) : (hCode E).closedTypes = true := by
  simp only [hCode, rows, cover, crispRelation, extensional,
    MaxAtomicitySyntax.wellFounded, fill, MaxAtomicitySyntax.crisp, small,
    Term.closedTypes_conj, Term.closedTypes_forall', Term.closedTypes_exists',
    Term.closedTypes_imp, Term.closedTypes_iff, Term.closedTypes_neg,
    Term.closedTypes_eq', Term.closedTypes_disj, Term.closedTypes_bot,
    Term.closedTypes_top, member, Term.closedTypes, Term.weaken,
    Term.closedTypes_rename, hE, Bool.true_and, Bool.and_true] <;> rfl

private theorem isIso_closedTypes {Γ : Ctx} (E : PT Γ ER) (c : PT Γ U) (h : PT Γ HU)
    (hE : E.closedTypes = true) (hc : c.closedTypes = true) (hh : h.closedTypes = true) :
    (isIso E c h).closedTypes = true := by
  simp only [isIso, sub, leProp, Term.closedTypes_conj,
    Term.closedTypes_forall', Term.closedTypes_exists', Term.closedTypes_imp,
    Term.closedTypes_iff, Term.closedTypes_eq', member, Term.closedTypes,
    Term.weaken, Term.closedTypes_rename, hE, hc, hh, Bool.true_and, Bool.and_true] <;> rfl

private theorem splits_closedTypes {Γ : Ctx} (p q : Formula Signature.pure Γ)
    (hp : p.closedTypes = true) (hq : q.closedTypes = true) :
    (splits p q).closedTypes = true := by
  simp only [splits, Term.closedTypes_conj, Term.closedTypes_neg,
    Term.closedTypes_eq', Term.closedTypes_bot, hp, hq, Bool.true_and]

theorem rawGuard_closedTypes (phi : SetFormula 3) {Γ : Ctx}
    (E : PT Γ ER) (c w G : PT Γ U) (h : PT Γ HU) (n : PT Γ U)
    (p q : Formula Signature.pure Γ)
    (hE : E.closedTypes = true) (hc : c.closedTypes = true) (hw : w.closedTypes = true)
    (hG : G.closedTypes = true) (hh : h.closedTypes = true) (hn : n.closedTypes = true)
    (hp : p.closedTypes = true) (hq : q.closedTypes = true) :
    (rawGuard phi E c w G h n p q).closedTypes = true := by
  have hphi := translate_closedTypes phi E (triple c w G) hE
    (triple_property (fun t => t.closedTypes = true) hc hw hG)
  have hgraph := appGraph_closedTypes E G n (.app h q) hE hG hn
    (by change h.closedTypes && q.closedTypes = true; simp only [hh, hq, Bool.true_and])
  have hearlier : (earlierFail E G n h p).closedTypes = true := by
    have he := appGraph_closedTypes E.weaken.weaken G.weaken.weaken Term.v1
      (.app h.weaken.weaken Term.v0)
      (weaken_closed _ (weaken_closed _ hE))
      (weaken_closed _ (weaken_closed _ hG)) rfl (by
        change h.weaken.weaken.closedTypes && true = true
        simp only [Term.weaken, Term.closedTypes_rename, hh, Bool.true_and])
    simp only [earlierFail, Term.closedTypes_forall', Term.closedTypes_imp,
      Term.closedTypes_neg, splits, Term.closedTypes_conj, Term.closedTypes_eq',
      Term.closedTypes_bot, member, Term.closedTypes, Term.weaken,
      Term.closedTypes_rename, hE, hn, hp, he, Bool.true_and, Bool.and_true]
    all_goals rfl
  have hmem : (member E n w).closedTypes = true := by
    change (E.closedTypes && n.closedTypes) && w.closedTypes = true
    simp only [hE, hn, hw, Bool.true_and]
  simpa only [rawGuard, Term.closedTypes_conj, hphi, hgraph, hearlier,
    hCode_closedTypes E hE, isIso_closedTypes E c h hE hc hh,
    splits_closedTypes p q hp hq, hmem, Bool.true_and]

theorem selector_closedTypes (phi : SetFormula 3) : (selector phi).closedTypes = true := by
  have h := rawGuard_closedTypes phi
    (v5 : PT [(U : Ty), (HU : Ty), (U : Ty), (U : Ty), (U : Ty), (ER : Ty), Ty.t, Ty.t] ER)
    v4 v3 Term.v2 Term.v1 Term.v0
    (Term.v1.weaken.weaken.weaken.weaken.weaken.weaken)
    (Term.v0.weaken.weaken.weaken.weaken.weaken.weaken)
    rfl rfl rfl rfl rfl rfl rfl rfl
  change true && (true && ((selects phi Term.v1 Term.v0).closedTypes && true)) = true
  simp only [selects, Term.closedTypes_exists', witnessGuard, Term.closedTypes_eq',
    Term.closedTypes_top, h, Bool.true_and, Bool.and_true]
  rfl

noncomputable section

variable {B : Type} [CompleteBooleanAlgebra B]

namespace OrdinarySelector

variable {D : Type} (R : D → D → Prop)

def Iso (c : D) (h : B → D) : Prop :=
  (∀ p, R (h p) c) ∧ (∀ a, R a c → ∃ p, h p = a) ∧
    ∀ p q, p ≤ q ↔ Ordinary.Subset R (h p) (h q)

def EarlierFail (G n : D) (h : B → D) (p : B) : Prop :=
  ∀ m, R m n → ∀ r, Ordinary.GraphApp R G m (h r) → ¬ Splits p r

end OrdinarySelector

def ValidCode (phi : SetFormula 3) (E : (B → B) → (B → B) → B)
    (c w G : B → B) : Prop :=
  (∀ a b, E a b = ⊥ ∨ E a b = ⊤) ∧
    GoodRelation (B := B) (fun a b => E a b = ⊤) ∧
    satisfies phi (fun a b => E a b = ⊤) (triple c w G)

def Witness (phi : SetFormula 3) (E : (B → B) → (B → B) → B)
    (c w G : B → B) (h : B → (B → B)) (n : B → B) (p q : B) : Prop :=
  ValidCode phi E c w G ∧
    OrdinarySelector.Iso (fun a b => E a b = ⊤) c h ∧ E n w = ⊤ ∧
      Ordinary.GraphApp (fun a b => E a b = ⊤) G n (h q) ∧ Splits p q ∧
        OrdinarySelector.EarlierFail (fun a b => E a b = ⊤) G n h p

def Selected (phi : SetFormula 3) (p q : B) : Prop :=
  ∃ E c w G h n, Witness phi E c w G h n p q

private theorem ev_conj (I : Interpretation Signature.pure B) {Γ : Ctx}
    (p q : Formula Signature.pure Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.conj p q) env = eval I p env ⊓ eval I q env := rfl
private theorem ev_imp (I : Interpretation Signature.pure B) {Γ : Ctx}
    (p q : Formula Signature.pure Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.imp p q) env = (eval I p env)ᶜ ⊔ eval I q env := rfl
private theorem ev_iff (I : Interpretation Signature.pure B) {Γ : Ctx}
    (p q : Formula Signature.pure Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.iff p q) env =
      ((eval I p env)ᶜ ⊔ eval I q env) ⊓ ((eval I q env)ᶜ ⊔ eval I p env) := rfl
private theorem ev_neg (I : Interpretation Signature.pure B) {Γ : Ctx}
    (p : Formula Signature.pure Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.neg p) env = (eval I p env)ᶜ := rfl
private theorem ev_eq (I : Interpretation Signature.pure B) {Γ : Ctx} {σ : Ty}
    (p q : PT Γ σ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.eq' p q) env = BooleanValued.crisp (eval I p env) (eval I q env) := rfl
private theorem ev_all (I : Interpretation Signature.pure B) {Γ : Ctx} {σ : Ty}
    (p : Formula Signature.pure (σ :: Γ)) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.forall' p) env = ⨅ x, eval I p (.cons x env) := rfl
private theorem ev_ex (I : Interpretation Signature.pure B) {Γ : Ctx} {σ : Ty}
    (p : Formula Signature.pure (σ :: Γ)) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.exists' p) env = ⨆ x, eval I p (.cons x env) := rfl
private theorem ev_app (I : Interpretation Signature.pure B) {Γ : Ctx} {σ : Ty} {τ : RTy}
    (f : PT Γ (σ ⇒ τ)) (a : PT Γ σ) (env : IEnv (Dom I.E B) Γ) :
    eval I (.app f a) env = eval I f env (eval I a env) := rfl
private theorem ev_member (I : Interpretation Signature.pure B) {Γ : Ctx}
    (E : PT Γ ER) (a b : PT Γ U) (env : IEnv (Dom I.E B) Γ) :
    eval I (member E a b) env = eval I E env (eval I a env) (eval I b env) := rfl

theorem eval_splits (I : Interpretation Signature.pure B) {Γ : Ctx}
    (p q : Formula Signature.pure Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (splits p q) env = truth (Splits (eval I p env) (eval I q env)) := by
  simp only [splits, ev_conj, ev_neg, ev_eq, eval_bot, crisp_eq_truth,
    compl_truth, inf_truth, Splits]

theorem eval_sub (I : Interpretation Signature.pure B) {Γ : Ctx}
    (E : PT Γ ER) (a b : PT Γ U) (env : IEnv (Dom I.E B) Γ)
    (R : (B → B) → (B → B) → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (sub E a b) env = truth (Ordinary.Subset R (eval I a env) (eval I b env)) := by
  simp only [sub, ev_all, ev_imp, ev_member, eval_weaken, eval, IEnv.get,
    hE, imp_truth, iInf_truth, Ordinary.Subset]

theorem eval_appGraph (I : Interpretation Signature.pure B) {Γ : Ctx}
    (E : PT Γ ER) (G a b : PT Γ U) (env : IEnv (Dom I.E B) Γ)
    (R : (B → B) → (B → B) → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (appGraph E G a b) env =
      truth (Ordinary.GraphApp R (eval I G env) (eval I a env) (eval I b env)) := by
  exact eval_translate I (graphApp (0 : Fin 3) 1 2) R E (triple G a b) env hE

theorem eval_isIso (I : Interpretation Signature.pure B) {Γ : Ctx}
    (E : PT Γ ER) (c : PT Γ U) (h : PT Γ HU) (env : IEnv (Dom I.E B) Γ)
    (R : (B → B) → (B → B) → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (isIso E c h) env = truth (OrdinarySelector.Iso R (eval I c env) (eval I h env)) := by
  simp only [isIso, ev_conj, ev_all, ev_imp, ev_ex, ev_eq, ev_iff,
    leProp, ev_conj, ev_eq, sub, ev_all, ev_imp, ev_member, ev_app,
    eval_weaken, eval, IEnv.get, hE, crisp_eq_truth, inf_eq_left,
    iSup_truth, imp_truth, iInf_truth, iff_truth, inf_truth,
    OrdinarySelector.Iso, Ordinary.Subset]

theorem eval_earlierFail (I : Interpretation Signature.pure B) {Γ : Ctx}
    (E : PT Γ ER) (G n : PT Γ U) (h : PT Γ HU) (p : Formula Signature.pure Γ)
    (env : IEnv (Dom I.E B) Γ) (R : (B → B) → (B → B) → Prop)
    (hE : ∀ x y, eval I E env x y = truth (R x y)) :
    eval I (earlierFail E G n h p) env =
      truth (OrdinarySelector.EarlierFail R (eval I G env) (eval I n env)
        (eval I h env) (eval I p env)) := by
  simp only [earlierFail, ev_all, ev_imp, ev_neg]
  have hg (m : B → B) (r : B) := eval_appGraph I E.weaken.weaken
    G.weaken.weaken Term.v1 (.app h.weaken.weaken Term.v0) (.cons r (.cons m env)) R
    (fun a b => by simpa only [eval_weaken] using hE a b)
  simp only [hg, eval_splits, ev_member, ev_app, eval_weaken, eval, IEnv.get,
    hE, compl_truth, imp_truth, iInf_truth, OrdinarySelector.EarlierFail]

/-- Exact crisp semantics of the individual guard, including invalid relation
arguments. This precedes every existential witness extraction. -/
theorem eval_witnessGuard [Nontrivial B] (I : Interpretation Signature.pure B)
    (phi : SetFormula 3) {Γ : Ctx} (E : PT Γ ER) (c w G : PT Γ U)
    (h : PT Γ HU) (n : PT Γ U) (p q : Formula Signature.pure Γ)
    (env : IEnv (Dom I.E B) Γ) :
    eval I (witnessGuard phi E c w G h n p q) env =
      truth (Witness phi (eval I E env) (eval I c env) (eval I w env)
        (eval I G env) (eval I h env) (eval I n env) (eval I p env) (eval I q env)) := by
  classical
  by_cases hc : ∀ a b, eval I E env a b = ⊥ ∨ eval I E env a b = ⊤
  · let R : (B → B) → (B → B) → Prop := fun a b => eval I E env a b = ⊤
    have hE : ∀ a b, eval I E env a b = truth (R a b) := fun a b => crisp_value (hc a) b
    have hphi := eval_translate I phi R E (triple c w G) env hE
    have hcode := eval_hCode I E env R hE
    have hgraph := eval_appGraph I E G n (.app h q) env R hE
    have hiso := eval_isIso I E c h env R hE
    have hearlier := eval_earlierFail I E G n h p env R hE
    simp only [witnessGuard, ev_eq, eval_top, rawGuard, ev_conj,
      hcode, hphi, hgraph, hiso, hearlier, eval_splits,
      ev_member, ev_app, hE, inf_truth, crisp_eq_truth, truth_eq_top_iff]
    congr 1
    simp only [Witness, ValidCode, hc, true_and, R, triple, and_assoc]
    rfl
  · have he := eval_hCode_noncrisp I E env hc
    simp only [witnessGuard, ev_eq, eval_top, rawGuard, ev_conj, he,
      bot_inf_eq, crisp_of_ne bot_ne_top]
    symm
    apply (truth_eq_bot_iff _).2
    intro hW
    exact hc hW.1.1

theorem eval_selects [Nontrivial B] (I : Interpretation Signature.pure B)
    (phi : SetFormula 3) {Γ : Ctx} (p q : Formula Signature.pure Γ)
    (env : IEnv (Dom I.E B) Γ) :
    eval I (selects phi p q) env = truth (Selected phi (eval I p env) (eval I q env)) := by
  simp only [selects, ev_ex, eval_witnessGuard, eval_weaken, eval, IEnv.get,
    iSup_truth, Selected, v3, v4, v5]

/-- Evaluation of the literal existential term is its actual Boolean join. -/
theorem eval_selector [Nontrivial B] (I : Interpretation Signature.pure B)
    (phi : SetFormula 3) (p : B) :
    eval I (selector phi) .nil p =
      ⨆ q : B, truth (Selected phi p q) ⊓ q := by
  simp only [selector, MaxAtomicityEvalTools.eval_lam, ev_ex, ev_conj,
    eval_selects, MaxAtomicityEvalTools.eval_v0, MaxAtomicityEvalTools.eval_v1]

/-- The exact mathematical adequacy data, before any use of rigidity or least
indices. The predecessor clause excludes spurious nonstandard predecessors. -/
structure Presentation {D : Type} (R : D → D → Prop) (c w G : D) (g : ℕ → B) where
  carrier : B ↪ D
  carrier_range : ∀ a, R a c ↔ ∃ b, carrier b = a
  carrier_order : ∀ b d, Ordinary.Subset R (carrier b) (carrier d) ↔ b ≤ d
  number : ℕ ↪ D
  number_range : ∀ a, R a w ↔ ∃ k, number k = a
  predecessor : ∀ k a, R a (number k) ↔ ∃ j, j < k ∧ number j = a
  graph : ∀ k a, Ordinary.GraphApp R G (number k) a ↔ a = carrier (g k)

/-- This is the one remaining formula-specific premise. It says what the
finite formula codes; it contains no least-generator or splitting assertion. -/
structure Adequate (phi : SetFormula 3) (g : ℕ → B) : Prop where
  sound : ∀ E c w G, ValidCode phi E c w G →
    Nonempty (Presentation (fun a b => E a b = ⊤) c w G g)
  exists_code : ∃ E c w G, ValidCode phi E c w G

namespace Presentation

variable {D : Type} {R : D → D → Prop} {c w G : D} {g : ℕ → B}
variable (P : Presentation R c w G g)

theorem carrier_isIso : OrdinarySelector.Iso R c P.carrier := by
  refine ⟨fun b => (P.carrier_range _).2 ⟨b, rfl⟩,
    fun a ha => (P.carrier_range a).1 ha, ?_⟩
  intro b d
  exact (P.carrier_order b d).symm

/-- The quantified isomorphism is forced to be the canonical carrier map by
rigidity. There is no uniqueness clause in formula adequacy. -/
theorem iso_eq_carrier (rigid : Rigid B) {h : B → D}
    (hiso : OrdinarySelector.Iso R c h) : h = P.carrier := by
  classical
  have hex : ∀ b, ∃ d, P.carrier d = h b :=
    fun b => (P.carrier_range _).1 (hiso.1 b)
  choose f hf using hex
  have horder : ∀ b d, f b ≤ f d ↔ b ≤ d := by
    intro b d
    rw [← P.carrier_order, hf, hf]
    exact (hiso.2.2 b d).symm
  have hinj : Function.Injective f := by
    intro b d hbd
    exact le_antisymm ((horder b d).1 hbd.le) ((horder d b).1 hbd.symm.le)
  have hsurj : Function.Surjective f := by
    intro d
    obtain ⟨b, hb⟩ := hiso.2.1 (P.carrier d) ((P.carrier_range _).2 ⟨d, rfl⟩)
    exact ⟨b, P.carrier.injective ((hf b).trans hb)⟩
  let e : B ≃o B := {
    toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
    map_rel_iff' := horder _ _ }
  funext b
  have hfix : f b = b := congrArg (fun a : B ≃o B => a b) (rigid e)
  exact (hf b).symm.trans (congrArg P.carrier hfix)

end Presentation

theorem selected_least (phi : SetFormula 3) (g : ℕ → B)
    (adequate : Adequate phi g) (rigid : Rigid B) (gen : CompletelyGenerates g)
    (atomless : AtomlessParts B) {p q : B} (hp : p ≠ ⊥)
    (hq : Selected phi p q) : q = g (leastIndex g gen atomless p hp) := by
  classical
  obtain ⟨E, c, w, G, h, n, hcode, hiso, hn, hgraph, hsplit, hearlier⟩ := hq
  obtain ⟨P⟩ := adequate.sound E c w G hcode
  have hh := P.iso_eq_carrier rigid hiso
  obtain ⟨k, hk⟩ := (P.number_range n).1 hn
  have hqk : q = g k := by
    apply P.carrier.injective
    exact (P.graph k (P.carrier q)).1 (by simpa only [hk, ← hh] using hgraph)
  have hmin : ∀ j, j < k → ¬ Splits p (g j) := by
    intro j hj
    apply hearlier (P.number j)
    · rw [← hk]
      exact (P.predecessor k _).2 ⟨j, hj, rfl⟩
    · apply (P.graph j _).2
      exact congrFun hh (g j)
  have hkmin : k = leastIndex g gen atomless p hp := by
    rcases lt_trichotomy k (leastIndex g gen atomless p hp) with hlt | heq | hgt
    · exact ((leastIndex_min g gen atomless p hp hlt) (hqk ▸ hsplit)).elim
    · exact heq
    · exact ((hmin _ hgt) (leastIndex_spec g gen atomless p hp)).elim
  exact hqk.trans (congrArg g hkmin)

theorem least_selected (phi : SetFormula 3) (g : ℕ → B)
    (adequate : Adequate phi g) (gen : CompletelyGenerates g)
    (atomless : AtomlessParts B) {p : B} (hp : p ≠ ⊥) :
    Selected phi p (g (leastIndex g gen atomless p hp)) := by
  classical
  obtain ⟨E, c, w, G, hcode⟩ := adequate.exists_code
  obtain ⟨P⟩ := adequate.sound E c w G hcode
  let k := leastIndex g gen atomless p hp
  refine ⟨E, c, w, G, P.carrier, P.number k, hcode, P.carrier_isIso, ?_, ?_,
    leastIndex_spec g gen atomless p hp, ?_⟩
  · exact (P.number_range _).2 ⟨k, rfl⟩
  · exact (P.graph k _).2 rfl
  · intro m hm r hr
    obtain ⟨j, hj, hjm⟩ := (P.predecessor k m).1 hm
    have hrj : r = g j := P.carrier.injective ((P.graph j _).1 (by
      simpa only [hjm] using hr))
    simpa only [hrj] using leastIndex_min g gen atomless p hp hj

/-- The semantic value of the actual closed pure term is the least splitting
generator. The only formula-specific input is the explicitly stated coding
adequacy above; leastness and uniqueness have been derived, not assumed. -/
theorem eval_selector_eq_least [Nontrivial B] (I : Interpretation Signature.pure B)
    (phi : SetFormula 3) (g : ℕ → B) (adequate : Adequate phi g)
    (rigid : Rigid B) (gen : CompletelyGenerates g) (atomless : AtomlessParts B)
    {p : B} (hp : p ≠ ⊥) :
    eval I (selector phi) .nil p = g (leastIndex g gen atomless p hp) := by
  rw [eval_selector]
  change MaxAtomicitySplitSemantics.guardedSup (Selected phi p) = _
  apply MaxAtomicitySplitSemantics.guardedSup_eq_unique
  · exact least_selected phi g adequate gen atomless hp
  · intro q hq
    exact selected_least phi g adequate rigid gen atomless hp hq

theorem eval_selector_splits [Nontrivial B] (I : Interpretation Signature.pure B)
    (phi : SetFormula 3) (g : ℕ → B) (adequate : Adequate phi g)
    (rigid : Rigid B) (gen : CompletelyGenerates g) (atomless : AtomlessParts B)
    {p : B} (hp : p ≠ ⊥) :
    p ⊓ eval I (selector phi) .nil p ≠ ⊥ ∧
      p ⊓ (eval I (selector phi) .nil p)ᶜ ≠ ⊥ := by
  rw [eval_selector_eq_least I phi g adequate rigid gen atomless hp]
  exact leastIndex_spec g gen atomless p hp

#print axioms selector_pure
#print axioms selector_closedTypes
#print axioms eval_witnessGuard
#print axioms eval_selects
#print axioms eval_selector
#print axioms Presentation.iso_eq_carrier
#print axioms selected_least
#print axioms least_selected
#print axioms eval_selector_eq_least
#print axioms eval_selector_splits

end

end Classicism.Meta.Research.MaxAtomicityPureSelector
