import Classicism.Models.ChoiceFirstOrderRecovery

-- Serial diagnostic markers; no mathematical declarations are changed.
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: imports complete"
  out.flush : IO Unit)


/-!
# An explicit first-order theory and its typed recovery

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/finite-choice-forcing-extraction-review.md` sections 2--4
(unpaginated). The axioms are actual Mathlib sentences: individual
nonemptiness, relational extensionality, and the finite-context definable
comprehension scheme. Their typed syntax is translated with the previously
defined sort guards. No sort-disjointness or coverage axiom is needed.

Every model of these explicit sentences supplies the actual project
`Structure`, its `SmallComprehension`, and hence `Premodel.IsModel`.
No model-existence, Choice, completeness, or forcing-extraction theorem is
assumed. This new module is separate from the frozen first audit batch.
-/

namespace Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory

open Recovery

/-- Lift a variable renaming past an unchanged finite prefix. -/
def liftMany {Γ Δ : Ctx} (r : ∀ σ, Var Γ σ → Var Δ σ) :
    ∀ (Ξ : Ctx) (σ : Ty), Var (Ξ ++ Γ) σ → Var (Ξ ++ Δ) σ
  | [], σ, v => r σ v
  | _ :: _, _, .zero => .zero
  | _ :: Ξ, _, .succ v => .succ (liftMany r Ξ _ v)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin get_liftMany"
  out.flush : IO Unit)

theorem get_liftMany {D : Ty → Type} {Γ Δ : Ctx}
    (r : ∀ σ, Var Γ σ → Var Δ σ) (g : IEnv D Γ) (h : IEnv D Δ)
    (hg : ∀ σ v, h.get (r σ v) = g.get v) :
    ∀ {Ξ : Ctx} (k : IEnv D Ξ) (σ : Ty) (v : Var (Ξ ++ Γ) σ),
      (appendEnv k h).get (liftMany r Ξ σ v) = (appendEnv k g).get v
  | _, .nil, σ, v => hg σ v
  | _, .cons _ _, _, .zero => rfl
  | _, .cons _ k, σ, .succ v => get_liftMany r g h hg k σ v

/-- Capture-free renaming in the actual finite typed syntax. -/
def rename : ∀ {Γ Δ : Ctx}, (∀ σ, Var Γ σ → Var Δ σ) →
    SmallFormula Γ → SmallFormula Δ
  | _, _, r, .equal x y => .equal (r _ x) (r _ y)
  | _, _, r, .rel ρ x a => .rel ρ (r _ x) (mapArgs r ρ a)
  | _, _, _, .falsum => .falsum
  | _, _, r, .neg p => .neg (rename r p)
  | _, _, r, .conj p q => .conj (rename r p) (rename r q)
  | _, _, r, .disj p q => .disj (rename r p) (rename r q)
  | _, _, r, .all ρ p => .all ρ (rename (liftMany r ρ.args) p)
  | _, _, r, .ex ρ p => .ex ρ (rename (liftMany r ρ.args) p)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_rename_correct"
  out.flush : IO Unit)

theorem raw_rename_correct (M : Type) [language.Structure M] :
    ∀ {Γ Δ : Ctx} (φ : SmallFormula Γ) (r : ∀ σ, Var Γ σ → Var Δ σ)
      (g : IEnv (D M) Γ) (h : IEnv (D M) Δ),
      (∀ σ v, h.get (r σ v) = g.get v) →
      (RawRealize M (rename r φ) h ↔ RawRealize M φ g)
  | _, _, .equal x y, r, g, h, hg => by
    change h.get (r _ x) = h.get (r _ y) ↔ g.get x = g.get y
    rw [hg, hg]
  | _, _, .rel ρ x a, r, g, h, hg => by
    change rel M ρ (h.get (r _ x))
      (mapArgs (fun _ v => h.get v) ρ (mapArgs r ρ a)) ↔
      rel M ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ a)
    rw [mapArgs_comp, hg]
    have hv : (fun σ v => h.get (r σ v)) = (fun σ v => g.get v) := by
      funext σ v
      exact hg σ v
    rw [hv]
  | _, _, .falsum, _, _, _, _ => Iff.rfl
  | _, _, .neg p, r, g, h, hg => not_congr (raw_rename_correct M p r g h hg)
  | _, _, .conj p q, r, g, h, hg =>
      and_congr (raw_rename_correct M p r g h hg) (raw_rename_correct M q r g h hg)
  | _, _, .disj p q, r, g, h, hg =>
      or_congr (raw_rename_correct M p r g h hg) (raw_rename_correct M q r g h hg)
  | _, _, .all ρ p, r, g, h, hg => by
    change (∀ a : Args (D M) ρ, _) ↔ ∀ a : Args (D M) ρ, _
    exact forall_congr' (fun a => raw_rename_correct M p (liftMany r ρ.args)
      (appendEnv (argsEnv ρ a) g) (appendEnv (argsEnv ρ a) h)
      (get_liftMany r g h hg (argsEnv ρ a)))
  | _, _, .ex ρ p, r, g, h, hg => by
    change (∃ a : Args (D M) ρ, _) ↔ ∃ a : Args (D M) ρ, _
    exact exists_congr (fun a => raw_rename_correct M p (liftMany r ρ.args)
      (appendEnv (argsEnv ρ a) g) (appendEnv (argsEnv ρ a) h)
      (get_liftMany r g h hg (argsEnv ρ a)))

def smallImp {Γ : Ctx} (p q : SmallFormula Γ) : SmallFormula Γ := .disj (.neg p) q
def smallIff {Γ : Ctx} (p q : SmallFormula Γ) : SmallFormula Γ :=
  .conj (smallImp p q) (smallImp q p)
def smallTrue {Γ : Ctx} : SmallFormula Γ := .neg .falsum

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_imp_correct"
  out.flush : IO Unit)

theorem raw_imp_correct (M : Type) [language.Structure M] {Γ : Ctx}
    (p q : SmallFormula Γ) (g : IEnv (D M) Γ) :
    RawRealize M (smallImp p q) g ↔ (RawRealize M p g → RawRealize M q g) := by
  classical
  change (¬RawRealize M p g ∨ RawRealize M q g) ↔ _
  constructor
  · intro h hp
    exact h.elim (fun hn => False.elim (hn hp)) id
  · intro h
    by_cases hp : RawRealize M p g
    · exact Or.inr (h hp)
    · exact Or.inl hp

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_iff_correct"
  out.flush : IO Unit)

theorem raw_iff_correct (M : Type) [language.Structure M] {Γ : Ctx}
    (p q : SmallFormula Γ) (g : IEnv (D M) Γ) :
    RawRealize M (smallIff p q) g ↔ (RawRealize M p g ↔ RawRealize M q g) := by
  change (RawRealize M (smallImp p q) g ∧ RawRealize M (smallImp q p) g) ↔ _
  rw [raw_imp_correct, raw_imp_correct]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

def allOne (σ : Ty) {Γ : Ctx} (φ : SmallFormula (σ :: Γ)) : SmallFormula Γ :=
  .all (.arr σ .t) φ

def exOne (σ : Ty) {Γ : Ctx} (φ : SmallFormula (σ :: Γ)) : SmallFormula Γ :=
  .ex (.arr σ .t) φ

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_allOne_correct"
  out.flush : IO Unit)

theorem raw_allOne_correct (M : Type) [language.Structure M] (σ : Ty) {Γ : Ctx}
    (φ : SmallFormula (σ :: Γ)) (g : IEnv (D M) Γ) :
    RawRealize M (allOne σ φ) g ↔ ∀ x : D M σ, RawRealize M φ (.cons x g) := by
  change (∀ a : D M σ × PUnit, RawRealize M φ (.cons a.1 g)) ↔ _
  exact ⟨fun h x => h (x, PUnit.unit), fun h a => h a.1⟩

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_exOne_correct"
  out.flush : IO Unit)

theorem raw_exOne_correct (M : Type) [language.Structure M] (σ : Ty) {Γ : Ctx}
    (φ : SmallFormula (σ :: Γ)) (g : IEnv (D M) Γ) :
    RawRealize M (exOne σ φ) g ↔ ∃ x : D M σ, RawRealize M φ (.cons x g) := by
  change (∃ a : D M σ × PUnit, RawRealize M φ (.cons a.1 g)) ↔ _
  exact ⟨fun ⟨a, h⟩ => ⟨a.1, h⟩, fun ⟨x, h⟩ => ⟨(x, PUnit.unit), h⟩⟩

/-- Universal closure over the finite parameter context. -/
def allContext : ∀ (Γ : Ctx), SmallFormula Γ → SmallFormula []
  | [], φ => φ
  | σ :: Γ, φ => allContext Γ (allOne σ φ)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_allContext_correct"
  out.flush : IO Unit)

theorem raw_allContext_correct (M : Type) [language.Structure M] :
    ∀ (Γ : Ctx) (φ : SmallFormula Γ),
      RawRealize M (allContext Γ φ) .nil ↔
        ∀ g : IEnv (D M) Γ, RawRealize M φ g
  | [], φ => by
    constructor
    · intro h g
      cases g
      exact h
    · intro h
      exact h .nil
  | σ :: Γ, φ => by
    rw [allContext, raw_allContext_correct]
    constructor
    · intro h g
      cases g with
      | cons x g => exact (raw_allOne_correct M σ φ g).mp (h g) x
    · intro h g
      exact (raw_allOne_correct M σ φ g).mpr (fun x => h (.cons x g))

/-- The argument variables occupy the unchanged prefix of the context. -/
def prefixArgs (Γ : Ctx) (ρ : RTy) : Args (fun σ => Var (ρ.args ++ Γ) σ) ρ :=
  mapArgs (fun _ v => leftVar (Δ := Γ) v) ρ (blockArgs ρ)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin eval_prefixArgs"
  out.flush : IO Unit)

theorem eval_prefixArgs {D : Ty → Type} (Γ : Ctx) (ρ : RTy)
    (a : Args D ρ) (g : IEnv D Γ) :
    mapArgs (fun _ v => (appendEnv (argsEnv ρ a) g).get v) ρ (prefixArgs Γ ρ) = a := by
  rw [prefixArgs, mapArgs_comp]
  have hv : (fun (σ : Ty) (v : Var ρ.args σ) =>
      (appendEnv (argsEnv ρ a) g).get (leftVar (Δ := Γ) v)) =
      (fun (σ : Ty) (v : Var ρ.args σ) => (argsEnv ρ a).get v) := by
    funext σ v
    exact get_append_left (argsEnv ρ a) g v
  rw [hv]
  exact mapArgs_block ρ a

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_profile_prefix"
  out.flush : IO Unit)

theorem raw_profile_prefix (M : Type) [language.Structure M] {Γ : Ctx}
    (ρ : RTy) (v : Var Γ (.rel ρ)) (a : Args (D M) ρ) (g : IEnv (D M) Γ) :
    RawRealize M (.rel ρ (rightVar ρ.args v) (prefixArgs Γ ρ))
      (appendEnv (argsEnv ρ a) g) ↔ rel M ρ (g.get v) a := by
  change rel M ρ ((appendEnv (argsEnv ρ a) g).get (rightVar ρ.args v))
    (mapArgs (fun _ v => (appendEnv (argsEnv ρ a) g).get v) ρ (prefixArgs Γ ρ)) ↔ _
  rw [get_append_right, eval_prefixArgs]

def nonemptySmall : SmallFormula [] := exOne .e smallTrue

def extBody (ρ : RTy) : SmallFormula [.rel ρ, .rel ρ] :=
  smallImp
    (.all ρ (smallIff
      (.rel ρ (rightVar ρ.args Var.zero) (prefixArgs [.rel ρ, .rel ρ] ρ))
      (.rel ρ (rightVar ρ.args (Var.succ Var.zero)) (prefixArgs [.rel ρ, .rel ρ] ρ))))
    (.equal Var.zero (Var.succ Var.zero))

def extensionalitySmall (ρ : RTy) : SmallFormula [] :=
  allContext [.rel ρ, .rel ρ] (extBody ρ)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_extBody_correct"
  out.flush : IO Unit)

theorem raw_extBody_correct (M : Type) [language.Structure M] (ρ : RTy)
    (X Y : D M (.rel ρ)) :
    RawRealize M (extBody ρ) (.cons X (.cons Y .nil)) ↔
      ((∀ a : Args (D M) ρ, rel M ρ X a ↔ rel M ρ Y a) → X = Y) := by
  rw [extBody, raw_imp_correct]
  have hc : RawRealize M
      (.all ρ (smallIff
        (.rel ρ (rightVar ρ.args Var.zero) (prefixArgs [.rel ρ, .rel ρ] ρ))
        (.rel ρ (rightVar ρ.args (Var.succ Var.zero)) (prefixArgs [.rel ρ, .rel ρ] ρ))))
      (.cons X (.cons Y .nil)) ↔
      ∀ a : Args (D M) ρ, rel M ρ X a ↔ rel M ρ Y a := by
    change (∀ a : Args (D M) ρ, _) ↔ ∀ a : Args (D M) ρ, _
    apply forall_congr'
    intro a
    rw [raw_iff_correct, raw_profile_prefix, raw_profile_prefix]
    rfl
  rw [hc]
  rfl

/-- Insert the new relational witness after the argument block. -/
def insertWitness {Γ : Ctx} (ρ : RTy) (φ : SmallFormula (ρ.args ++ Γ)) :
    SmallFormula (ρ.args ++ (.rel ρ :: Γ)) :=
  rename (liftMany (fun _ v => Var.succ v) ρ.args) φ

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_insertWitness_correct"
  out.flush : IO Unit)

theorem raw_insertWitness_correct (M : Type) [language.Structure M] {Γ : Ctx}
    (ρ : RTy) (φ : SmallFormula (ρ.args ++ Γ)) (X : D M (.rel ρ))
    (a : Args (D M) ρ) (g : IEnv (D M) Γ) :
    RawRealize M (insertWitness ρ φ) (appendEnv (argsEnv ρ a) (.cons X g)) ↔
      RawRealize M φ (appendEnv (argsEnv ρ a) g) := by
  exact raw_rename_correct M φ (liftMany (fun _ v => Var.succ v) ρ.args)
    (appendEnv (argsEnv ρ a) g) (appendEnv (argsEnv ρ a) (.cons X g))
    (get_liftMany (fun _ v => Var.succ v) g (.cons X g)
      (fun _ _ => rfl) (argsEnv ρ a))

def comprehensionBody (Γ : Ctx) (ρ : RTy) (φ : SmallFormula (ρ.args ++ Γ)) :
    SmallFormula Γ :=
  exOne (.rel ρ) (.all ρ (smallIff
    (.rel ρ (rightVar ρ.args Var.zero) (prefixArgs (.rel ρ :: Γ) ρ))
    (insertWitness ρ φ)))

def comprehensionSmall (Γ : Ctx) (ρ : RTy) (φ : SmallFormula (ρ.args ++ Γ)) :
    SmallFormula [] := allContext Γ (comprehensionBody Γ ρ φ)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin raw_comprehensionBody_correct"
  out.flush : IO Unit)

theorem raw_comprehensionBody_correct (M : Type) [language.Structure M]
    (Γ : Ctx) (ρ : RTy) (φ : SmallFormula (ρ.args ++ Γ)) (g : IEnv (D M) Γ) :
    RawRealize M (comprehensionBody Γ ρ φ) g ↔
      ∃ X : D M (.rel ρ), ∀ a : Args (D M) ρ,
        rel M ρ X a ↔ RawRealize M φ (appendEnv (argsEnv ρ a) g) := by
  rw [comprehensionBody, raw_exOne_correct]
  apply exists_congr
  intro X
  change (∀ a : Args (D M) ρ, _) ↔ ∀ a : Args (D M) ρ, _
  apply forall_congr'
  intro a
  rw [raw_iff_correct, raw_profile_prefix, raw_insertWitness_correct]
  rfl

/-- Countably indexed actual sentence axioms, not semantic verdict fields. -/
abbrev AxiomIndex := Unit ⊕ (RTy ⊕ SmallComprehensionIndex)

def axiomSmall : AxiomIndex → SmallFormula []
  | .inl _ => nonemptySmall
  | .inr (.inl ρ) => extensionalitySmall ρ
  | .inr (.inr ⟨Γ, ρ, φ⟩) => comprehensionSmall Γ ρ φ

def axiomSentence (i : AxiomIndex) : language.Sentence := translate (axiomSmall i)

def theory : language.Theory := Set.range axiomSentence

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin axiomIndex_countable"
  out.flush : IO Unit)

theorem axiomIndex_countable : Countable AxiomIndex := inferInstance

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin theory_countable"
  out.flush : IO Unit)

theorem theory_countable : theory.Countable := Set.countable_range axiomSentence

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin nonempty_sentence_correct"
  out.flush : IO Unit)

theorem nonempty_sentence_correct (M : Type) [language.Structure M] :
    FirstOrder.Language.Sentence.Realize M (axiomSentence (.inl ())) ↔
      Nonempty (D M .e) := by
  rw [axiomSentence, Recovery.raw_sentence_correct]
  change RawRealize M (exOne .e smallTrue) .nil ↔ _
  rw [raw_exOne_correct]
  constructor
  · rintro ⟨x, _⟩
    exact ⟨x⟩
  · rintro ⟨x⟩
    exact ⟨x, fun h => h⟩

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin extensionality_sentence_correct"
  out.flush : IO Unit)

theorem extensionality_sentence_correct (M : Type) [language.Structure M] (ρ : RTy) :
    FirstOrder.Language.Sentence.Realize M (axiomSentence (.inr (.inl ρ))) ↔
      Function.Injective (rel M ρ) := by
  rw [axiomSentence, Recovery.raw_sentence_correct]
  change RawRealize M (allContext [.rel ρ, .rel ρ] (extBody ρ)) .nil ↔ _
  rw [raw_allContext_correct]
  constructor
  · intro h X Y hXY
    apply (raw_extBody_correct M ρ X Y).mp (h (.cons X (.cons Y .nil)))
    intro a
    exact iff_of_eq (congrFun hXY a)
  · intro h g
    cases g with
    | cons X g =>
      cases g with
      | cons Y g =>
        cases g
        apply (raw_extBody_correct M ρ X Y).mpr
        intro hXY
        exact h (funext (fun a => propext (hXY a)))

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin comprehension_sentence_correct"
  out.flush : IO Unit)

theorem comprehension_sentence_correct (M : Type) [language.Structure M]
    (Γ : Ctx) (ρ : RTy) (φ : SmallFormula (ρ.args ++ Γ)) :
    FirstOrder.Language.Sentence.Realize M
      (axiomSentence (.inr (.inr ⟨Γ, ρ, φ⟩))) ↔
      ∀ g : IEnv (D M) Γ, ∃ X : D M (.rel ρ), ∀ a : Args (D M) ρ,
        rel M ρ X a ↔ RawRealize M φ (appendEnv (argsEnv ρ a) g) := by
  rw [axiomSentence, Recovery.raw_sentence_correct]
  change RawRealize M (allContext Γ (comprehensionBody Γ ρ φ)) .nil ↔ _
  rw [raw_allContext_correct]
  exact forall_congr' (fun g => raw_comprehensionBody_correct M Γ ρ φ g)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin model_nonempty"
  out.flush : IO Unit)

theorem model_nonempty (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M theory) : Nonempty (D M .e) :=
  (nonempty_sentence_correct M).mp
    (hT.realize_of_mem _ ⟨.inl (), rfl⟩)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin model_extensional"
  out.flush : IO Unit)

theorem model_extensional (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M theory) :
    ∀ ρ, Function.Injective (rel M ρ) :=
  fun ρ => (extensionality_sentence_correct M ρ).mp
    (hT.realize_of_mem _ ⟨.inr (.inl ρ), rfl⟩)

/-- The structure fields are proved from the displayed sentence axioms. -/
def recoveredStructure (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M theory) : Structure :=
  Recovery.recoverStructure M (model_nonempty M hT) (model_extensional M hT)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin recovered_smallComprehension"
  out.flush : IO Unit)

theorem recovered_smallComprehension (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M theory) :
    SmallComprehension (recoveredStructure M hT) := by
  intro Γ ρ φ g
  have hc := (comprehension_sentence_correct M Γ ρ φ).mp
    (hT.realize_of_mem _ ⟨.inr (.inr ⟨Γ, ρ, φ⟩), rfl⟩)
  obtain ⟨X, hX⟩ := hc g
  refine ⟨X, fun a => ?_⟩
  exact (hX a).trans (Recovery.rawRealize_recoverStructure M
    (model_nonempty M hT) (model_extensional M hT) φ (appendEnv (argsEnv ρ a) g))

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin recovered_isModel"
  out.flush : IO Unit)

theorem recovered_isModel (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M theory) :
    (recoveredStructure M hT).model.IsModel :=
  isModel_of_small_comprehension (recoveredStructure M hT) (recovered_smallComprehension M hT)

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin recovered_sentence_correct"
  out.flush : IO Unit)

theorem recovered_sentence_correct (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M theory) (p : Sentence Signature.pure) :
    FirstOrder.Language.Sentence.Realize M (MathlibBridge.sentence p) ↔
      (recoveredStructure M hT).model.HoldsSentence p :=
  Recovery.sentence_correct M (model_nonempty M hT) (model_extensional M hT) p

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: begin recovered_c_theorem_holds"
  out.flush : IO Unit)

theorem recovered_c_theorem_holds (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M theory)
    {p : Sentence Signature.pure} (hp : C.Theorem p) :
    (recoveredStructure M hT).model.HoldsSentence p :=
  (recoveredStructure M hT).model.theorem_holds (recovered_isModel M hT) hp

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Choice AxiomTheory: complete"
  out.flush : IO Unit)

end Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory
