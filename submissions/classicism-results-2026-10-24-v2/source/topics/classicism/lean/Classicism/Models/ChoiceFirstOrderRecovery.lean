import Classicism.Models.ChoiceFirstOrderMathlib

/-!
# Recovering sorted semantics from an arbitrary first-order structure

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/finite-choice-forcing-extraction-review.md` sections 2--4
(unpaginated). The domains are the unary-sort subtypes of an arbitrary
Mathlib structure. Application is its finite-arity profile relation on
underlying values. The guarded translation preserves this raw semantics
without nonemptiness, extensionality, comprehension, or model-existence
premises. Concrete individual nonemptiness and relational extensionality
then assemble the existing `ChoiceFirstOrder.Structure`.

No completeness or extraction theorem is assumed or asserted here.
-/

namespace Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery

def SortPred (M : Type) [language.Structure M] (σ : Ty) (x : M) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := language) (Relation.sort σ) (fun _ => x)

abbrev D (M : Type) [language.Structure M] (σ : Ty) := {x : M // SortPred M σ x}

def rel (M : Type) [language.Structure M] (ρ : RTy) (X : D M (.rel ρ)) (a : Args (D M) ρ) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := language) (Relation.profile ρ)
    (Fin.cons X.val (flatten (fun σ (x : D M σ) => x.val) ρ a))

theorem profile_correct (M : Type) [language.Structure M] (ρ : RTy) (X : D M (.rel ρ)) (a : Args (D M) ρ) :
    FirstOrder.Language.Structure.RelMap (L := language) (Relation.profile ρ)
      (Fin.cons X.val (flatten (fun σ (x : D M σ) => x.val) ρ a)) ↔ rel M ρ X a :=
  Iff.rfl

def recoverStructure (M : Type) [language.Structure M] (he : Nonempty (D M .e))
    (hx : ∀ ρ, Function.Injective (rel M ρ)) : Structure where
  D := D M
  rel := rel M
  rel_injective := hx
  nonempty_e := he

/-- The raw sorted semantics exists even before the structure axioms are
verified. Quantifiers range only over the appropriate unary-sort subtypes. -/
def RawRealize (M : Type) [language.Structure M] : {Γ : Ctx} → SmallFormula Γ → IEnv (D M) Γ → Prop
  | _, .equal x y, g => g.get x = g.get y
  | _, .rel ρ x a, g => rel M ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ a)
  | _, .falsum, _ => False
  | _, .neg p, g => ¬ RawRealize M p g
  | _, .conj p q, g => RawRealize M p g ∧ RawRealize M q g
  | _, .disj p q, g => RawRealize M p g ∨ RawRealize M q g
  | _, .all ρ p, g => ∀ a : Args (D M) ρ,
      RawRealize M p (appendEnv (argsEnv ρ a) g)
  | _, .ex ρ p, g => ∃ a : Args (D M) ρ,
      RawRealize M p (appendEnv (argsEnv ρ a) g)

def envVector (M : Type) [language.Structure M] : ∀ {Γ : Ctx}, IEnv (D M) Γ → Fin Γ.length → M
  | [], .nil => Fin.elim0
  | _ :: _, .cons x g => Fin.snoc (envVector M g) x.val

theorem variable_correct (M : Type) [language.Structure M] : ∀ {Γ : Ctx} {σ : Ty}
    (v : Var Γ σ) (g : IEnv (D M) Γ),
    (variableTerm v).realize (Sum.elim Empty.elim (envVector M g)) = (g.get v).val
  | _, _, .zero, .cons x g => by
    simp only [variableTerm, FirstOrder.Language.Term.realize, Sum.elim_inr,
      variableIndex, envVector, Fin.snoc_last, IEnv.get]
  | _, _, .succ v, .cons x g => by
    simpa only [variableTerm, FirstOrder.Language.Term.realize, Sum.elim_inr,
      variableIndex, envVector, Fin.snoc_castSucc, IEnv.get] using variable_correct M v g

theorem flatten_variables_correct (M : Type) [language.Structure M] {Γ : Ctx} (g : IEnv (D M) Γ) :
    ∀ ρ (a : Args (fun σ => Var Γ σ) ρ),
    (fun i => (flatten (fun _ v => variableTerm v) ρ a i).realize
      (Sum.elim Empty.elim (envVector M g))) =
      flatten (fun σ (x : D M σ) => x.val) ρ (mapArgs (fun _ v => g.get v) ρ a)
  | .t, _ => by funext i; exact i.elim0
  | .arr σ ρ, a => by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [flatten, mapArgs, Fin.cons_zero] using variable_correct M a.1 g
    · simpa only [flatten, mapArgs, Fin.cons_succ] using
        congrFun (flatten_variables_correct M g ρ a.2) j

def realizeAt (M : Type) [language.Structure M] {Γ : Ctx} (φ : FormulaAt Γ) (g : IEnv (D M) Γ) : Prop :=
  φ.Realize Empty.elim (envVector M g)

theorem guardedAll_correct (M : Type) [language.Structure M] (σ : Ty) {Γ : Ctx}
    (φ : FormulaAt (σ :: Γ)) (g : IEnv (D M) Γ) :
    realizeAt M (guardedAll σ (Γ := Γ) φ) g ↔
      ∀ x : D M σ, realizeAt M φ (.cons x g) := by
  change (∀ z : M,
    SortPred M σ (Fin.snoc (α := fun _ : Fin (Γ.length + 1) => M)
      (envVector M g) z (Fin.last Γ.length)) →
      φ.Realize Empty.elim (Fin.snoc (envVector M g) z)) ↔
    ∀ x : D M σ, φ.Realize Empty.elim (Fin.snoc (envVector M g) x.val)
  simp only [Fin.snoc_last]
  constructor
  · intro h x
    exact h x.val x.property
  · intro h z hz
    exact h ⟨z, hz⟩

theorem guardedEx_correct (M : Type) [language.Structure M] (σ : Ty) {Γ : Ctx}
    (φ : FormulaAt (σ :: Γ)) (g : IEnv (D M) Γ) :
    realizeAt M (guardedEx σ (Γ := Γ) φ) g ↔
      ∃ x : D M σ, realizeAt M φ (.cons x g) := by
  simp only [realizeAt, guardedEx, FirstOrder.Language.BoundedFormula.realize_ex,
    FirstOrder.Language.BoundedFormula.realize_inf]
  change (∃ z : M,
    SortPred M σ (Fin.snoc (α := fun _ : Fin (Γ.length + 1) => M)
      (envVector M g) z (Fin.last Γ.length)) ∧
      φ.Realize Empty.elim (Fin.snoc (envVector M g) z)) ↔
    ∃ x : D M σ, φ.Realize Empty.elim (Fin.snoc (envVector M g) x.val)
  simp only [Fin.snoc_last]
  constructor
  · rintro ⟨z, hz, h⟩
    exact ⟨⟨z, hz⟩, h⟩
  · rintro ⟨x, h⟩
    exact ⟨x.val, x.property, h⟩

theorem allArgs_correct (M : Type) [language.Structure M] : ∀ (ρ : RTy) (Γ : Ctx)
    (φ : FormulaAt (ρ.args ++ Γ)) (g : IEnv (D M) Γ),
    realizeAt M (allArgs ρ Γ φ) g ↔
      ∀ a : Args (D M) ρ, realizeAt M φ (appendEnv (argsEnv ρ a) g)
  | .t, _, _, _ => ⟨fun h _ => h, fun h => h PUnit.unit⟩
  | .arr σ ρ, Γ, φ, g => by
    rw [allArgs, allArgs_correct]
    constructor
    · intro h a
      exact (guardedAll_correct M σ φ (appendEnv (argsEnv ρ a.2) g)).mp (h a.2) a.1
    · intro h a
      exact (guardedAll_correct M σ φ (appendEnv (argsEnv ρ a) g)).mpr
        (fun x => h (x, a))

theorem exArgs_correct (M : Type) [language.Structure M] : ∀ (ρ : RTy) (Γ : Ctx)
    (φ : FormulaAt (ρ.args ++ Γ)) (g : IEnv (D M) Γ),
    realizeAt M (exArgs ρ Γ φ) g ↔
      ∃ a : Args (D M) ρ, realizeAt M φ (appendEnv (argsEnv ρ a) g)
  | .t, _, _, _ => ⟨fun h => ⟨PUnit.unit, h⟩, fun ⟨_, h⟩ => h⟩
  | .arr σ ρ, Γ, φ, g => by
    rw [exArgs, exArgs_correct]
    constructor
    · rintro ⟨a, h⟩
      obtain ⟨x, hx⟩ := (guardedEx_correct M σ φ (appendEnv (argsEnv ρ a) g)).mp h
      exact ⟨(x, a), hx⟩
    · rintro ⟨⟨x, a⟩, h⟩
      exact ⟨a, (guardedEx_correct M σ φ (appendEnv (argsEnv ρ a) g)).mpr ⟨x, h⟩⟩

/-- The guarded Mathlib translation is correct for every arbitrary
first-order structure, before any theory axioms are imposed. -/
theorem raw_translate_correct (M : Type) [language.Structure M] : ∀ {Γ : Ctx} (φ : SmallFormula Γ)
    (g : IEnv (D M) Γ), realizeAt M (translate φ) g ↔ RawRealize M φ g
  | _, .equal x y, g => by
    change (variableTerm x).realize (Sum.elim Empty.elim (envVector M g)) =
      (variableTerm y).realize (Sum.elim Empty.elim (envVector M g)) ↔ g.get x = g.get y
    rw [variable_correct, variable_correct]
    exact ⟨Subtype.ext, congrArg Subtype.val⟩
  | Γ, .rel ρ x a, g => by
    change FirstOrder.Language.Structure.RelMap (L := language) (Relation.profile ρ)
      (fun i : Fin (ρ.args.length + 1) =>
        (Fin.cons (α := fun _ => language.Term (Empty ⊕ Fin Γ.length)) (variableTerm x)
        (flatten (fun _ v => variableTerm v) ρ a) i).realize
          (Sum.elim Empty.elim (envVector M g))) ↔
      rel M ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ a)
    have hv : (fun i : Fin (ρ.args.length + 1) =>
        (Fin.cons (α := fun _ => language.Term (Empty ⊕ Fin Γ.length)) (variableTerm x)
        (flatten (fun _ v => variableTerm v) ρ a) i).realize
          (Sum.elim Empty.elim (envVector M g))) =
        Fin.cons (α := fun _ : Fin (ρ.args.length + 1) => M) (g.get x).val
          (flatten (fun σ (v : D M σ) => v.val) ρ
            (mapArgs (fun _ v => g.get v) ρ a)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using variable_correct M x g
      · simpa only [Fin.cons_succ] using congrFun (flatten_variables_correct M g ρ a) j
    rw [hv]
    exact profile_correct M ρ (g.get x) (mapArgs (fun _ v => g.get v) ρ a)
  | _, .falsum, _ => Iff.rfl
  | _, .neg p, g => not_congr (raw_translate_correct M p g)
  | _, .conj p q, g =>
      FirstOrder.Language.BoundedFormula.realize_inf.trans
        (and_congr (raw_translate_correct M p g) (raw_translate_correct M q g))
  | _, .disj p q, g =>
      FirstOrder.Language.BoundedFormula.realize_sup.trans
        (or_congr (raw_translate_correct M p g) (raw_translate_correct M q g))
  | Γ, .all ρ p, g =>
      (allArgs_correct M ρ Γ (translate p) g).trans
        (forall_congr' (fun a => raw_translate_correct M p (appendEnv (argsEnv ρ a) g)))
  | Γ, .ex ρ p, g =>
      (exArgs_correct M ρ Γ (translate p) g).trans
        (exists_congr (fun a => raw_translate_correct M p (appendEnv (argsEnv ρ a) g)))

/-- Any closed small formula, including the explicit theory axioms, has
the same truth value in Mathlib and in the recovered raw sorted semantics. -/
theorem raw_sentence_correct (M : Type) [language.Structure M] (φ : SmallFormula []) :
    FirstOrder.Language.Sentence.Realize M (translate φ) ↔ RawRealize M φ .nil := by
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  have hz : (default : Fin 0 → M) = Fin.elim0 := Subsingleton.elim _ _
  change (translate φ).Realize (default : Empty → M) (default : Fin 0 → M) ↔ _
  rw [he, hz]
  exact raw_translate_correct M φ .nil

theorem rawRealize_recoverStructure (M : Type) [language.Structure M] (he : Nonempty (D M .e))
    (hx : ∀ ρ, Function.Injective (rel M ρ)) :
    ∀ {Γ : Ctx} (φ : SmallFormula Γ) (g : IEnv (D M) Γ),
      RawRealize M φ g ↔ φ.Realize (recoverStructure M he hx) g
  | _, .equal _ _, _ => Iff.rfl
  | _, .rel _ _ _, _ => Iff.rfl
  | _, .falsum, _ => Iff.rfl
  | _, .neg p, g => not_congr (rawRealize_recoverStructure M he hx p g)
  | _, .conj p q, g => and_congr
      (rawRealize_recoverStructure M he hx p g) (rawRealize_recoverStructure M he hx q g)
  | _, .disj p q, g => or_congr
      (rawRealize_recoverStructure M he hx p g) (rawRealize_recoverStructure M he hx q g)
  | _, .all ρ p, g => forall_congr' (fun a =>
      rawRealize_recoverStructure M he hx p (appendEnv (argsEnv ρ a) g))
  | _, .ex ρ p, g => exists_congr (fun a =>
      rawRealize_recoverStructure M he hx p (appendEnv (argsEnv ρ a) g))

theorem translate_correct (M : Type) [language.Structure M] (he : Nonempty (D M .e))
    (hx : ∀ ρ, Function.Injective (rel M ρ)) {Γ : Ctx}
    (φ : SmallFormula Γ) (g : IEnv (D M) Γ) :
    realizeAt M (translate φ) g ↔ φ.Realize (recoverStructure M he hx) g :=
  (raw_translate_correct M φ g).trans (rawRealize_recoverStructure M he hx φ g)

/-- The sentence bridge uses only the concrete structural facts needed to
assemble the premodel. Its term-closure theorem is a later consequence of
the explicit first-order comprehension axioms. -/
theorem sentence_correct (M : Type) [language.Structure M] (he : Nonempty (D M .e))
    (hx : ∀ ρ, Function.Injective (rel M ρ)) (p : Sentence Signature.pure) :
    FirstOrder.Language.Sentence.Realize M (sentence p) ↔
      (recoverStructure M he hx).model.HoldsSentence p := by
  have he' : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  have hz : (default : Fin 0 → M) = Fin.elim0 := Subsingleton.elim _ _
  change (translate (smallSentenceTranslation p)).Realize
    (default : Empty → M) (default : Fin 0 → M) ↔ _
  rw [he', hz]
  exact (translate_correct M he hx (smallSentenceTranslation p) .nil).trans
    (smallSentenceTranslation_correct (recoverStructure M he hx) p)

end Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery
