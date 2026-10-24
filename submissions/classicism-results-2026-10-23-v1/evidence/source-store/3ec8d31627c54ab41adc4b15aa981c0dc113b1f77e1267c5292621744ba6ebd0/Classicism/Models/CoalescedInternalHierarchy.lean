import Classicism.Models.CoalescedInternalSyntax

/-!
# The Henkin relational hierarchy internal to a membership model

Original formalization (misc), 23 October 2026. The universe need not be
transitive, well founded, or omega-standard. Only external finite syntax is
used. Separation below is a scheme on the explicit `RawFormula` syntax;
it is not closure under arbitrary external subsets. The base sort can later
be specialized to a set model's internally represented real numbers.
-/

namespace Classicism.Meta.CoalescedInternalHierarchy

open ChoiceFirstOrder

/-- Elementary set closure and definable Separation in the finite language
with membership and primitive injective pairing. Separation includes formulas
containing that pair symbol; no conservativity over pure membership is assumed.
This is also satisfied by the usual definable Kuratowski pairing. -/
structure Universe where
  Carrier : Type
  mem : Carrier → Carrier → Prop
  ext : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  unit : Carrier
  unitSet : Carrier
  unit_mem : ∀ x, mem x unitSet ↔ x = unit
  pair : Carrier → Carrier → Carrier
  pair_injective : ∀ x y x' y', pair x y = pair x' y' → x = x' ∧ y = y'
  product : Carrier → Carrier → Carrier
  product_mem : ∀ A B z, mem z (product A B) ↔
    ∃ x y, mem x A ∧ mem y B ∧ z = pair x y
  power : Carrier → Carrier
  power_mem : ∀ A X, mem X (power A) ↔ ∀ x, mem x X → mem x A
  individuals : Carrier
  individuals_nonempty : ∃ x, mem x individuals
  separation : ∀ (Γ : Ctx) (φ : RawFormula Carrier (.e :: Γ))
    (g : RawEnv Carrier Γ) (A : Carrier),
    ∃ B, ∀ x, mem x B ↔ mem x A ∧ φ.Realize mem pair (.cons x g)

variable (U : Universe)

mutual
  /-- An internal set coding each external finite object type. -/
  def domainCode (U : Universe) : Ty → U.Carrier
    | .e => U.individuals
    | .rel ρ => U.power (tupleCode U ρ)
    | .var _ => U.individuals
  /-- An internal set coding the finite argument tuples of a relation type. -/
  def tupleCode (U : Universe) : RTy → U.Carrier
    | .t => U.unitSet
    | .arr σ ρ => U.product (domainCode U σ) (tupleCode U ρ)
end

abbrev D (σ : Ty) : Type := {x : U.Carrier // U.mem x (domainCode U σ)}

def encode (U : Universe) : (ρ : RTy) → Args (D U) ρ → U.Carrier
  | .t, _ => U.unit
  | .arr _ ρ, a => U.pair a.1.val (encode U ρ a.2)

theorem encode_mem (U : Universe) : ∀ ρ (a : Args (D U) ρ), U.mem (encode U ρ a) (tupleCode U ρ)
  | .t, _ => (U.unit_mem U.unit).mpr rfl
  | .arr σ ρ, a => (U.product_mem _ _ _).mpr
      ⟨a.1.val, encode U ρ a.2, a.1.property, encode_mem U ρ a.2, rfl⟩

theorem encode_injective (U : Universe) : ∀ ρ, Function.Injective (encode U ρ)
  | .t => by intro a b _; cases a; cases b; rfl
  | .arr σ ρ => by
    intro a b h
    have hp := U.pair_injective _ _ _ _ h
    apply Prod.ext
    · exact Subtype.ext hp.1
    · exact encode_injective U ρ hp.2

theorem encode_surjective (U : Universe) : ∀ ρ (x : U.Carrier), U.mem x (tupleCode U ρ) →
    ∃ a : Args (D U) ρ, encode U ρ a = x
  | .t, x, hx => by
    exact ⟨PUnit.unit, ((U.unit_mem x).mp hx).symm⟩
  | .arr σ ρ, x, hx => by
    obtain ⟨y, z, hy, hz, h⟩ := (U.product_mem _ _ x).mp hx
    obtain ⟨a, ha⟩ := encode_surjective U ρ z hz
    refine ⟨(⟨y, hy⟩, a), ?_⟩
    change U.pair y (encode U ρ a) = x
    rw [ha]
    exact h.symm

/-- The relation profile is actual membership in the internally coded set. -/
def rel (ρ : RTy) (X : D U (.rel ρ)) (a : Args (D U) ρ) : Prop :=
  U.mem (encode U ρ a) X.val

theorem rel_injective (ρ : RTy) : Function.Injective (rel U ρ) := by
  intro X Y h
  apply Subtype.ext
  apply U.ext
  intro z
  constructor
  · intro hz
    have ht := (U.power_mem (tupleCode U ρ) X.val).mp X.property z hz
    obtain ⟨a, ha⟩ := encode_surjective U ρ z ht
    have he := congrFun h a
    change U.mem (encode U ρ a) X.val = U.mem (encode U ρ a) Y.val at he
    rw [ha] at he
    exact (Iff.of_eq he).mp hz
  · intro hz
    have ht := (U.power_mem (tupleCode U ρ) Y.val).mp Y.property z hz
    obtain ⟨a, ha⟩ := encode_surjective U ρ z ht
    have he := congrFun h a
    change U.mem (encode U ρ a) X.val = U.mem (encode U ρ a) Y.val at he
    rw [ha] at he
    exact (Iff.of_eq he).mpr hz

def typedStructure : ChoiceFirstOrder.Structure where
  D := D U
  rel := rel U
  rel_injective := rel_injective U
  nonempty_e := by
    obtain ⟨x, hx⟩ := U.individuals_nonempty
    exact ⟨⟨x, hx⟩⟩

def eraseEnv (U : Universe) : {Γ : Ctx} → IEnv (D U) Γ → RawEnv U.Carrier Γ
  | _, .nil => .nil
  | _, .cons x g => .cons x.val (eraseEnv U g)

theorem get_eraseEnv (U : Universe) : ∀ {Γ σ} (g : IEnv (D U) Γ) (v : Var Γ σ),
    (eraseEnv U g).get v = (g.get v).val
  | _, _, .cons _ _, .zero => rfl
  | _, _, .cons _ g, .succ v => get_eraseEnv U g v

theorem eraseEnv_append (U : Universe) : ∀ {Γ Δ} (g : IEnv (D U) Γ) (h : IEnv (D U) Δ),
    eraseEnv U (appendEnv g h) = appendEnv (eraseEnv U g) (eraseEnv U h)
  | _, _, .nil, _ => rfl
  | _, _, .cons x g, h => congrArg (IEnv.cons (Dom := fun _ => U.Carrier) x.val) (eraseEnv_append U g h)

def encodeRaw (U : Universe) : (ρ : RTy) → Args (fun _ => U.Carrier) ρ → U.Carrier
  | .t, _ => U.unit
  | .arr _ ρ, a => U.pair a.1 (encodeRaw U ρ a.2)

theorem encodeRaw_values (U : Universe) : ∀ ρ (a : Args (D U) ρ),
    encodeRaw U ρ (mapArgs (fun _ x => x.val) ρ a) = encode U ρ a
  | .t, _ => rfl
  | .arr _ ρ, a => congrArg (U.pair a.1.val) (encodeRaw_values U ρ a.2)

def tupleTerm (U : Universe) {Γ : Ctx} : (ρ : RTy) → Args (fun σ => Var Γ σ) ρ → RawTerm U.Carrier Γ
  | .t, _ => .param U.unit
  | .arr _ ρ, a => .pair (.var a.1) (tupleTerm U ρ a.2)

theorem tupleTerm_eval (U : Universe) {Γ : Ctx} (g : RawEnv U.Carrier Γ) :
    ∀ ρ (a : Args (fun σ => Var Γ σ) ρ),
      (tupleTerm U ρ a).eval U.pair g =
        encodeRaw U ρ (mapArgs (fun _ v => g.get v) ρ a)
  | .t, _ => by simp only [tupleTerm, RawTerm.eval, encodeRaw]
  | .arr σ ρ, a => by
    change Var Γ σ × Args (fun τ => Var Γ τ) ρ at a
    have hv : (RawTerm.var (M := U.Carrier) (Γ := Γ) (σ := σ) a.1).eval U.pair g =
        g.get a.1 := by
      simp only [RawTerm.eval]
    simpa only [tupleTerm, RawTerm.eval, encodeRaw, mapArgs, hv] using
      congrArg (U.pair (g.get a.1)) (tupleTerm_eval U g ρ a.2)

theorem tupleTerm_eval_typed {Γ : Ctx} (g : IEnv (D U) Γ)
    (ρ : RTy) (a : Args (fun σ => Var Γ σ) ρ) :
    (tupleTerm U ρ a).eval U.pair (eraseEnv U g) =
      encode U ρ (mapArgs (fun _ v => g.get v) ρ a) := by
  rw [tupleTerm_eval]
  have he : (fun σ (v : Var Γ σ) => (eraseEnv U g).get v) =
      (fun σ (v : Var Γ σ) => (g.get v).val) := by
    funext σ v
    exact get_eraseEnv U g v
  rw [he, ← mapArgs_comp]
  exact encodeRaw_values U ρ _

/-- Finite guarded quantifier blocks. The tail is bound first, leaving the
displayed context in its original order. All raw binders still range over M. -/
def allBlock (U : Universe) : (ρ : RTy) → {Γ : Ctx} →
    RawFormula U.Carrier (ρ.args ++ Γ) → RawFormula U.Carrier Γ
  | .t, _, p => p
  | .arr σ ρ, _, p => allBlock U ρ
      (.all σ ((RawFormula.mem (.var .zero) (.param (domainCode U σ))).imp p))

def exBlock (U : Universe) : (ρ : RTy) → {Γ : Ctx} →
    RawFormula U.Carrier (ρ.args ++ Γ) → RawFormula U.Carrier Γ
  | .t, _, p => p
  | .arr σ ρ, _, p => exBlock U ρ
      (.ex σ (.conj (.mem (.var .zero) (.param (domainCode U σ))) p))

theorem realize_allBlock (U : Universe) : ∀ ρ {Γ} (p : RawFormula U.Carrier (ρ.args ++ Γ))
    (g : RawEnv U.Carrier Γ),
    (allBlock U ρ p).Realize U.mem U.pair g ↔
      ∀ a : Args (D U) ρ,
        p.Realize U.mem U.pair (appendEnv (eraseEnv U (argsEnv ρ a)) g)
  | .t, _, p, g => by
    constructor
    · intro h a; exact h
    · intro h; exact h PUnit.unit
  | .arr σ ρ, _, p, g => by
    rw [allBlock, realize_allBlock]
    change (∀ a : Args (D U) ρ, ∀ x : U.Carrier,
      ((RawFormula.mem (.var .zero) (.param (domainCode U σ))).imp p).Realize
        U.mem U.pair (.cons x (appendEnv (eraseEnv U (argsEnv ρ a)) g))) ↔ _
    constructor
    · intro h a
      apply (RawFormula.realize_imp U.mem U.pair _ _ _).mp (h a.2 a.1.val)
      simpa only [RawFormula.Realize, RawTerm.eval, IEnv.get,
        argsEnv, eraseEnv, appendEnv] using a.1.property
    · intro h a x
      apply (RawFormula.realize_imp U.mem U.pair _ _ _).mpr
      intro hx
      have hx' : U.mem x (domainCode U σ) := by
        simpa only [RawFormula.Realize, RawTerm.eval, IEnv.get] using hx
      exact h (⟨x, hx'⟩, a)

theorem realize_exBlock (U : Universe) : ∀ ρ {Γ} (p : RawFormula U.Carrier (ρ.args ++ Γ))
    (g : RawEnv U.Carrier Γ),
    (exBlock U ρ p).Realize U.mem U.pair g ↔
      ∃ a : Args (D U) ρ,
        p.Realize U.mem U.pair (appendEnv (eraseEnv U (argsEnv ρ a)) g)
  | .t, _, p, g => by
    exact ⟨fun h => ⟨PUnit.unit, h⟩, fun h => h.choose_spec⟩
  | .arr σ ρ, _, p, g => by
    rw [exBlock, realize_exBlock]
    simp only [RawFormula.Realize, RawTerm.eval, IEnv.get]
    change (∃ a : Args (D U) ρ, ∃ x : U.Carrier,
      U.mem x (domainCode U σ) ∧
        p.Realize U.mem U.pair (.cons x (appendEnv (eraseEnv U (argsEnv ρ a)) g))) ↔ _
    constructor
    · rintro ⟨a, x, hx, hp⟩
      exact ⟨(⟨x, hx⟩, a), hp⟩
    · rintro ⟨a, hp⟩
      exact ⟨a.2, a.1.val, a.1.property, hp⟩

/-- A structural translation of finite typed formulas into membership syntax. -/
def translate (U : Universe) : {Γ : Ctx} → SmallFormula Γ → RawFormula U.Carrier Γ
  | _, .equal x y => .equal (.var x) (.var y)
  | _, .rel ρ x a => .mem (tupleTerm U ρ a) (.var x)
  | _, .falsum => .falsum
  | _, .neg p => .neg (translate U p)
  | _, .conj p q => .conj (translate U p) (translate U q)
  | _, .disj p q => .disj (translate U p) (translate U q)
  | _, .all ρ p => allBlock U ρ (translate U p)
  | _, .ex ρ p => exBlock U ρ (translate U p)

theorem translate_correct (U : Universe) : ∀ {Γ} (p : SmallFormula Γ) (g : IEnv (D U) Γ),
    (translate U p).Realize U.mem U.pair (eraseEnv U g) ↔
      p.Realize (typedStructure U) g
  | _, .equal x y, g => by
    simp only [translate, RawFormula.Realize, RawTerm.eval, SmallFormula.Realize]
    rw [get_eraseEnv, get_eraseEnv]
    exact ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
  | _, .rel ρ x a, g => by
    simp only [translate, RawFormula.Realize, RawTerm.eval,
      SmallFormula.Realize, typedStructure, rel]
    rw [tupleTerm_eval_typed, get_eraseEnv]
  | _, .falsum, _ => Iff.rfl
  | _, .neg p, g => not_congr (translate_correct U p g)
  | _, .conj p q, g => and_congr (translate_correct U p g) (translate_correct U q g)
  | _, .disj p q, g => or_congr (translate_correct U p g) (translate_correct U q g)
  | _, .all ρ p, g => by
    rw [translate, realize_allBlock]
    apply forall_congr'
    intro a
    rw [← eraseEnv_append]
    exact translate_correct U p (appendEnv (argsEnv ρ a) g)
  | _, .ex ρ p, g => by
    rw [translate, realize_exBlock]
    apply exists_congr
    intro a
    rw [← eraseEnv_append]
    exact translate_correct U p (appendEnv (argsEnv ρ a) g)

def prefixVars (Γ : Ctx) (ρ : RTy) : Args (fun σ => Var (ρ.args ++ Γ) σ) ρ :=
  mapArgs (fun _ v => leftVar v) ρ (blockArgs ρ)

theorem tupleTerm_prefix_eval (ρ : RTy) {Γ : Ctx}
    (a : Args (D U) ρ) (g : RawEnv U.Carrier Γ) :
    (tupleTerm U ρ (prefixVars Γ ρ)).eval U.pair
      (appendEnv (eraseEnv U (argsEnv ρ a)) g) = encode U ρ a := by
  rw [tupleTerm_eval, prefixVars, mapArgs_comp]
  have he :
      (fun σ (v : Var ρ.args σ) =>
        (appendEnv (eraseEnv U (argsEnv ρ a)) g).get (leftVar v)) =
      (fun σ (v : Var ρ.args σ) => ((argsEnv ρ a).get v).val) := by
    funext σ v
    rw [get_append_left, get_eraseEnv]
  rw [he, ← mapArgs_comp, mapArgs_block]
  exact encodeRaw_values U ρ a

/-- The unary set-separation formula existentially decodes its tuple variable.
It needs no projection symbols and no choice of a tuple outside its code set. -/
def comprehensionBody (Γ : Ctx) (ρ : RTy) (p : SmallFormula (ρ.args ++ Γ)) :
    RawFormula U.Carrier (ρ.args ++ .e :: Γ) :=
  .conj (.equal (tupleTerm U ρ (prefixVars (.e :: Γ) ρ))
    (.var (rightVar ρ.args .zero)))
    ((translate U p).rename (insertRen .e ρ.args))

def comprehensionFormula (Γ : Ctx) (ρ : RTy) (p : SmallFormula (ρ.args ++ Γ)) :
    RawFormula U.Carrier (.e :: Γ) := exBlock U ρ (comprehensionBody U Γ ρ p)

theorem comprehensionBody_correct (Γ : Ctx) (ρ : RTy)
    (p : SmallFormula (ρ.args ++ Γ)) (g : IEnv (D U) Γ)
    (x : U.Carrier) (a : Args (D U) ρ) :
    (comprehensionBody U Γ ρ p).Realize U.mem U.pair
      (appendEnv (eraseEnv U (argsEnv ρ a)) (.cons x (eraseEnv U g))) ↔
    encode U ρ a = x ∧ p.Realize (typedStructure U) (appendEnv (argsEnv ρ a) g) := by
  simp only [comprehensionBody, RawFormula.Realize, RawTerm.eval]
  rw [tupleTerm_prefix_eval, get_append_right]
  apply and_congr Iff.rfl
  have hr := RawFormula.realize_rename U.mem U.pair (translate U p)
    (insertRen .e ρ.args)
    (appendEnv (eraseEnv U (argsEnv ρ a)) (eraseEnv U g))
    (appendEnv (eraseEnv U (argsEnv ρ a)) (.cons x (eraseEnv U g)))
    (get_insertRen .e x (eraseEnv U g) (eraseEnv U (argsEnv ρ a)))
  have hc := translate_correct U p (appendEnv (argsEnv ρ a) g)
  rw [eraseEnv_append] at hc
  exact hr.trans hc

theorem comprehensionFormula_correct (Γ : Ctx) (ρ : RTy)
    (p : SmallFormula (ρ.args ++ Γ)) (g : IEnv (D U) Γ) (x : U.Carrier) :
    (comprehensionFormula U Γ ρ p).Realize U.mem U.pair (.cons x (eraseEnv U g)) ↔
      ∃ a : Args (D U) ρ, encode U ρ a = x ∧
        p.Realize (typedStructure U) (appendEnv (argsEnv ρ a) g) := by
  rw [comprehensionFormula, realize_exBlock]
  apply exists_congr
  intro a
  exact comprehensionBody_correct U Γ ρ p g x a

/-- The full finite typed comprehension scheme, derived from definable
set-theoretic Separation and internal Power Set. -/
theorem smallComprehension : SmallComprehension (typedStructure U) := by
  intro Γ ρ p g
  obtain ⟨B, hB⟩ := U.separation Γ (comprehensionFormula U Γ ρ p)
    (eraseEnv U g) (tupleCode U ρ)
  have hpower : U.mem B (U.power (tupleCode U ρ)) := by
    apply (U.power_mem _ _).mpr
    intro x hx
    exact ((hB x).mp hx).1
  refine ⟨⟨B, hpower⟩, ?_⟩
  intro a
  change U.mem (encode U ρ a) B ↔ _
  rw [hB, comprehensionFormula_correct U Γ ρ p g (encode U ρ a)]
  constructor
  · rintro ⟨_, b, hb, hp⟩
    have he := encode_injective U ρ hb
    exact he ▸ hp
  · intro hp
    exact ⟨encode_mem U ρ a, a, rfl, hp⟩

/-- Actual closure of every externally finite typed C term. -/
theorem isModel : (typedStructure U).model.IsModel :=
  isModel_of_small_comprehension (typedStructure U) (smallComprehension U)

/-- Faithful evaluation of the finite first-order code of any closed pure
sentence, including sentences defining real structures and structural CH. -/
theorem sentence_correct (p : Sentence Signature.pure) :
    (translate U (smallSentenceTranslation p)).Realize U.mem U.pair .nil ↔
      (typedStructure U).model.HoldsSentence p :=
  (translate_correct U (smallSentenceTranslation p) .nil).trans
    (smallSentenceTranslation_correct (typedStructure U) p)

#print axioms smallComprehension
#print axioms isModel
#print axioms sentence_correct

end Classicism.Meta.CoalescedInternalHierarchy
