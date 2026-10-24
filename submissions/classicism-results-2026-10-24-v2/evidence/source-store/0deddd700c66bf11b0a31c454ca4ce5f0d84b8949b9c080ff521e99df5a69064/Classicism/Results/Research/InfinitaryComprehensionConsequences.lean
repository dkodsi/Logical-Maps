import Classicism.Results.Research.InfinitaryComprehensionSyntax

/-!
# A concrete infinitary modal proof of the named-exhaustion step

Original source: `research/2026-10-23/infinitary-comprehension/
logical-observer-separation.md`, §2; misc, 23 October 2026.

This module defines an inductive natural-deduction fragment over the actual
infinitary lambda-free syntax. It is not an interpretation of object formulas
as Lean propositions. Its rules are implication, conjunction, arbitrary
conjunction/disjunction, ordinary quantification and equality, K, theorem-only
necessitation, 4, and the stipulated arbitrary-conjunction modal rule.
The use of 4 is explicit; the existing finitary C reconstruction derives it.

The endpoint proved here is the logical core: necessary exhaustion by an
arbitrary syntactic family gives the Barcan implication for every admitted
predicate. Infinitary Comprehension is not assumed as a disguised Barcan rule.
The separate passage from a model's current exhaustive family to necessary
exhaustion remains a comprehension/Barcan application.
-/

namespace Classicism.Research.InfinitaryComprehension.ConsequenceCalculus
open Classicism.Meta

universe u
variable {Param : Ty → Type u}

abbrev Sub (Γ Δ : Ctx) := ∀ {σ}, Var Γ σ → Term Param Δ σ

def wk {Γ σ τ} (a : Term Param Γ τ) : Term Param (σ :: Γ) τ :=
  a.rename (fun v => .succ v)

namespace Sub

def id (Γ : Ctx) : Sub (Param := Param) Γ Γ := fun v => .var v

def lift {Γ Δ σ} (s : Sub (Param := Param) Γ Δ) :
    Sub (Param := Param) (σ :: Γ) (σ :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => wk (s v)

theorem lift_id {Γ σ} :
    @Eq (Sub (Param := Param) (σ :: Γ) (σ :: Γ))
      (lift (id (Param := Param) Γ)) (id (σ :: Γ)) := by
  funext τ v
  cases v <;> rfl

def single {Γ σ} (a : Term Param Γ σ) : Sub (Param := Param) (σ :: Γ) Γ
  | _, .zero => a
  | _, .succ v => .var v

end Sub

def subst {Γ Δ τ} (s : Sub (Param := Param) Γ Δ) : Term Param Γ τ → Term Param Δ τ
  | .var v => s v
  | .param p => .param p
  | .app f a => .app (subst s f) (subst s a)
  | .top => .top
  | .bot => .bot
  | .neg p => .neg (subst s p)
  | .conj p q => .conj (subst s p) (subst s q)
  | .disj p q => .disj (subst s p) (subst s q)
  | .imp p q => .imp (subst s p) (subst s q)
  | .iff p q => .iff (subst s p) (subst s q)
  | .eq a b => .eq (subst s a) (subst s b)
  | .boxOp => .boxOp
  | .all p => .all (subst (Sub.lift s) p)
  | .ex p => .ex (subst (Sub.lift s) p)
  | .iAnd I p => .iAnd I (fun i => subst s (p i))
  | .iOr I p => .iOr I (fun i => subst s (p i))

def inst {Γ σ τ} (p : Term Param (σ :: Γ) τ) (a : Term Param Γ σ) : Term Param Γ τ :=
  subst (Sub.single a) p

/-- Syntactic renaming/substitution coherence, unrelated to object identity. -/
theorem subst_rename {Γ Δ Θ τ} (s : Sub (Param := Param) Δ Θ)
    (r : Ren Γ Δ) (p : Term Param Γ τ) :
    subst s (p.rename r) = subst (fun v => s (r v)) p := by
  induction p generalizing Δ Θ with
  | var v => rfl
  | param p => rfl
  | app f a ihf iha => simp only [Term.rename, subst, ihf, iha]
  | top => rfl
  | bot => rfl
  | neg p ih => simp only [Term.rename, subst, ih]
  | conj p q ihp ihq => simp only [Term.rename, subst, ihp, ihq]
  | disj p q ihp ihq => simp only [Term.rename, subst, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, subst, ihp, ihq]
  | iff p q ihp ihq => simp only [Term.rename, subst, ihp, ihq]
  | eq a b iha ihb => simp only [Term.rename, subst, iha, ihb]
  | boxOp => rfl
  | all p ih =>
      simp only [Term.rename, subst, ih]
      congr 2
      funext τ v
      cases v <;> rfl
  | ex p ih =>
      simp only [Term.rename, subst, ih]
      congr 2
      funext τ v
      cases v <;> rfl
  | iAnd I p ih => simp only [Term.rename, subst, ih]
  | iOr I p ih => simp only [Term.rename, subst, ih]

theorem subst_id {Γ τ} (p : Term Param Γ τ) :
    subst (Sub.id Γ) p = p := by
  induction p with
  | var v => rfl
  | param p => rfl
  | app f a ihf iha => simp only [subst, ihf, iha]
  | top => rfl
  | bot => rfl
  | neg p ih => simp only [subst, ih]
  | conj p q ihp ihq => simp only [subst, ihp, ihq]
  | disj p q ihp ihq => simp only [subst, ihp, ihq]
  | imp p q ihp ihq => simp only [subst, ihp, ihq]
  | iff p q ihp ihq => simp only [subst, ihp, ihq]
  | eq a b iha ihb => simp only [subst, iha, ihb]
  | boxOp => rfl
  | all p ih => simp only [subst, Sub.lift_id, ih]
  | ex p ih => simp only [subst, Sub.lift_id, ih]
  | iAnd I p ih => simp only [subst, ih]
  | iOr I p ih => simp only [subst, ih]

@[simp] theorem inst_wk {Γ σ τ} (p : Term Param Γ τ) (a : Term Param Γ σ) :
    inst (wk p) a = p := by
  rw [inst, wk, subst_rename]
  exact subst_id p

@[simp] theorem inst_var {Γ σ} (a : Term Param Γ σ) :
    inst (.var .zero) a = a := rfl

@[simp] theorem inst_app {Γ σ τ} {ρ : RTy}
    (f : Term Param (σ :: Γ) (τ ⇒ ρ)) (b : Term Param (σ :: Γ) τ)
    (a : Term Param Γ σ) :
    inst (.app f b) a = .app (inst f a) (inst b a) := rfl

@[simp] theorem inst_box {Γ σ} (p : Formula Param (σ :: Γ)) (a : Term Param Γ σ) :
    inst p.box a = (inst p a).box := rfl

/-- Instantiate a weakened binder by its fresh variable. This equation is
pure syntactic substitution, not an object beta or extensionality axiom. -/
theorem instantiate_at_fresh {Γ σ τ} (p : Term Param (σ :: Γ) τ) :
    inst (p.rename (Ren.lift (fun v => .succ v))) (.var .zero) = p := by
  rw [inst, subst_rename]
  have hs : @Eq (Sub (Param := Param) (σ :: Γ) (σ :: Γ))
      (fun {_} v => Sub.single (.var .zero : Term Param (σ :: Γ) σ)
        (Ren.lift (fun z => .succ z) v))
      (Sub.id (σ :: Γ)) := by
    funext τ v
    cases v <;> rfl
  rw [hs]
  exact subst_id p

/-- Inductive derivations; there is no constructor for Barcan or exhaustion. -/
inductive Derives : (Γ : Ctx) → List (Formula Param Γ) → Formula Param Γ → Prop
  | hyp {Γ Δ p} : p ∈ Δ → Derives Γ Δ p
  | weaken {Γ Δ Δ' p} : (∀ q, q ∈ Δ → q ∈ Δ') →
      Derives Γ Δ p → Derives Γ Δ' p
  | impI {Γ Δ p q} : Derives Γ (p :: Δ) q → Derives Γ Δ (.imp p q)
  | impE {Γ Δ p q} : Derives Γ Δ (.imp p q) → Derives Γ Δ p → Derives Γ Δ q
  | andI {Γ Δ p q} : Derives Γ Δ p → Derives Γ Δ q → Derives Γ Δ (.conj p q)
  | andE₁ {Γ Δ p q} : Derives Γ Δ (.conj p q) → Derives Γ Δ p
  | andE₂ {Γ Δ p q} : Derives Γ Δ (.conj p q) → Derives Γ Δ q
  | iAndI {Γ Δ} {I : Type u} {p : I → Formula Param Γ} :
      (∀ i, Derives Γ Δ (p i)) → Derives Γ Δ (.iAnd I p)
  | iAndE {Γ Δ} {I : Type u} {p : I → Formula Param Γ} :
      Derives Γ Δ (.iAnd I p) → (i : I) → Derives Γ Δ (p i)
  | iOrI {Γ Δ} {I : Type u} {p : I → Formula Param Γ} (i : I) :
      Derives Γ Δ (p i) → Derives Γ Δ (.iOr I p)
  | iOrE {Γ Δ q} {I : Type u} {p : I → Formula Param Γ} :
      Derives Γ Δ (.iOr I p) →
      (∀ i, Derives Γ (p i :: Δ) q) → Derives Γ Δ q
  | allI {Γ Δ σ} {p : Formula Param (σ :: Γ)} :
      Derives (σ :: Γ) (Δ.map (fun p => wk p)) p → Derives Γ Δ (.all p)
  | allE {Γ Δ σ} {p : Formula Param (σ :: Γ)} (a : Term Param Γ σ) :
      Derives Γ Δ (.all p) → Derives Γ Δ (inst p a)
  | eqSymm {Γ Δ σ} {a b : Term Param Γ σ} :
      Derives Γ Δ (.eq a b) → Derives Γ Δ (.eq b a)
  | eqApp {Γ Δ σ} {f : Term Param Γ (σ ⇒ RTy.t)} {a b : Term Param Γ σ} :
      Derives Γ Δ (.eq a b) → Derives Γ Δ (.eq (.app f a) (.app f b))
  | eqTruth {Γ Δ p q} : Derives Γ Δ (.eq p q) → Derives Γ Δ p → Derives Γ Δ q
  | nec {Γ p} : Derives Γ [] p → Derives Γ [] p.box
  | K {Γ Δ p q} : Derives Γ Δ (Term.box (.imp p q)) →
      Derives Γ Δ p.box → Derives Γ Δ q.box
  | four {Γ Δ} {p : Formula Param Γ} : Derives Γ Δ p.box → Derives Γ Δ p.box.box
  | box_iAnd {Γ Δ} {I : Type u} {p : I → Formula Param Γ} :
      Derives Γ Δ (.iAnd I (fun i => (p i).box)) →
      Derives Γ Δ (Term.box (.iAnd I p))

namespace Derives

theorem lift {Γ Δ p} (h : Derives (Param := Param) Γ [] p) : Derives Γ Δ p :=
  .weaken (fun _ h => False.elim (List.not_mem_nil h)) h

theorem hyp₀ {Γ Δ p} : Derives (Param := Param) Γ (p :: Δ) p :=
  .hyp (List.mem_cons_self ..)

theorem hyp₁ {Γ Δ p q} : Derives (Param := Param) Γ (p :: q :: Δ) q :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem allE_fresh {Γ : Ctx} {σ : Ty} {Δ : List (Formula Param (σ :: Γ))}
    {p : Formula Param (σ :: Γ)}
    (h : Derives (σ :: Γ) Δ (wk (.all p))) : Derives (σ :: Γ) Δ p := by
  have hh : Derives (σ :: Γ) Δ
      (inst (p.rename (Ren.lift (fun v => .succ v))) (.var .zero)) :=
    .allE (.var .zero) h
  rw [instantiate_at_fresh] at hh
  exact hh

/-- Infinitary modal consequence: collect all necessary instances before
using a necessarily available covering condition. All logical inputs are
unconditional derivations; no local hypothesis is necessitated. -/
theorem necessary_coverage {Γ} {I : Type u}
    (N P Q : Formula Param Γ) (f : I → Formula Param Γ)
    (cover : Derives Γ [] (.imp N (.imp (.iAnd I f) Q)))
    (instances : ∀ i, Derives Γ [] (.imp P (f i).box)) :
    Derives Γ [] (.imp N.box (.imp P Q.box)) := by
  apply Derives.impI
  apply Derives.impI
  have hf : Derives Γ [P, N.box] (Term.box (.iAnd I f)) :=
    .box_iAnd (.iAndI (fun i => .impE (instances i).lift .hyp₀))
  exact .K (.K (Derives.nec cover).lift .hyp₁) hf

/-- A closed implication from necessary N to B automatically persists under
necessary N, by theorem-only Nec, K and 4. -/
theorem necessary_condition_persistent {Γ} (N B : Formula Param Γ)
    (h : Derives Γ [] (.imp N.box B)) :
    Derives Γ [] (.imp N.box B.box) := by
  apply Derives.impI
  exact .K (Derives.nec h).lift (.four .hyp₀)

end Derives

/-- `∀x ⋁i x=a_i`, in the actual object syntax. -/
def namedExhaustion {Γ σ} {I : Type u} (a : I → Term Param Γ σ) : Formula Param Γ :=
  .all (.iOr I (fun i => .eq (.var .zero) (wk (a i))))

def forallPredicate {Γ σ} (F : Term Param Γ (σ ⇒ RTy.t)) : Formula Param Γ :=
  .all (.app (wk F) (.var .zero))

def forallBoxPredicate {Γ σ} (F : Term Param Γ (σ ⇒ RTy.t)) : Formula Param Γ :=
  .all (Term.box (.app (wk F) (.var .zero)))

/-- Every named instance follows from universal necessity by ordinary UI. -/
theorem named_box_instance {Γ σ} {I : Type u}
    (a : I → Term Param Γ σ) (F : Term Param Γ (σ ⇒ RTy.t)) (i : I) :
    Derives Γ [] (.imp (forallBoxPredicate F) (Term.box (.app F (a i)))) := by
  apply Derives.impI
  have h := Derives.allE (a i)
    (Derives.hyp₀ : Derives Γ [forallBoxPredicate F] (forallBoxPredicate F))
  change Derives Γ [forallBoxPredicate F]
    (Term.box (inst (.app (wk F) (.var .zero)) (a i))) at h
  rw [inst_app, inst_wk, inst_var] at h
  exact h

/-- The precise purely quantified covering formula. -/
def NamedCoverage {Γ σ} {I : Type u}
    (a : I → Term Param Γ σ) (F : Term Param Γ (σ ⇒ RTy.t)) : Prop :=
  Derives Γ [] (.imp (namedExhaustion a)
    (.imp (.iAnd I (fun i => .app F (a i))) (forallPredicate F)))

/-- Named exhaustion and every named F-instance imply universal F. The
proof uses actual eigenvariable generalization, infinitary case elimination,
and equality substitution; coverage is not assumed. -/
theorem named_coverage {Γ σ} {I : Type u}
    (a : I → Term Param Γ σ) (F : Term Param Γ (σ ⇒ RTy.t)) :
    NamedCoverage a F := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.allI
  have hx : Derives (σ :: Γ)
      [wk (.iAnd I (fun i => .app F (a i))), wk (namedExhaustion a)]
      (.iOr I (fun i => .eq (.var .zero) (wk (a i)))) :=
    Derives.allE_fresh Derives.hyp₁
  apply Derives.iOrE hx
  intro i
  have hFi : Derives (σ :: Γ)
      [.eq (.var .zero) (wk (a i)),
        wk (.iAnd I (fun i => .app F (a i))), wk (namedExhaustion a)]
      (.app (wk F) (wk (a i))) :=
    Derives.iAndE Derives.hyp₁ i
  exact Derives.eqTruth
    (Derives.eqApp (f := wk F) (Derives.eqSymm Derives.hyp₀)) hFi

/-- The full named-exhaustion implication for any current admitted predicate;
no covering proof, modal conclusion, or choice witness remains an input. -/
theorem necessary_named_exhaustion {Γ σ} {I : Type u}
    (a : I → Term Param Γ σ) (F : Term Param Γ (σ ⇒ RTy.t)) :
    Derives Γ [] (.imp (Term.box (namedExhaustion a))
      (.imp (forallBoxPredicate F) (Term.box (forallPredicate F)))) :=
  Derives.necessary_coverage (namedExhaustion a) (forallBoxPredicate F)
    (forallPredicate F) (fun i => .app F (a i))
    (named_coverage a F) (named_box_instance a F)

/-- The closed predicate quantifier of the actual Barcan formula. -/
def barcan (Γ : Ctx) (σ : Ty) : Formula Param Γ :=
  .all (σ := σ ⇒ RTy.t) (.imp (forallBoxPredicate (.var .zero))
    (Term.box (forallPredicate (.var .zero))))

/-- A parameter-only naming family is unchanged by eigenvariable renaming. -/
def parameterExhaustion (Γ : Ctx) {σ : Ty} {I : Type u}
    (a : I → Param σ) : Formula Param Γ :=
  namedExhaustion (fun i => .param (a i))

/-- Necessary exhaustion supplies the whole Barcan sentence, including its
quantifier over predicates, rather than only current named predicate cases. -/
theorem necessary_parameter_exhaustion_barcan {Γ σ} {I : Type u}
    (a : I → Param σ) :
    Derives Γ [] (.imp (Term.box (parameterExhaustion Γ a)) (barcan Γ σ)) := by
  apply Derives.impI
  apply Derives.allI
  exact Derives.impE
    (Derives.lift (necessary_named_exhaustion
      (Γ := (σ ⇒ RTy.t) :: Γ) (fun i => .param (a i)) (.var .zero)))
    Derives.hyp₀

/-- Named exhaustion entails necessary Barcan without necessitating that
local exhaustion assumption. This is the persistence step used in the
ordinary Infinitary Comprehension argument. -/
theorem necessary_parameter_exhaustion_necessary_barcan {Γ σ} {I : Type u}
    (a : I → Param σ) :
    Derives Γ [] (.imp (Term.box (parameterExhaustion Γ a))
      (Term.box (barcan Γ σ))) :=
  Derives.necessary_condition_persistent (parameterExhaustion Γ a) (barcan Γ σ)
    (necessary_parameter_exhaustion_barcan a)

#print axioms named_coverage
#print axioms Derives.necessary_coverage
#print axioms Derives.necessary_condition_persistent
#print axioms necessary_named_exhaustion
#print axioms necessary_parameter_exhaustion_necessary_barcan

end Classicism.Research.InfinitaryComprehension.ConsequenceCalculus
