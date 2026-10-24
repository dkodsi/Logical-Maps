import Classicism.Results.Research.ModalComprehensionConcreteBodies

/-!
# Concrete lambda-free derivations for modal comprehension

Original research, misc, 23 October 2026. This is an independently defined
object proof relation, not C.Derivable and not an interpretation in Lean Prop.
Its quantified rules use actual de Bruijn eigenvariable contexts. Modal K,
theorem-only Nec, all-type Intensionality, and finite-body strong SC are
explicit rules/axioms of the stipulated base. NI/T/4/uniqueness/beta/eta are
not constructors; they are inherited from the representation proofs.

`Ax` denotes additional GLOBAL axioms eligible for necessitation, not local
optional premises. Local premises occupy the separate list Δ. The empty Ax
instance is the unextended base used for the principal declarations below.

This is the positive logical/equality/quantifier fragment used by the
reconstruction proof. A full syntax translation of all classical C rules
and connection to conservative named signature extensions remain separate.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open ModalComprehensionRepresentation

abbrev Formula (Const : Ty → Type) (Γ : Ctx) := Term Const Γ Ty.t
abbrev Axioms (Const : Ty → Type) := ∀ Γ, Formula Const Γ → Prop

inductive Derives (Const : Ty → Type) (Ax : Axioms Const) :
    (Γ : Ctx) → List (Formula Const Γ) → Formula Const Γ → Prop
  | hyp {Γ Δ p} : p ∈ Δ → Derives Const Ax Γ Δ p
  | ax {Γ Δ p} : Ax Γ p → Derives Const Ax Γ Δ p
  | weaken {Γ Δ Δ' p} : (∀ q, q ∈ Δ → q ∈ Δ') →
      Derives Const Ax Γ Δ p → Derives Const Ax Γ Δ' p
  | impI {Γ Δ p q} : Derives Const Ax Γ (p :: Δ) q →
      Derives Const Ax Γ Δ (.imp p q)
  | impE {Γ Δ p q} : Derives Const Ax Γ Δ (.imp p q) →
      Derives Const Ax Γ Δ p → Derives Const Ax Γ Δ q
  | iffI {Γ Δ p q} : Derives Const Ax Γ Δ (.imp p q) →
      Derives Const Ax Γ Δ (.imp q p) → Derives Const Ax Γ Δ (.iff p q)
  | iffE₁ {Γ Δ p q} : Derives Const Ax Γ Δ (.iff p q) →
      Derives Const Ax Γ Δ p → Derives Const Ax Γ Δ q
  | iffE₂ {Γ Δ p q} : Derives Const Ax Γ Δ (.iff p q) →
      Derives Const Ax Γ Δ q → Derives Const Ax Γ Δ p
  | topI {Γ Δ} : Derives Const Ax Γ Δ .top
  | eqRefl {Γ Δ σ} (a : Term Const Γ σ) : Derives Const Ax Γ Δ (.eq a a)
  | eqSymm {Γ Δ σ} {a b : Term Const Γ σ} :
      Derives Const Ax Γ Δ (.eq a b) → Derives Const Ax Γ Δ (.eq b a)
  | eqTrans {Γ Δ σ} {a b c : Term Const Γ σ} :
      Derives Const Ax Γ Δ (.eq a b) → Derives Const Ax Γ Δ (.eq b c) →
      Derives Const Ax Γ Δ (.eq a c)
  | eqApp {Γ Δ σ} {ρ : RTy} {f g : Term Const Γ (σ ⇒ ρ)} {a b : Term Const Γ σ} :
      Derives Const Ax Γ Δ (.eq f g) → Derives Const Ax Γ Δ (.eq a b) →
      Derives Const Ax Γ Δ (.eq (.app f a) (.app g b))
  | eqRight {Γ Δ σ} (a : Term Const Γ σ) {b c : Term Const Γ σ} :
      Derives Const Ax Γ Δ (.eq b c) →
      Derives Const Ax Γ Δ (.eq (.eq a b) (.eq a c))
  | eqTruth {Γ Δ p q} : Derives Const Ax Γ Δ (.eq p q) →
      Derives Const Ax Γ Δ p → Derives Const Ax Γ Δ q
  | eqSubst {Γ Δ σ} (P : Formula Const (σ :: Γ)) (a b : Term Const Γ σ) :
      Derives Const Ax Γ Δ (.eq a b) → Derives Const Ax Γ Δ (P.inst a) →
      Derives Const Ax Γ Δ (P.inst b)
  | allI {Γ Δ σ} {P : Formula Const (σ :: Γ)} :
      Derives Const Ax (σ :: Γ) (Δ.map (fun p => p.wk)) P →
      Derives Const Ax Γ Δ (.all P)
  | allE {Γ Δ σ} {P : Formula Const (σ :: Γ)} (a : Term Const Γ σ) :
      Derives Const Ax Γ Δ (.all P) → Derives Const Ax Γ Δ (P.inst a)
  | exI {Γ Δ σ} {P : Formula Const (σ :: Γ)} (a : Term Const Γ σ) :
      Derives Const Ax Γ Δ (P.inst a) → Derives Const Ax Γ Δ (.ex P)
  | exE {Γ Δ σ} {P : Formula Const (σ :: Γ)} {q : Formula Const Γ} :
      Derives Const Ax Γ Δ (.ex P) →
      Derives Const Ax (σ :: Γ) (P :: Δ.map (fun p => p.wk)) q.wk →
      Derives Const Ax Γ Δ q
  | nec {Γ p} : Derives Const Ax Γ [] p → Derives Const Ax Γ [] p.box
  | K {Γ Δ p q} : Derives Const Ax Γ Δ (Term.box (.imp p q)) →
      Derives Const Ax Γ Δ p.box → Derives Const Ax Γ Δ q.box
  | intensionality {Γ Δ} (ρ : RTy) (a b : Term Const Γ ρ) :
      Derives Const Ax Γ Δ (Term.box (Term.coext ρ a b)) →
      Derives Const Ax Γ Δ (.eq a b)
  /-- Strong comprehension over one finite syntactic binder spine. -/
  | comprehension {Γ Δ} {ρ : RTy} (A : Body Const Γ ρ) :
      Derives Const Ax Γ Δ (.ex (Body.code A))

namespace Derives
variable {Const : Ty → Type} {Ax : Axioms Const}

theorem lift {Γ Δ p} (h : Derives Const Ax Γ [] p) : Derives Const Ax Γ Δ p :=
  .weaken (fun _ h => False.elim (List.not_mem_nil h)) h

theorem hyp₀ {Γ Δ p} : Derives Const Ax Γ (p :: Δ) p := .hyp (List.mem_cons_self ..)
theorem hyp₁ {Γ Δ p q} : Derives Const Ax Γ (p :: q :: Δ) q :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- Necessary universal instantiation follows from ordinary theorem UI,
Nec and K. The supplied boxed premise stays local. -/
theorem boxed_allE {Γ Δ σ}
    {P : Formula Const (σ :: Γ)} (a : Term Const Γ σ)
    (h : Derives Const Ax Γ Δ (Term.box (.all P))) :
    Derives Const Ax Γ Δ (Term.box (P.inst a)) := by
  have ui : Derives Const Ax Γ [] (.imp (.all P) (P.inst a)) :=
    .impI (.allE a .hyp₀)
  exact .K (.lift (.nec ui)) h

/-- Rename the old binder past a fresh variable and instantiate it by that
fresh variable. This is substitution of syntax trees, not object beta. -/
theorem instantiate_at_fresh {Γ σ τ} (P : Term Const (σ :: Γ) τ) :
    (P.rename (Ren.lift (Ren.shift (σ := σ)))).inst (.var .zero) = P := by
  rw [Term.inst, Term.subst_rename]
  have hs : @Eq (Sub Const (σ :: Γ) (σ :: Γ))
      (fun {τ} (v : Var (σ :: Γ) τ) =>
        Sub.cons (.var (.zero : Var (σ :: Γ) σ)) Sub.id (Ren.lift Ren.shift v)) Sub.id := by
    funext τ v
    cases v <;> rfl
  rw [hs, Term.subst_id]

/-- The interface's binary universal lifting rule, proved using the actual
eigenvariable Gen and UI constructors. It is not an axiom of this calculus. -/
theorem allLift₂ {Γ σ} {A B C : Formula Const (σ :: Γ)}
    (h : Derives Const Ax (σ :: Γ) [] (.imp A (.imp B C))) :
    Derives Const Ax Γ [] (.imp (.all A) (.imp (.all B) (.all C))) := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.allI
  have ha : Derives Const Ax (σ :: Γ) [(Term.all B).wk, (Term.all A).wk] A := by
    have hu : Derives Const Ax (σ :: Γ) [(Term.all B).wk, (Term.all A).wk]
        ((A.rename (Ren.lift (Ren.shift (σ := σ)))).inst (.var .zero)) :=
      Derives.allE (.var .zero)
      (Derives.hyp₁ : Derives Const Ax (σ :: Γ)
        [(Term.all B).wk, (Term.all A).wk] (Term.all A).wk)
    rw [instantiate_at_fresh] at hu
    exact hu
  have hb : Derives Const Ax (σ :: Γ) [(Term.all B).wk, (Term.all A).wk] B := by
    have hu : Derives Const Ax (σ :: Γ) [(Term.all B).wk, (Term.all A).wk]
        ((B.rename (Ren.lift (Ren.shift (σ := σ)))).inst (.var .zero)) :=
      Derives.allE (.var .zero)
      (Derives.hyp₀ : Derives Const Ax (σ :: Γ)
        [(Term.all B).wk, (Term.all A).wk] (Term.all B).wk)
    rw [instantiate_at_fresh] at hu
    exact hu
  exact .impE (.impE h.lift ha) hb

end Derives

/-- Every abstract proof-rule field has now been supplied by an independently
defined lambda-free derivation constructor or an actual derivation. -/
def calculus (Const : Ty → Type) (Ax : Axioms Const) : Calculus (language Const) where
  Derives := Derives Const Ax
  hyp := Derives.hyp
  weaken := Derives.weaken
  impI := Derives.impI
  impE := Derives.impE
  iffI := Derives.iffI
  iffE₁ := Derives.iffE₁
  iffE₂ := Derives.iffE₂
  topI := Derives.topI
  eqRefl := Derives.eqRefl
  eqSymm := Derives.eqSymm
  eqTrans := Derives.eqTrans
  eqApp := Derives.eqApp
  eqRight := Derives.eqRight
  eqTruth := Derives.eqTruth
  eqSubst := Derives.eqSubst
  allI h := Derives.allI (Δ := []) h
  allE P a := .impI (.allE a .hyp₀)
  allLift₂ := Derives.allLift₂
  nec := Derives.nec
  K := Derives.K
  intensionality := Derives.intensionality
  comprehension M := by
    have h := Derives.comprehension (Ax := Ax) (Δ := []) (.bind (Body.ofTerm _ M))
    change Derives Const Ax _ [] (Term.ex (Term.representativeBody M))
    rw [Body.code_bind_ofTerm (Const := Const) M] at h
    exact h

def uniformComprehension (Const : Ty → Type) (Ax : Axioms Const) :
    UniformComprehension (language Const) (calculus Const Ax) where
  bodyCode := Body.code
  bodyCode_inst := Body.code_inst
  comprehend A := Derives.comprehension (Δ := []) A

def noAdditionalAxioms (Const : Ty → Type) : Axioms Const := fun _ _ => False

/-- Concrete theorem: no interface rules or syntax equations remain as
hypotheses. The object calculus's stipulated K/Nec/I/SC rules remain visible. -/
theorem concrete_closed_representation (Const : Ty → Type) {ρ : RTy}
    (A : Body Const [] ρ) :
    Derives Const (noAdditionalAxioms Const) [] [] (.ex (Body.code A)) ∧
      (∀ H : Term Const [] ρ,
        Derives Const (noAdditionalAxioms Const) [] []
          (.imp (UniformRepresents A H) (Term.box (UniformRepresents A H)))) ∧
      (∀ H J : Term Const [] ρ,
        Derives Const (noAdditionalAxioms Const) [] []
          (.imp (UniformRepresents A H) (.imp (UniformRepresents A J) (.eq H J)))) :=
  (calculus Const (noAdditionalAxioms Const)).closed_uniform_representation
    (uniformComprehension Const (noAdditionalAxioms Const)) A

theorem concrete_beta {Const : Ty → Type} {Γ Δ σ} {ρ : RTy}
    (M : Term Const (σ :: Γ) ρ) (H : Term Const Γ (σ ⇒ ρ)) (a : Term Const Γ σ)
    (h : Derives Const (noAdditionalAxioms Const) Γ Δ
      (Represents (L := language Const) H M)) :
    Derives Const (noAdditionalAxioms Const) Γ Δ (.eq (.app H a) (M.inst a)) :=
  (calculus Const (noAdditionalAxioms Const)).representative_beta M H a h

theorem concrete_eta {Const : Ty → Type} {Γ Δ σ} {ρ : RTy}
    (H F : Term Const Γ (σ ⇒ ρ))
    (h : Derives Const (noAdditionalAxioms Const) Γ Δ
      (Represents (L := language Const) H (.app F.wk (.var .zero)))) :
    Derives Const (noAdditionalAxioms Const) Γ Δ (.eq H F) :=
  (calculus Const (noAdditionalAxioms Const)).representative_eta H F h

#print axioms calculus
#print axioms uniformComprehension
#print axioms concrete_closed_representation
#print axioms concrete_beta
#print axioms concrete_eta

end Classicism.Research.ModalComprehensionConcreteSyntax
