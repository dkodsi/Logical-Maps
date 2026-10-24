import Classicism.Results.Research.ModalClassicalSequentClosure

/-!
# Finite support of newly introduced relational constants

Original research, misc, 23 October 2026. Source: finite-name-erasure-proof.txt,
sections 3–5. Old signatures are unrestricted. Only NEW relational names are
collected. Restriction takes a proof that every occurring new name is listed;
it never supplies a default denotation for an unused name.
-/

namespace Classicism.Research.ModalFiniteNameSupport
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Research.ModalFreshConstantSyntax
open Classicism.Research.ModalComprehensionRepresentation (AdmittedBody diagram UniformRepresents)

variable {C D E : Ty → Type} {Names : RTy → Type}

inductive NamedConst (C : Ty → Type) (Names : RTy → Type) : Ty → Type
  | old {σ} : C σ → NamedConst C Names σ
  | name {ρ : RTy} : Names ρ → NamedConst C Names ρ

abbrev Label (Names : RTy → Type) := Sigma Names
abbrev ScopedNames (Names : RTy → Type) (S : List (Label Names)) (ρ : RTy) :=
  {n : Names ρ // (⟨ρ, n⟩ : Label Names) ∈ S}
abbrev ScopedConst (C : Ty → Type) (Names : RTy → Type) (S : List (Label Names)) :=
  NamedConst C (ScopedNames Names S)
abbrev ConstMap (C D : Ty → Type) := ∀ {σ}, C σ → D σ

def mapTerm (f : ConstMap C D) : Term C Γ σ → Term D Γ σ
  | .var v => .var v
  | .const c => .const (f c)
  | .app g a => .app (mapTerm f g) (mapTerm f a)
  | .top => .top
  | .imp p q => .imp (mapTerm f p) (mapTerm f q)
  | .iff p q => .iff (mapTerm f p) (mapTerm f q)
  | .eq a b => .eq (mapTerm f a) (mapTerm f b)
  | .boxOp => .boxOp
  | .all p => .all (mapTerm f p)
  | .ex p => .ex (mapTerm f p)

theorem mapTerm_id (t : Term C Γ σ) : mapTerm (fun c => c) t = t := by
  induction t <;> simp_all only [mapTerm]

theorem mapTerm_comp (f : ConstMap C D) (g : ConstMap D E) (t : Term C Γ σ) :
    mapTerm g (mapTerm f t) = mapTerm (fun c => g (f c)) t := by
  induction t <;> simp_all only [mapTerm]

theorem mapTerm_rename (f : ConstMap C D) (r : Ren Γ Θ) (t : Term C Γ σ) :
    mapTerm f (t.rename r) = (mapTerm f t).rename r := by
  induction t generalizing Θ <;> simp_all only [mapTerm, Term.rename]

theorem mapTerm_wk (f : ConstMap C D) (t : Term C Γ σ) :
    mapTerm f (t.wk (σ := τ)) = (mapTerm f t).wk :=
  mapTerm_rename f Ren.shift t

theorem mapTerm_subst (f : ConstMap C D) (s : Sub C Γ Θ) (t : Term C Γ σ) :
    mapTerm f (t.subst s) = (mapTerm f t).subst (fun v => mapTerm f (s v)) := by
  have hl {Γ Θ υ} (s : Sub C Γ Θ) :
      @Eq (Sub D (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => mapTerm f (Sub.lift s v))
        (Sub.lift (fun v => mapTerm f (s v))) := by
    funext τ v
    cases v with
    | zero => rfl
    | succ v => exact mapTerm_wk f (s v)
  induction t generalizing Θ <;> simp_all only [mapTerm, Term.subst, hl]

theorem mapTerm_inst (f : ConstMap C D) (P : Term C (σ :: Γ) τ)
    (a : Term C Γ σ) :
    mapTerm f (P.inst a) = (mapTerm f P).inst (mapTerm f a) := by
  rw [Term.inst, mapTerm_subst]
  have hs : @Eq (Sub D (σ :: Γ) Γ)
      (fun {υ} (v : Var (σ :: Γ) υ) => mapTerm f (Sub.cons a Sub.id v))
      (Sub.cons (mapTerm f a) Sub.id) := by
    funext υ v
    cases v <;> rfl
  rw [hs]
  rfl

theorem mapTerm_coext (f : ConstMap C D) (ρ : RTy) :
    ∀ {Γ} (a b : Term C Γ ρ),
      mapTerm f (Term.coext ρ a b) = Term.coext ρ (mapTerm f a) (mapTerm f b) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [Term.coext, mapTerm, ih, mapTerm_wk]

def mapBody (f : ConstMap C D) : Body C Γ ρ → Body D Γ ρ
  | .atom p => .atom (mapTerm f p)
  | .bind A => .bind (mapBody f A)

theorem mapBody_id (A : Body C Γ ρ) : mapBody (fun c => c) A = A := by
  induction A with
  | atom p => exact congrArg (AdmittedBody.atom (L := language C)) (mapTerm_id p)
  | bind A ih => exact congrArg AdmittedBody.bind ih

theorem mapBody_comp (f : ConstMap C D) (g : ConstMap D E) (A : Body C Γ ρ) :
    mapBody g (mapBody f A) = mapBody (fun c => g (f c)) A := by
  induction A with
  | atom p => exact congrArg (AdmittedBody.atom (L := language E)) (mapTerm_comp f g p)
  | bind A ih => exact congrArg AdmittedBody.bind ih

theorem mapBody_rename (f : ConstMap C D) (r : Ren Γ Θ) (A : Body C Γ ρ) :
    mapBody f (A.rename r) = (mapBody f A).rename r := by
  induction A generalizing Θ with
  | atom p => exact congrArg (AdmittedBody.atom (L := language D)) (mapTerm_rename f r p)
  | bind A ih =>
      change AdmittedBody.bind (mapBody f (Body.rename (Ren.lift r) A)) =
        AdmittedBody.bind (Body.rename (Ren.lift r) (mapBody f A))
      rw [ih]

theorem mapTerm_diagram (f : ConstMap C D) (A : Body C Γ ρ) (H : Term C Γ ρ) :
    mapTerm f (diagram A H) = diagram (mapBody f A) (mapTerm f H) := by
  induction A with
  | atom p => rfl
  | bind A ih =>
      change Term.all (mapTerm f (diagram A (.app H.wk (.var .zero)))) =
        Term.all (diagram (mapBody f A) (.app (mapTerm f H).wk (.var .zero)))
      rw [ih]
      simp only [mapTerm, mapTerm_wk]

theorem mapTerm_body_code (f : ConstMap C D) (A : Body C Γ ρ) :
    mapTerm f (Body.code A) = Body.code (mapBody f A) := by
  simp only [Body.code, Term.box, mapTerm, mapTerm_diagram, mapBody_rename]

theorem mapTerm_closedAt (f : ConstMap C D) (p : Formula C []) (Γ : Ctx) :
    mapTerm f (closedAt p Γ) = closedAt (mapTerm f p) Γ :=
  mapTerm_rename f (emptyRen Γ) p

def includeConst (S : List (Label Names)) : ConstMap (ScopedConst C Names S) (NamedConst C Names)
  | _, .old c => .old c
  | _, .name n => .name n.val

def names : Term (NamedConst C Names) Γ σ → List (Label Names)
  | .var _ => []
  | .const (.old _) => []
  | .const (.name (ρ := ρ) n) => [⟨ρ, n⟩]
  | .app f a => names f ++ names a
  | .top => []
  | .imp p q => names p ++ names q
  | .iff p q => names p ++ names q
  | .eq a b => names a ++ names b
  | .boxOp => []
  | .all p => names p
  | .ex p => names p

abbrev Subset (S T : List (Label Names)) := ∀ n, n ∈ S → n ∈ T

theorem subset_left {S T U : List (Label Names)} (h : Subset (S ++ T) U) :
    Subset S U := fun n hn => h n (List.mem_append.mpr (.inl hn))
theorem subset_right {S T U : List (Label Names)} (h : Subset (S ++ T) U) :
    Subset T U := fun n hn => h n (List.mem_append.mpr (.inr hn))

/-- Only occurring names are evaluated by this partial-signature operation. -/
def restrict (S : List (Label Names)) : (t : Term (NamedConst C Names) Γ σ) →
    Subset (names t) S → Term (ScopedConst C Names S) Γ σ
  | .var v, _ => .var v
  | .const (.old c), _ => .const (.old c)
  | .const (.name n), h => .const (.name ⟨n, h _ (List.mem_cons_self ..)⟩)
  | .app f a, h => .app (restrict S f (subset_left h)) (restrict S a (subset_right h))
  | .top, _ => .top
  | .imp p q, h => .imp (restrict S p (subset_left h)) (restrict S q (subset_right h))
  | .iff p q, h => .iff (restrict S p (subset_left h)) (restrict S q (subset_right h))
  | .eq a b, h => .eq (restrict S a (subset_left h)) (restrict S b (subset_right h))
  | .boxOp, _ => .boxOp
  | .all p, h => .all (restrict S p h)
  | .ex p, h => .ex (restrict S p h)

theorem include_restrict (S : List (Label Names)) (t : Term (NamedConst C Names) Γ σ)
    (h : Subset (names t) S) : mapTerm (includeConst S) (restrict S t h) = t := by
  induction t with
  | var v => rfl
  | const c => cases c <;> rfl
  | app f a ihf iha => simp only [restrict, mapTerm, ihf, iha]
  | top => rfl
  | imp p q ihp ihq => simp only [restrict, mapTerm, ihp, ihq]
  | iff p q ihp ihq => simp only [restrict, mapTerm, ihp, ihq]
  | eq a b iha ihb => simp only [restrict, mapTerm, iha, ihb]
  | boxOp => rfl
  | all p ih => exact congrArg Term.all (ih h)
  | ex p ih => exact congrArg Term.ex (ih h)

/-- A partial inverse is used ONLY to prove inclusion injective. A name
outside S yields none, never a fabricated term or denotation. -/
noncomputable def recoverConst (S : List (Label Names)) :
    ∀ {σ}, NamedConst C Names σ → Option (ScopedConst C Names S σ) := by
  classical
  intro σ c
  cases c with
  | old c => exact some (.old c)
  | @name ρ n => exact if h : (⟨ρ, n⟩ : Label Names) ∈ S then some (.name ⟨n, h⟩) else none

def partialTerm (f : ∀ {σ}, C σ → Option (D σ)) : Term C Γ σ → Option (Term D Γ σ)
  | .var v => some (.var v)
  | .const c => (f c).map Term.const
  | .app g a => do return .app (← partialTerm f g) (← partialTerm f a)
  | .top => some .top
  | .imp p q => do return .imp (← partialTerm f p) (← partialTerm f q)
  | .iff p q => do return .iff (← partialTerm f p) (← partialTerm f q)
  | .eq a b => do return .eq (← partialTerm f a) (← partialTerm f b)
  | .boxOp => some .boxOp
  | .all p => (partialTerm f p).map Term.all
  | .ex p => (partialTerm f p).map Term.ex

theorem partialTerm_mapTerm (f : ConstMap C D) (g : ∀ {σ}, D σ → Option (C σ))
    (h : ∀ {σ} (c : C σ), g (f c) = some c) (t : Term C Γ σ) :
    partialTerm g (mapTerm f t) = some t := by
  induction t <;> simp_all [partialTerm, mapTerm]

theorem recover_include (S : List (Label Names)) {σ} (c : ScopedConst C Names S σ) :
    recoverConst S (includeConst S c) = some c := by
  classical
  cases c with
  | old c => rfl
  | name n => simp [includeConst, recoverConst, n.property]

theorem include_injective (S : List (Label Names)) {Γ σ} :
    Function.Injective (mapTerm (includeConst (C := C) S) :
      Term (ScopedConst C Names S) Γ σ → Term (NamedConst C Names) Γ σ) := by
  intro a b h
  have hp := congrArg (partialTerm (recoverConst S)) h
  simpa only [partialTerm_mapTerm _ _ (recover_include S), Option.some.injEq] using hp

def bodyNames : Body (NamedConst C Names) Γ ρ → List (Label Names)
  | .atom p => names p
  | .bind A => bodyNames A

def restrictBody (S : List (Label Names)) : (A : Body (NamedConst C Names) Γ ρ) →
    Subset (bodyNames A) S → Body (ScopedConst C Names S) Γ ρ
  | .atom p, h => .atom (restrict S p h)
  | .bind A, h => .bind (restrictBody S A h)

theorem include_restrictBody (S : List (Label Names))
    (A : Body (NamedConst C Names) Γ ρ) (h : Subset (bodyNames A) S) :
    mapBody (includeConst S) (restrictBody S A h) = A := by
  induction A with
  | atom p =>
      exact congrArg (AdmittedBody.atom (L := language (NamedConst C Names)))
        (include_restrict S p h)
  | bind A ih => exact congrArg AdmittedBody.bind (ih h)

/-- A finite list is the witness; all later supersets preserve availability. -/
def Eventually (P : List (Label Names) → Prop) : Prop :=
  ∃ S, ∀ T, Subset S T → P T

theorem eventually_of_forall {P : List (Label Names) → Prop} (h : ∀ S, P S) : Eventually P :=
  ⟨[], fun S _ => h S⟩

theorem eventually_mono {P Q : List (Label Names) → Prop}
    (h : Eventually P) (f : ∀ S, P S → Q S) : Eventually Q := by
  rcases h with ⟨S, hS⟩
  exact ⟨S, fun T hT => f T (hS T hT)⟩

theorem eventually_and {P Q : List (Label Names) → Prop}
    (hP : Eventually P) (hQ : Eventually Q) : Eventually (fun S => P S ∧ Q S) := by
  rcases hP with ⟨S, hS⟩
  rcases hQ with ⟨T, hT⟩
  exact ⟨S ++ T, fun U hU => ⟨hS U (subset_left hU), hT U (subset_right hU)⟩⟩

def TermLift (S : List (Label Names)) (t : Term (NamedConst C Names) Γ σ) : Prop :=
  ∃ u : Term (ScopedConst C Names S) Γ σ, mapTerm (includeConst S) u = t

theorem term_eventually (t : Term (NamedConst C Names) Γ σ) :
    Eventually (fun S => TermLift S t) :=
  ⟨names t, fun S h => ⟨restrict S t h, include_restrict S t h⟩⟩

theorem body_eventually (A : Body (NamedConst C Names) Γ ρ) :
    Eventually (fun S => ∃ B : Body (ScopedConst C Names S) Γ ρ,
      mapBody (includeConst S) B = A) :=
  ⟨bodyNames A, fun S h => ⟨restrictBody S A h, include_restrictBody S A h⟩⟩

theorem list_eventually (Δ : List (Formula (NamedConst C Names) Γ)) :
    Eventually (fun S => ∃ Θ : List (Formula (ScopedConst C Names S) Γ),
      Θ.map (mapTerm (includeConst S)) = Δ) := by
  induction Δ with
  | nil => exact eventually_of_forall (fun _ => ⟨[], rfl⟩)
  | cons p Δ ih =>
      apply eventually_mono (eventually_and (term_eventually p) ih)
      rintro S ⟨⟨q, hq⟩, ⟨Θ, hΘ⟩⟩
      exact ⟨q :: Θ, by simp only [List.map_cons, hq, hΘ]⟩

#print axioms include_restrict
#print axioms include_injective
#print axioms term_eventually
#print axioms body_eventually

end Classicism.Research.ModalFiniteNameSupport
