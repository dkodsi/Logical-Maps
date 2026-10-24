import Classicism.Results.Research.ModalFiniteDerivationSupport

/-!
# Independent closed representation definitions

The new names have relational output; each is specified by an old-language,
closed finite strong-comprehension body. Neither bodies nor old signatures
are assumed finite. An individual defining instance has singleton NEW-name
support, and the actual proof induction consequently restricts every proof.
-/

namespace Classicism.Research.ModalFiniteNameSupport
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Research.ModalFreshConstantSyntax
open Classicism.Research.ModalComprehensionRepresentation (diagram)

variable {C : Ty → Type} {Names : RTy → Type}

abbrev Definitions (C : Ty → Type) (Names : RTy → Type) :=
  ∀ {ρ : RTy}, Names ρ → Body C [] ρ

def nameDefinition (body : Definitions C Names) {ρ : RTy} (n : Names ρ) :
    Formula (NamedConst C Names) [] :=
  Term.box (diagram (mapBody NamedConst.old (body n)) (.const (.name n)))

inductive NamedAxioms (body : Definitions C Names) : Axioms (NamedConst C Names)
  | classical {Γ p} : ClassicalAxioms (NamedConst C Names) Γ p → NamedAxioms body Γ p
  | definition {Γ} {ρ : RTy} (n : Names ρ) :
      NamedAxioms body Γ (closedAt (nameDefinition body n) Γ)

def scopedDefinitions (body : Definitions C Names) (S : List (Label Names)) :
    Definitions C (ScopedNames Names S) := fun n => body n.val

def scopedNamedAxioms (body : Definitions C Names) : ScopedAxioms C Names :=
  fun S => NamedAxioms (scopedDefinitions body S)

theorem include_nameDefinition (body : Definitions C Names)
    (S : List (Label Names)) {ρ : RTy} (n : Names ρ)
    (hn : (⟨ρ, n⟩ : Label Names) ∈ S) :
    mapTerm (includeConst S) (nameDefinition (scopedDefinitions body S) ⟨n, hn⟩) =
      nameDefinition body n := by
  change Term.box (mapTerm (includeConst S)
      (diagram (mapBody NamedConst.old (body n)) (.const (.name ⟨n, hn⟩)))) = _
  rw [mapTerm_diagram, mapBody_comp]
  rfl

/-- Classical instances and independent defining instances both have
explicit finite support; no global proof-preservation premise is assumed. -/
theorem named_axiom_eventually (body : Definitions C Names) {Γ p}
    (h : NamedAxioms body Γ p) :
    Eventually (fun S => ∃ q : Formula (ScopedConst C Names S) Γ,
      mapTerm (includeConst S) q = p ∧
      Derives (ScopedConst C Names S) (scopedNamedAxioms body S) Γ [] q) := by
  cases h with
  | classical hc =>
      cases hc with
      | dne p =>
          apply eventually_mono (term_eventually p)
          rintro S ⟨p₀, hp₀⟩
          refine ⟨.imp (neg (neg p₀)) p₀, ?_, .ax (.classical (.dne p₀))⟩
          simp only [neg, bottom, mapTerm, hp₀]
      | exists_e =>
          apply eventually_of_forall
          intro S
          exact ⟨.ex (.eq (.var (.zero : Var (Ty.e :: Γ) Ty.e)) (.var .zero)),
            rfl, .ax (.classical .exists_e)⟩
  | @definition Γ ρ n =>
      refine ⟨[⟨ρ, n⟩], ?_⟩
      intro S hS
      have hn : (⟨ρ, n⟩ : Label Names) ∈ S := hS _ (List.mem_cons_self ..)
      refine ⟨closedAt (nameDefinition (scopedDefinitions body S) ⟨n, hn⟩) Γ,
        ?_, .ax (NamedAxioms.definition (body := scopedDefinitions body S)
          (Γ := Γ) (⟨n, hn⟩ : ScopedNames Names S ρ))⟩
      rw [mapTerm_closedAt, include_nameDefinition]

/-- A proof with arbitrarily many available independent names uses only a
finite subfamily. The returned proof is in the ACTUAL concrete calculus. -/
theorem named_finite_derivation_support (body : Definitions C Names) {Γ Δ p}
    (proof : Derives (NamedConst C Names) (NamedAxioms body) Γ Δ p) :
    ∃ (S : List (Label Names)) (Δ' : List (Formula (ScopedConst C Names S) Γ))
      (p' : Formula (ScopedConst C Names S) Γ),
      Δ'.map (mapTerm (includeConst S)) = Δ ∧ mapTerm (includeConst S) p' = p ∧
      Derives (ScopedConst C Names S) (NamedAxioms (scopedDefinitions body S)) Γ Δ' p' :=
  finite_derivation_support (named_axiom_eventually body) proof

/-- When the conclusion and local premises are old-language formulas,
restriction preserves those boundary formulas literally. -/
theorem named_finite_old_support (body : Definitions C Names)
    {Γ : Ctx} {Δ : List (Formula C Γ)} {p : Formula C Γ}
    (proof : Derives (NamedConst C Names) (NamedAxioms body) Γ
      (Δ.map (mapTerm NamedConst.old)) (mapTerm NamedConst.old p)) :
    ∃ S, Derives (ScopedConst C Names S) (NamedAxioms (scopedDefinitions body S)) Γ
      (Δ.map (mapTerm NamedConst.old)) (mapTerm NamedConst.old p) := by
  rcases derivation_eventually (named_axiom_eventually body) proof with ⟨S, hS⟩
  refine ⟨S, hS S (fun _ h => h) _ _ ?_ ?_⟩
  · simp only [List.map_map, Function.comp_def, mapTerm_comp]
    rfl
  · rw [mapTerm_comp]
    rfl

#print axioms named_axiom_eventually
#print axioms named_finite_derivation_support
#print axioms named_finite_old_support

end Classicism.Research.ModalFiniteNameSupport
