import Classicism.Results.Research.ModalFiniteNameSupport

/-!
# Restricting an actual finite derivation to finitely many new names

Original research, misc, 23 October 2026. Each inference constructor is
handled below. The axiom hypothesis concerns individual global instances
only; the subsequent named-definition instance discharges that hypothesis.
Intermediate formulas, witnesses and comprehension bodies are included.
-/

namespace Classicism.Research.ModalFiniteNameSupport
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Research.ModalFreshConstantSyntax
open Classicism.Research.ModalComprehensionRepresentation (diagram)

variable {C : Ty → Type} {Names : RTy → Type}

abbrev ScopedAxioms (C : Ty → Type) (Names : RTy → Type) :=
  (S : List (Label Names)) → Axioms (ScopedConst C Names S)

def ProofLift (Ay : ScopedAxioms C Names) (S : List (Label Names))
    (Γ : Ctx) (Δ : List (Formula (NamedConst C Names) Γ))
    (p : Formula (NamedConst C Names) Γ) : Prop :=
  ∀ (Δ' : List (Formula (ScopedConst C Names S) Γ))
    (p' : Formula (ScopedConst C Names S) Γ),
    Δ'.map (mapTerm (includeConst S)) = Δ → mapTerm (includeConst S) p' = p →
    Derives (ScopedConst C Names S) (Ay S) Γ Δ' p'

theorem restore_output {Ay : ScopedAxioms C Names} {S Γ Δ}
    {p : Formula (NamedConst C Names) Γ}
    {q r : Formula (ScopedConst C Names S) Γ}
    (hq : mapTerm (includeConst S) q = p)
    (hr : mapTerm (includeConst S) r = p)
    (proof : Derives (ScopedConst C Names S) (Ay S) Γ Δ q) :
    Derives (ScopedConst C Names S) (Ay S) Γ Δ r := by
  have he : q = r := include_injective S (hq.trans hr.symm)
  exact he ▸ proof

theorem map_list_wk (S : List (Label Names))
    (Δ : List (Formula (ScopedConst C Names S) Γ)) :
    (Δ.map (fun p => p.wk (σ := σ))).map (mapTerm (includeConst S)) =
      (Δ.map (mapTerm (includeConst S))).map (fun p => p.wk) := by
  simp only [List.map_map, Function.comp_def, mapTerm_wk]

/-- Finite support is proved by induction on the actual proof tree.
No finite-support or proof-preservation field occurs among the hypotheses. -/
theorem derivation_eventually {Ax : Axioms (NamedConst C Names)}
    {Ay : ScopedAxioms C Names}
    (axiomFinite : ∀ {Γ p}, Ax Γ p → Eventually (fun S =>
      ∃ q : Formula (ScopedConst C Names S) Γ,
        mapTerm (includeConst S) q = p ∧
        Derives (ScopedConst C Names S) (Ay S) Γ [] q))
    {Γ Δ p} (proof : Derives (NamedConst C Names) Ax Γ Δ p) :
    Eventually (fun S => ProofLift Ay S Γ Δ p) := by
  induction proof with
  | hyp h =>
      apply eventually_of_forall
      intro S Δ' p' hΔ hp
      apply Derives.hyp
      have hm : mapTerm (includeConst S) p' ∈ Δ'.map (mapTerm (includeConst S)) := by
        rw [hΔ, hp]
        exact h
      rcases List.mem_map.mp hm with ⟨q, hq, he⟩
      have hqp : q = p' := include_injective S he
      exact hqp ▸ hq
  | ax h =>
      apply eventually_mono (axiomFinite h)
      rintro S ⟨q, hq, hproof⟩ Δ' p' _ hp
      exact restore_output hq hp hproof.lift
  | @weaken Γ Δ Δ₂ p h _ ih =>
      apply eventually_mono (eventually_and ih (list_eventually Δ))
      rintro S ⟨ih, ⟨Δ₀, h₀⟩⟩ Δ' p' hΔ hp
      apply Derives.weaken ?_ (ih Δ₀ p' h₀ hp)
      intro q hq
      have hm : mapTerm (includeConst S) q ∈ Δ'.map (mapTerm (includeConst S)) := by
        rw [hΔ]
        apply h
        rw [← h₀]
        exact List.mem_map_of_mem hq
      rcases List.mem_map.mp hm with ⟨r, hr, he⟩
      have hEq : r = q := include_injective S he
      exact hEq ▸ hr
  | @impI Γ Δ p q _ ih =>
      apply eventually_mono (eventually_and ih
        (eventually_and (term_eventually p) (term_eventually q)))
      rintro S ⟨ih, ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (q := .imp p₀ q₀)
        (by simp only [mapTerm, hp₀, hq₀]) hout
        (.impI (ih (p₀ :: Δ') q₀ (by simp [hΔ, hp₀]) hq₀))
  | @impE Γ Δ p q _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂) (term_eventually p))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨p₀, hp₀⟩⟩ Δ' out hΔ hout
      exact .impE (ih₁ Δ' (.imp p₀ out) hΔ (by simp only [mapTerm, hp₀, hout]))
        (ih₂ Δ' p₀ hΔ hp₀)
  | @iffI Γ Δ p q _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂)
        (eventually_and (term_eventually p) (term_eventually q)))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (q := .iff p₀ q₀)
        (by simp only [mapTerm, hp₀, hq₀]) hout
        (.iffI (ih₁ Δ' (.imp p₀ q₀) hΔ (by simp only [mapTerm, hp₀, hq₀]))
          (ih₂ Δ' (.imp q₀ p₀) hΔ (by simp only [mapTerm, hp₀, hq₀])))
  | @iffE₁ Γ Δ p q _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂) (term_eventually p))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨p₀, hp₀⟩⟩ Δ' out hΔ hout
      exact .iffE₁ (ih₁ Δ' (.iff p₀ out) hΔ (by simp only [mapTerm, hp₀, hout]))
        (ih₂ Δ' p₀ hΔ hp₀)
  | @iffE₂ Γ Δ p q _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂) (term_eventually q))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨q₀, hq₀⟩⟩ Δ' out hΔ hout
      exact .iffE₂ (ih₁ Δ' (.iff out q₀) hΔ (by simp only [mapTerm, hq₀, hout]))
        (ih₂ Δ' q₀ hΔ hq₀)
  | topI =>
      apply eventually_of_forall
      intro S Δ' out _ hout
      exact restore_output (q := .top) rfl hout .topI
  | eqRefl a =>
      apply eventually_mono (term_eventually a)
      rintro S ⟨a₀, ha₀⟩ Δ' out _ hout
      exact restore_output (by simp only [mapTerm, ha₀]) hout (.eqRefl a₀)
  | @eqSymm Γ Δ σ a b _ ih =>
      apply eventually_mono (eventually_and ih
        (eventually_and (term_eventually a) (term_eventually b)))
      rintro S ⟨ih, ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by simp only [mapTerm, ha₀, hb₀]) hout
        (.eqSymm (ih Δ' (.eq a₀ b₀) hΔ (by simp only [mapTerm, ha₀, hb₀])))
  | @eqTrans Γ Δ σ a b c _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂)
        (eventually_and (term_eventually a)
          (eventually_and (term_eventually b) (term_eventually c))))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨⟨a₀, ha₀⟩, ⟨⟨b₀, hb₀⟩, ⟨c₀, hc₀⟩⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by simp only [mapTerm, ha₀, hc₀]) hout
        (.eqTrans (ih₁ Δ' (.eq a₀ b₀) hΔ (by simp only [mapTerm, ha₀, hb₀]))
          (ih₂ Δ' (.eq b₀ c₀) hΔ (by simp only [mapTerm, hb₀, hc₀])))
  | @eqApp Γ Δ σ ρ f g a b _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂)
        (eventually_and (eventually_and (term_eventually f) (term_eventually g))
          (eventually_and (term_eventually a) (term_eventually b))))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨⟨⟨f₀, hf₀⟩, ⟨g₀, hg₀⟩⟩, ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by simp only [mapTerm, hf₀, hg₀, ha₀, hb₀]) hout
        (.eqApp (ih₁ Δ' (.eq f₀ g₀) hΔ (by simp only [mapTerm, hf₀, hg₀]))
          (ih₂ Δ' (.eq a₀ b₀) hΔ (by simp only [mapTerm, ha₀, hb₀])))
  | @eqRight Γ Δ σ a b c _ ih =>
      apply eventually_mono (eventually_and ih
        (eventually_and (term_eventually a)
          (eventually_and (term_eventually b) (term_eventually c))))
      rintro S ⟨ih, ⟨⟨a₀, ha₀⟩, ⟨⟨b₀, hb₀⟩, ⟨c₀, hc₀⟩⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by simp only [mapTerm, ha₀, hb₀, hc₀]) hout
        (.eqRight a₀ (ih Δ' (.eq b₀ c₀) hΔ (by simp only [mapTerm, hb₀, hc₀])))
  | @eqTruth Γ Δ p q _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂) (term_eventually p))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨p₀, hp₀⟩⟩ Δ' out hΔ hout
      exact .eqTruth (ih₁ Δ' (.eq p₀ out) hΔ (by simp only [mapTerm, hp₀, hout]))
        (ih₂ Δ' p₀ hΔ hp₀)
  | eqSubst P a b _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂)
        (eventually_and (term_eventually P)
          (eventually_and (term_eventually a) (term_eventually b))))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨⟨P₀, hP₀⟩, ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by rw [mapTerm_inst, hP₀, hb₀]) hout
        (.eqSubst P₀ a₀ b₀
          (ih₁ Δ' (.eq a₀ b₀) hΔ (by simp only [mapTerm, ha₀, hb₀]))
          (ih₂ Δ' (P₀.inst a₀) hΔ (by rw [mapTerm_inst, hP₀, ha₀])))
  | @allI Γ Δ σ P _ ih =>
      apply eventually_mono (eventually_and ih (term_eventually P))
      rintro S ⟨ih, ⟨P₀, hP₀⟩⟩ Δ' out hΔ hout
      exact restore_output (by simp only [mapTerm, hP₀]) hout
        (.allI (ih (Δ'.map (fun p => p.wk)) P₀ (by rw [map_list_wk, hΔ]) hP₀))
  | @allE Γ Δ σ P a _ ih =>
      apply eventually_mono (eventually_and ih
        (eventually_and (term_eventually P) (term_eventually a)))
      rintro S ⟨ih, ⟨⟨P₀, hP₀⟩, ⟨a₀, ha₀⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by rw [mapTerm_inst, hP₀, ha₀]) hout
        (.allE a₀ (ih Δ' (.all P₀) hΔ (by simp only [mapTerm, hP₀])))
  | @exI Γ Δ σ P a _ ih =>
      apply eventually_mono (eventually_and ih
        (eventually_and (term_eventually P) (term_eventually a)))
      rintro S ⟨ih, ⟨⟨P₀, hP₀⟩, ⟨a₀, ha₀⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by simp only [mapTerm, hP₀]) hout
        (.exI a₀ (ih Δ' (P₀.inst a₀) hΔ (by rw [mapTerm_inst, hP₀, ha₀])))
  | @exE Γ Δ σ P q _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂) (term_eventually P))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨P₀, hP₀⟩⟩ Δ' out hΔ hout
      exact .exE (ih₁ Δ' (.ex P₀) hΔ (by simp only [mapTerm, hP₀]))
        (ih₂ (P₀ :: Δ'.map (fun p => p.wk)) out.wk
          (by simp only [List.map_cons, map_list_wk, hP₀, hΔ])
          (by rw [mapTerm_wk, hout]))
  | @nec Γ p _ ih =>
      apply eventually_mono (eventually_and ih (term_eventually p))
      rintro S ⟨ih, ⟨p₀, hp₀⟩⟩ Δ' out hΔ hout
      have hn : Δ' = [] := by
        cases Δ' with
        | nil => rfl
        | cons a Δ' =>
            change _ :: _ = [] at hΔ
            cases hΔ
      subst Δ'
      exact restore_output (by simp only [Term.box, mapTerm, hp₀]) hout
        (.nec (ih [] p₀ rfl hp₀))
  | @K Γ Δ p q _ _ ih₁ ih₂ =>
      apply eventually_mono (eventually_and (eventually_and ih₁ ih₂)
        (eventually_and (term_eventually p) (term_eventually q)))
      rintro S ⟨⟨ih₁, ih₂⟩, ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by simp only [Term.box, mapTerm, hq₀]) hout
        (.K (ih₁ Δ' (Term.box (.imp p₀ q₀)) hΔ
            (by simp only [Term.box, mapTerm, hp₀, hq₀]))
          (ih₂ Δ' p₀.box hΔ (by simp only [Term.box, mapTerm, hp₀])))
  | intensionality ρ a b _ ih =>
      apply eventually_mono (eventually_and ih
        (eventually_and (term_eventually a) (term_eventually b)))
      rintro S ⟨ih, ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩⟩ Δ' out hΔ hout
      exact restore_output (by simp only [mapTerm, ha₀, hb₀]) hout
        (.intensionality ρ a₀ b₀ (ih Δ' (Term.box (Term.coext ρ a₀ b₀)) hΔ
          (by simp only [Term.box, mapTerm, mapTerm_coext, ha₀, hb₀])))
  | comprehension A =>
      apply eventually_mono (body_eventually A)
      rintro S ⟨A₀, hA₀⟩ Δ' out _ hout
      exact restore_output (by simp only [mapTerm, mapTerm_body_code, hA₀]) hout
        (.comprehension A₀)

/-- The universal preimage formulation above yields a literal derivation
in a finite sub-signature, including its local boundary formulas. -/
theorem finite_derivation_support {Ax : Axioms (NamedConst C Names)}
    {Ay : ScopedAxioms C Names}
    (axiomFinite : ∀ {Γ p}, Ax Γ p → Eventually (fun S =>
      ∃ q : Formula (ScopedConst C Names S) Γ,
        mapTerm (includeConst S) q = p ∧
        Derives (ScopedConst C Names S) (Ay S) Γ [] q))
    {Γ Δ p} (proof : Derives (NamedConst C Names) Ax Γ Δ p) :
    ∃ (S : List (Label Names)) (Δ' : List (Formula (ScopedConst C Names S) Γ))
      (p' : Formula (ScopedConst C Names S) Γ),
      Δ'.map (mapTerm (includeConst S)) = Δ ∧ mapTerm (includeConst S) p' = p ∧
      Derives (ScopedConst C Names S) (Ay S) Γ Δ' p' := by
  have he := eventually_and (derivation_eventually axiomFinite proof)
    (eventually_and (list_eventually Δ) (term_eventually p))
  rcases he with ⟨S, hS⟩
  rcases hS S (fun _ h => h) with ⟨hp, ⟨⟨Δ', hΔ⟩, ⟨p', hp'⟩⟩⟩
  exact ⟨S, Δ', p', hΔ, hp', hp Δ' p' hΔ hp'⟩

#print axioms derivation_eventually
#print axioms finite_derivation_support

end Classicism.Research.ModalFiniteNameSupport
