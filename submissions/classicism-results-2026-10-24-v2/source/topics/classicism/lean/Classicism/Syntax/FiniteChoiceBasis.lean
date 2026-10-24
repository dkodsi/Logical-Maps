import Classicism.Syntax.Entailment

/-!
# Finite support and the nonfinite-basis reduction

These are metatheorems about the actual `Derivable` relation of C. In
particular the Logical Equivalence/Subst premises retain their restricted
logical axiom sets. No compactness, forcing construction or separation model
is assumed as a new axiom.

`not_finitely_axiomatizable` is conditional on an explicitly supplied gap for
every finite fragment. It formalizes the final deduction in
`research/2026-10-22/followup/finite-functional-choice.md` §4, not the symmetric
models that establish that hypothesis for full boxed Functional Choice.
-/

namespace Classicism.Meta.FiniteChoiceBasis

variable {Sig : Signature}

def ofList (L : List (Sentence Sig)) : AxiomSet Sig := fun a => a ∈ L

def Supported (Ax : AxiomSet Sig) {Γ : Ctx}
    (Δ : List (Formula Sig Γ)) (p : Formula Sig Γ) : Prop :=
  ∃ L : List (Sentence Sig), (∀ a ∈ L, Ax a) ∧
    Derivable (C.axioms ∪ ofList L) Δ p

private theorem liftList {L M : List (Sentence Sig)}
    (hLM : ∀ a, a ∈ L → a ∈ M) {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}
    (h : Derivable (C.axioms ∪ ofList L) Δ p) :
    Derivable (C.axioms ∪ ofList M) Δ p :=
  Derivable.mono (fun a ha => ha.elim Or.inl (fun h => Or.inr (hLM a h))) h

private theorem merge₂ {Ax : AxiomSet Sig} {Γ₁ Γ₂ : Ctx}
    {Δ₁ : List (Formula Sig Γ₁)} {Δ₂ : List (Formula Sig Γ₂)}
    {p₁ : Formula Sig Γ₁} {p₂ : Formula Sig Γ₂}
    (h₁ : Supported Ax Δ₁ p₁) (h₂ : Supported Ax Δ₂ p₂) :
    ∃ L, (∀ a ∈ L, Ax a) ∧
      Derivable (C.axioms ∪ ofList L) Δ₁ p₁ ∧
      Derivable (C.axioms ∪ ofList L) Δ₂ p₂ := by
  obtain ⟨L, hL, d₁⟩ := h₁
  obtain ⟨M, hM, d₂⟩ := h₂
  refine ⟨L ++ M, ?_, ?_, ?_⟩
  · intro a ha
    exact (List.mem_append.mp ha).elim (hL a) (hM a)
  · exact liftList (fun _ h => List.mem_append.mpr (Or.inl h)) d₁
  · exact liftList (fun _ h => List.mem_append.mpr (Or.inr h)) d₂

private theorem merge₃ {Ax : AxiomSet Sig} {Γ₁ Γ₂ Γ₃ : Ctx}
    {Δ₁ : List (Formula Sig Γ₁)} {Δ₂ : List (Formula Sig Γ₂)}
    {Δ₃ : List (Formula Sig Γ₃)}
    {p₁ : Formula Sig Γ₁} {p₂ : Formula Sig Γ₂} {p₃ : Formula Sig Γ₃}
    (h₁ : Supported Ax Δ₁ p₁) (h₂ : Supported Ax Δ₂ p₂)
    (h₃ : Supported Ax Δ₃ p₃) :
    ∃ L, (∀ a ∈ L, Ax a) ∧
      Derivable (C.axioms ∪ ofList L) Δ₁ p₁ ∧
      Derivable (C.axioms ∪ ofList L) Δ₂ p₂ ∧
      Derivable (C.axioms ∪ ofList L) Δ₃ p₃ := by
  obtain ⟨L, hL, d₁⟩ := h₁
  obtain ⟨M, hM, d₂⟩ := h₂
  obtain ⟨N, hN, d₃⟩ := h₃
  refine ⟨L ++ (M ++ N), ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (List.mem_append.mp ha).elim (hL a)
      (fun h => (List.mem_append.mp h).elim (hM a) (hN a))
  · exact liftList (fun _ h => List.mem_append.mpr (Or.inl h)) d₁
  · exact liftList (fun _ h => List.mem_append.mpr
      (Or.inr (List.mem_append.mpr (Or.inl h)))) d₂
  · exact liftList (fun _ h => List.mem_append.mpr
      (Or.inr (List.mem_append.mpr (Or.inr h)))) d₃

/-- Every derivation uses finitely many optional axioms. The Subst case does
not move optional axioms into either Logical Equivalence premise. -/
theorem finiteSupportOf {Ax : AxiomSet Sig} : ∀ {B : AxiomSet Sig} {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derivable B Δ p → (∀ a, B a → (C.axioms ∪ Ax) a) → Supported Ax Δ p
  | _, _, _, _, .hyp h, hA => ⟨[], by simp, .hyp h⟩
  | _, _, _, _, .ax (a := a) h, hA => by
    rcases hA a h with hC | hOpt
    · exact ⟨[], by simp, .ax (Or.inl hC)⟩
    · refine ⟨[a], ?_, .ax (Or.inr (List.mem_cons_self))⟩
      intro b hb
      have he : b = a := List.mem_singleton.mp hb
      subst b
      exact hOpt
  | _, _, _, _, .andI h₁ h₂, hA => by
    obtain ⟨L, hL, d₁, d₂⟩ := merge₂ (finiteSupportOf h₁ hA) (finiteSupportOf h₂ hA)
    exact ⟨L, hL, .andI d₁ d₂⟩
  | _, _, _, _, .andE₁ h, hA => by
    obtain ⟨L, hL, d⟩ := finiteSupportOf h hA
    exact ⟨L, hL, .andE₁ d⟩
  | _, _, _, _, .andE₂ h, hA => by
    obtain ⟨L, hL, d⟩ := finiteSupportOf h hA
    exact ⟨L, hL, .andE₂ d⟩
  | _, _, _, _, .orI₁ h, hA => by
    obtain ⟨L, hL, d⟩ := finiteSupportOf h hA
    exact ⟨L, hL, .orI₁ d⟩
  | _, _, _, _, .orI₂ h, hA => by
    obtain ⟨L, hL, d⟩ := finiteSupportOf h hA
    exact ⟨L, hL, .orI₂ d⟩
  | _, _, _, _, .orE h h₁ h₂, hA => by
    obtain ⟨L, hL, d, d₁, d₂⟩ :=
      merge₃ (finiteSupportOf h hA) (finiteSupportOf h₁ hA) (finiteSupportOf h₂ hA)
    exact ⟨L, hL, .orE d d₁ d₂⟩
  | _, _, _, _, .notI h₁ h₂, hA => by
    obtain ⟨L, hL, d₁, d₂⟩ := merge₂ (finiteSupportOf h₁ hA) (finiteSupportOf h₂ hA)
    exact ⟨L, hL, .notI d₁ d₂⟩
  | _, _, _, _, .notE h₁ h₂, hA => by
    obtain ⟨L, hL, d₁, d₂⟩ := merge₂ (finiteSupportOf h₁ hA) (finiteSupportOf h₂ hA)
    exact ⟨L, hL, .notE d₁ d₂⟩
  | _, _, _, _, .em p, hA => ⟨[], by simp, .em p⟩
  | _, _, _, _, .allE h a, hA => by
    obtain ⟨L, hL, d⟩ := finiteSupportOf h hA
    exact ⟨L, hL, .allE d a⟩
  | _, _, _, _, .allI h, hA => by
    obtain ⟨L, hL, d⟩ := finiteSupportOf h hA
    exact ⟨L, hL, .allI d⟩
  | _, _, _, _, .exI a h, hA => by
    obtain ⟨L, hL, d⟩ := finiteSupportOf h hA
    exact ⟨L, hL, .exI a d⟩
  | _, _, _, _, .exE h h', hA => by
    obtain ⟨L, hL, d, d'⟩ := merge₂ (finiteSupportOf h hA) (finiteSupportOf h' hA)
    exact ⟨L, hL, .exE d d'⟩
  | _, _, _, _, .refl a, hA => ⟨[], by simp, .refl a⟩
  | _, _, _, _, .ll F h₁ h₂, hA => by
    obtain ⟨L, hL, d₁, d₂⟩ := merge₂ (finiteSupportOf h₁ hA) (finiteSupportOf h₂ hA)
    exact ⟨L, hL, .ll F d₁ d₂⟩
  | B, _, _, _, .subst K h₁ h₂ h₃, hA => by
    obtain ⟨L, hL, d₃⟩ := finiteSupportOf h₃ hA
    have hlog : ∀ a, B.logical a →
        (C.axioms ∪ ofList L).logical a :=
      fun a ha => ⟨Or.inl ((C.logical_union Ax a).mp ⟨hA a ha.1, ha.2⟩), ha.2⟩
    exact ⟨L, hL, .subst K (Derivable.mono hlog h₁) (Derivable.mono hlog h₂) d₃⟩
  | _, _, _, _, .conv h c, hA => by
    obtain ⟨L, hL, d⟩ := finiteSupportOf h hA
    exact ⟨L, hL, .conv d c⟩

theorem finiteSupport {Ax : AxiomSet Sig} {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}
    (h : Derivable (C.axioms ∪ Ax) Δ p) : Supported Ax Δ p :=
  finiteSupportOf h (fun _ hA => hA)

/-- Finitely many conclusions of a schema have one finite axiom support. -/
theorem finiteSupportList {Ax : AxiomSet Sig} :
    ∀ L : List (Sentence Sig), (∀ a ∈ L, Theorem (C.axioms ∪ Ax) a) →
      ∃ K, (∀ a ∈ K, Ax a) ∧ (ofList K ⟹ ofList L)
  | [], _ => ⟨[], by simp, fun _ h => False.elim (List.not_mem_nil h)⟩
  | a :: rest, h => by
    obtain ⟨L, hL, da⟩ := finiteSupport (h a (List.mem_cons_self))
    obtain ⟨M, hM, drest⟩ := finiteSupportList rest
      (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨L ++ M, ?_, ?_⟩
    · intro b hb
      exact (List.mem_append.mp hb).elim (hL b) (hM b)
    · intro b hb
      rcases List.mem_cons.mp hb with he | hm
      · subst b
        exact liftList (fun _ hl => List.mem_append.mpr (Or.inl hl)) da
      · exact liftList (fun _ hl => List.mem_append.mpr (Or.inr hl)) (drest b hm)

def FinitelyAxiomatizable (Ax : AxiomSet Sig) : Prop :=
  ∃ L : List (Sentence Sig), (Ax ⟹ ofList L) ∧ (ofList L ⟹ Ax)

def FiniteFragmentGap (Ax : AxiomSet Sig) : Prop :=
  ∀ L : List (Sentence Sig), (∀ a ∈ L, Ax a) →
    ∃ a, Ax a ∧ ¬ Theorem (C.axioms ∪ ofList L) a

/-- The finite-basis argument. Its separation hypothesis is visible and is
not a claim that the Choice countermodels have been formalized. -/
theorem not_finitely_axiomatizable {Ax : AxiomSet Sig}
    (hgap : FiniteFragmentGap Ax) : ¬ FinitelyAxiomatizable Ax := by
  rintro ⟨L, hforward, hback⟩
  obtain ⟨K, hK, hKL⟩ := finiteSupportList L (fun a ha => hforward a ha)
  obtain ⟨a, ha, hn⟩ := hgap K hK
  exact hn ((hKL.trans hback) a ha)

/-- A finite list lies at a common stage of an increasing sequence of axiom
sets. The natural-number quantification is metalogical. -/
theorem finiteStage {stages : Nat → AxiomSet Sig}
    (hmono : ∀ i j, i ≤ j → stages i ⊆ stages j) :
    ∀ L : List (Sentence Sig), (∀ a ∈ L, ∃ n, stages n a) →
      ∃ n, ∀ a ∈ L, stages n a
  | [], _ => ⟨0, by simp⟩
  | a :: rest, h => by
    obtain ⟨i, hi⟩ := h a (List.mem_cons_self)
    obtain ⟨j, hj⟩ := finiteStage hmono rest
      (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨max i j, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with he | hm
    · subst b
      exact hmono i (max i j) (Nat.le_max_left _ _) a hi
    · exact hmono j (max i j) (Nat.le_max_right _ _) b (hj b hm)

/-- Every theorem of the increasing union already belongs to one stage.
The claim is finitary; it does not admit an infinitary proof rule. -/
theorem theorem_at_stage {stages : Nat → AxiomSet Sig}
    (hmono : ∀ i j, i ≤ j → stages i ⊆ stages j) {p : Sentence Sig}
    (h : Theorem (C.axioms ∪ (fun a => ∃ n, stages n a)) p) :
    ∃ n, Theorem (C.axioms ∪ stages n) p := by
  obtain ⟨L, hL, d⟩ := finiteSupport h
  obtain ⟨n, hn⟩ := finiteStage hmono L hL
  exact ⟨n, Derivable.mono
    (fun a ha => ha.elim Or.inl (fun h => Or.inr (hn a h))) d⟩

end Classicism.Meta.FiniteChoiceBasis
