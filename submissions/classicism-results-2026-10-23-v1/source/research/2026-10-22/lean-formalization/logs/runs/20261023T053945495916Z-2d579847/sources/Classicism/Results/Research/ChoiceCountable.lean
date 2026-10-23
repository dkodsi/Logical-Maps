import Classicism.Results.Research.ChoiceChains
import Classicism.Results.Research.ChoiceBoolean

/-!
# Countability transport and the CBC/CCC upgrade

Direct source: `research/2026-10-22/notes/relational-choice-countable-completeness-ccc.md`,
§§1–4 (`misc`, original research, 22 October 2026; unpaginated).
Countability is the library's represented Frege-label relation, not an external
enumeration or Lean's set-theoretic countability predicate.
-/
namespace Classicism.Research.Choice
open Classicism.Paper Classicism.P

/-- Pull labels back through a total relation with disjoint fibers. The relation
need not select one output or one label for each input. -/
theorem countable_pullback {κ σ τ : Type} [Ty κ] [Ty σ] [Ty τ]
    (A : σ → Prop) (B : τ → Prop) (f : σ → τ → Prop)
    (ht : ∀ a, A a → ∃ b, B b ∧ f a b)
    (hi : ∀ a c b, A a → A c → f a b → f c b → a = c)
    (hc : Ctbl κ B) : Ctbl κ A := by
  obtain ⟨L, hL⟩ := hc
  refine ⟨fun a n => ∃ b, B b ∧ f a b ∧ L b n, ?_⟩
  intro a c hac
  constructor
  · intro h
    obtain ⟨n, hn, ⟨b, hb, hab, hbn⟩, ⟨d, hd, hcd, hdn⟩⟩ := h
    have e : b = d := (hL b d ⟨hb, hd⟩).1 ⟨n, hn, hbn, hdn⟩
    exact hi a c b hac.1 hac.2 hab (e.symm ▸ hcd)
  · intro e
    obtain ⟨b, hb, hab⟩ := ht a hac.1
    obtain ⟨n, hn, hbn, _⟩ := (hL b b ⟨hb, hb⟩).2 rfl
    exact ⟨n, hn, ⟨b, hb, hab, hbn⟩, ⟨b, hb, e ▸ hab, hbn⟩⟩

/-- Every represented disjoint family of nonbottom entities is Frege-countable. -/
def BooleanCCC (κ τ : Type) [Ty κ] [Rel τ] : Prop :=
  ∀ D : τ → Prop, (∀ d, D d → d ≠ (⊥ : τ)) →
    (∀ d e, D d → D e → d ≠ e → (d ∧ e) = (⊥ : τ)) → Ctbl κ D

section
variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

def IncrementGraph (f : τ → τ → Prop) (a d : τ) : Prop :=
  ∃ c, f a c ∧ d = (c ∧ ¬ a)

theorem canonical_increments_disjoint (P : τ → Prop) (f : τ → τ → Prop)
    (a b c d : τ)
    (ha : CanonicalUnion P (fun x y => x ≤ y) f a)
    (hb : CanonicalUnion P (fun x y => x ≤ y) f b)
    (hne : a ≠ b) (hac : f a c) (hbd : f b d) :
    ((c ∧ ¬ a) ∧ (d ∧ ¬ b)) = (⊥ : τ) := by
  have hA := canonical_union_conforming P (fun x y : τ => x ≤ y) f
    le_trans_rel le_antisymm_rel
  rcases hA.1.1.2.2 a b ha hb with hab | hba
  · exact disjoint_of_bounds _ _ b
      (le_trans_rel _ _ _ (meet_le_left _ _)
        (canonical_successor_bound P (fun x y : τ => x ≤ y) f
          le_trans_rel le_antisymm_rel a b c ha hb hab hne hac))
      (meet_le_right _ _)
  · have hda := canonical_successor_bound P (fun x y : τ => x ≤ y) f
      le_trans_rel le_antisymm_rel b a d hb ha hba (fun e => hne e.symm) hbd
    exact eq_bot_of_opposite _ a
      (le_trans_rel _ _ _ (meet_le_right _ _)
        (le_trans_rel _ _ _ (meet_le_left _ _) hda))
      (le_trans_rel _ _ _ (meet_le_left _ _) (meet_le_right _ _))

/-- Strictness makes the canonical union countable under Boolean CCC. No
enumeration, arithmetic recursion, or supremum of that union is used here. -/
theorem canonical_countable {κ : Type} [Ty κ]
    (P : τ → Prop) (f : τ → τ → Prop)
    (hserial : ∀ a, P a → ∃ c, f a c)
    (hprog : ∀ a c, P a → f a c → a ≤ c)
    (hstrict : ∀ a c, P a → f a c → a ≠ c)
    (huniq : ∀ a c d, P a → f a c → f a d → c = d)
    (ccc : BooleanCCC κ τ) : Ctbl κ (CanonicalUnion P (fun x y => x ≤ y) f) := by
  let A := CanonicalUnion P (fun x y : τ => x ≤ y) f
  let D : τ → Prop := fun d => ∃ a, A a ∧ IncrementGraph f a d
  have hAP : ∀ a, A a → P a :=
    canonical_member_domain P (fun x y : τ => x ≤ y) f le_trans_rel le_antisymm_rel
  have dnz : ∀ d, D d → d ≠ (⊥ : τ) := by
    intro d hd
    obtain ⟨a, ha, c, hac, e⟩ := hd
    rw [e]
    exact increment_nonzero a c (hprog a c (hAP a ha) hac)
      (hstrict a c (hAP a ha) hac)
  have ddisj : ∀ d e, D d → D e → d ≠ e → (d ∧ e) = (⊥ : τ) := by
    intro d e hd he hne
    obtain ⟨a, ha, c, hac, ed⟩ := hd
    obtain ⟨b, hb, c', hbc', ee⟩ := he
    have hnab : a ≠ b := by
      intro eab
      rw [eab] at hac
      have ecc := huniq b c c' (hAP b hb) hac hbc'
      apply hne
      rw [ed, ee, eab, ecc]
    rw [ed, ee]
    exact canonical_increments_disjoint P f a b c c' ha hb hnab hac hbc'
  apply countable_pullback A D (IncrementGraph f) _ _ (ccc D dnz ddisj)
  · intro a ha
    obtain ⟨c, hac⟩ := hserial a (hAP a ha)
    exact ⟨c ∧ ¬ a, ⟨a, ha, c, hac, rfl⟩, c, hac, rfl⟩
  · intro a b d ha hb had hbd
    refine (em (a = b)).elim id (fun hnab => False.elim ?_)
    obtain ⟨c, hac, ed⟩ := had
    obtain ⟨c', hbc', ed'⟩ := hbd
    have hdisj := canonical_increments_disjoint P f a b c c' ha hb hnab hac hbc'
    rw [← ed, ← ed'] at hdisj
    exact dnz d ⟨a, ha, c, hac, ed⟩ (self_meet_bot d hdisj)

def UpperCut (X : τ → Prop) (b : τ) : Prop := ∀ u, UB u X → b ≤ u

theorem upperCut_lub (X : τ → Prop) (b : τ) (hb : UpperCut X b) (hu : UB b X) :
    LUB b X := fun u =>
  ⟨hb u, fun h x hx => le_trans_rel x b u (hu x hx) h⟩

theorem upperCut_step (X : τ → Prop) (hn : ¬ ∃ j, LUB j X) (b : τ)
    (hb : UpperCut X b) : ∃ c, UpperCut X c ∧ b ≤ c ∧ b ≠ c := by
  have hex : ∃ x, X x ∧ ¬ x ≤ b := (em (∃ x, X x ∧ ¬ x ≤ b)).elim id fun h =>
    (hn ⟨b, upperCut_lub X b hb (fun x hx => (em (x ≤ b)).elim id
      (fun hxb => (h ⟨x, hx, hxb⟩).elim))⟩).elim
  obtain ⟨x, hx, hnxb⟩ := hex
  refine ⟨OrderJoin b x, (fun u hu => orderJoin_le b x u (hb u hu) (hu x hx)),
    le_orderJoin_left b x, ?_⟩
  intro e
  exact hnxb (e.symm ▸ le_orderJoin_right b x)

/-- Actual RC, represented countable completeness, and Boolean CCC give full
Boolean completeness at the same relational type. The counting type is free. -/
theorem choice_countable_ccc_completeness {κ : Type} [Ty κ] :
    RelationalChoice τ τ → CountableBooleanCompleteness κ τ → BooleanCCC κ τ →
      BooleanCompleteness τ := by
  intro rc cbc ccc
  apply BooleanCompleteness.of_lub
  intro X
  refine (em (∃ j, LUB j X)).elim id (fun hn => False.elim ?_)
  let P := UpperCut X
  let U : τ → τ → Prop := fun b c =>
    (P b ∧ P c ∧ b ≤ c ∧ b ≠ c) ∨ (¬ P b ∧ b = c)
  have hser : Serial U := by
    intro b
    exact (em (P b)).elim
      (fun hb => (upperCut_step X hn b hb).elim fun c hc => ⟨c, Or.inl ⟨hb, hc⟩⟩)
      (fun hb => ⟨b, Or.inr ⟨hb, rfl⟩⟩)
  obtain ⟨f, hff, hfU⟩ := rc U hser
  have fs : ∀ b, P b → ∃ c, f b c := fun b _ =>
    (hff b).elim fun c hc => ⟨c, hc.1⟩
  have fc : ∀ b c, P b → f b c → P c := fun b c hb hbc =>
    (hfU b c hbc).elim (fun h => h.2.1) (fun h => (h.1 hb).elim)
  have fp : ∀ b c, P b → f b c → b ≤ c := fun b c hb hbc =>
    (hfU b c hbc).elim (fun h => h.2.2.1) (fun h => (h.1 hb).elim)
  have fst : ∀ b c, P b → f b c → b ≠ c := fun b c hb hbc =>
    (hfU b c hbc).elim (fun h => h.2.2.2) (fun h => (h.1 hb).elim)
  have fu : ∀ b c d, P b → f b c → f b d → c = d := fun b c d _ hbc hbd =>
    (hff b).elim fun v hv => (hv.2 c hbc).symm.trans (hv.2 d hbd)
  let A := CanonicalUnion P (fun x y : τ => x ≤ y) f
  have hAP : ∀ a, A a → P a :=
    canonical_member_domain P (fun x y : τ => x ≤ y) f le_trans_rel le_antisymm_rel
  obtain ⟨u, hu⟩ := cbc A (canonical_countable P f fs fp fst fu ccc)
  have hup : P u := fun v hv => (hu v).1 (fun a ha => hAP a ha v hv)
  have hud : DomainLUB P (fun x y : τ => x ≤ y) A u :=
    ⟨hup, (hu u).2 (le_refl_rel u), fun v _ hv => (hu v).1 hv⟩
  have hfix := canonical_fixedpoint_of_supremum P (fun x y : τ => x ≤ y) f
    le_refl_rel le_trans_rel le_antisymm_rel fs fc fp fu u hud
  exact fst u u hup hfix.2 rfl

end

end Classicism.Research.Choice
