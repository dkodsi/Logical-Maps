import Classicism.Results.Research.AtomicProbabilityCutAddition

/-!
# Order and additive closure of graph-coded cuts

Shallow C language at one admitted code type; CURRENT hypotheses throughout.
The rational order and addition laws are explicitly listed as premises, not
asserted as an already available internal rational construction. Addition is a
ternary graph, never an operation with codomain e. No external Nat is used.

This continues the cut bridge required by the probability research notes.
It does not establish a field, negation/multiplication, Archimedeanness or the
identification of original Frege numbers with any numerical core.
-/

namespace Classicism.Research.ProbabilityCuts

variable {σ : Type} [Ty σ]

def StrictCodeOrder (lt : σ → σ → Prop) : Prop :=
  (∀ a, ¬ lt a a) ∧
  (∀ a b c, lt a b → lt b c → lt a c) ∧
  (∀ a b, lt a b ∨ a = b ∨ lt b a)

def CodeDense (lt : σ → σ → Prop) : Prop :=
  ∀ a b, lt a b → ∃ c, lt a c ∧ lt c b

def principalCut (lt : σ → σ → Prop) (a : σ) : σ → Prop := fun q => lt q a

theorem principal_is_cut (lt : σ → σ → Prop) (ho : StrictCodeOrder lt)
    (hd : CodeDense lt) (hbelow : ∀ a, ∃ b, lt b a) (a : σ) :
    LowerCut lt (principalCut lt a) := by
  refine ⟨hbelow a, ⟨a, ho.1 a⟩, ?_, ?_⟩
  · intro p q hpq hqa
    exact ho.2.1 p q a hpq hqa
  · intro p hpa
    obtain ⟨q, hpq, hqa⟩ := hd p a hpa
    exact ⟨q, hqa, hpq⟩

theorem cut_member_below_nonmember (lt : σ → σ → Prop) (ho : StrictCodeOrder lt)
    (P : σ → Prop) (hP : LowerCut lt P) (p q : σ) (hp : P p) (hq : ¬ P q) :
    lt p q := by
  cases ho.2.2 p q with
  | inl hpq => exact hpq
  | inr h =>
    cases h with
    | inl he => exact False.elim (hq (he ▸ hp))
    | inr hqp => exact False.elim (hq (hP.2.2.1 q p hqp hp))

/-- Every proper lower cut is currently bounded above by a principal cut. -/
theorem cut_principal_upper_bound (lt : σ → σ → Prop) (ho : StrictCodeOrder lt)
    (P : σ → Prop) (hP : LowerCut lt P) : ∃ a, Included P (principalCut lt a) := by
  obtain ⟨a, ha⟩ := hP.2.1
  exact ⟨a, fun p hp => cut_member_below_nonmember lt ho P hP p a hp ha⟩

/-- Linear comparison is current inclusion; literal code identity is a separate bridge. -/
theorem cuts_comparable (lt : σ → σ → Prop) (ho : StrictCodeOrder lt)
    (P Q : σ → Prop) (hP : LowerCut lt P) (hQ : LowerCut lt Q) :
    Included P Q ∨ Included Q P := by
  cases em (Included P Q) with
  | inl h => exact Or.inl h
  | inr hn =>
    have hsep : ∃ a, P a ∧ ¬ Q a := by
      cases em (∃ a, P a ∧ ¬ Q a) with
      | inl h => exact h
      | inr hnone =>
        apply False.elim
        apply hn
        intro a ha
        cases em (Q a) with
        | inl hqa => exact hqa
        | inr hqa => exact False.elim (hnone ⟨a, ha, hqa⟩)
    obtain ⟨a, hPa, hQa⟩ := hsep
    apply Or.inr
    intro q hq
    exact hP.2.2.1 q a (cut_member_below_nonmember lt ho Q hQ q a hq hQa) hPa

theorem principal_injective_coextension (lt : σ → σ → Prop)
    (ho : StrictCodeOrder lt) (a b : σ)
    (he : SameCut (principalCut lt a) (principalCut lt b)) : a = b := by
  cases ho.2.2 a b with
  | inl hab => exact False.elim (ho.1 a ((he a).2 hab))
  | inr h =>
    cases h with
    | inl hab => exact hab
    | inr hba => exact False.elim (ho.1 b ((he b).1 hba))

def CodeAddTotal (Add : σ → σ → σ → Prop) : Prop :=
  ∀ p q, ∃ r, Add p q r

def CodeAddComm (Add : σ → σ → σ → Prop) : Prop :=
  ∀ p q r, Add p q r → Add q p r

/-- Strict monotonicity of translation, stated for a graph. -/
def CodeAddRightStrict (lt : σ → σ → Prop) (Add : σ → σ → σ → Prop) : Prop :=
  ∀ p q q' r r', Add p q r → Add p q' r' → lt q q' → lt r r'

/-- Solving below a sum by lowering its first coordinate; a rational-group resource. -/
def CodeAddLowerSolve (lt : σ → σ → Prop) (Add : σ → σ → σ → Prop) : Prop :=
  ∀ p q r t, Add p q r → lt t r → ∃ p', lt p' p ∧ Add p' q t

theorem codeAdd_strict_both (lt : σ → σ → Prop) (Add : σ → σ → σ → Prop)
    (ho : StrictCodeOrder lt) (ht : CodeAddTotal Add) (hc : CodeAddComm Add)
    (hm : CodeAddRightStrict lt Add) (p q r p' q' r' : σ)
    (ha : Add p q r) (hb : Add p' q' r') (hpp : lt p p') (hqq : lt q q') :
    lt r r' := by
  obtain ⟨t, hpt⟩ := ht p' q
  have hrt := hm q p p' r t (hc p q r ha) (hc p' q t hpt) hpp
  have htr := hm p' q q' t r' hpt hb hqq
  exact ho.2.1 r t r' hrt htr

/-- Proper rounded cuts are closed under existential graph addition. -/
theorem cutAdd_is_cut (lt : σ → σ → Prop) (Add : σ → σ → σ → Prop)
    (ho : StrictCodeOrder lt) (ht : CodeAddTotal Add) (hc : CodeAddComm Add)
    (hm : CodeAddRightStrict lt Add) (hs : CodeAddLowerSolve lt Add)
    (P Q : σ → Prop) (hP : LowerCut lt P) (hQ : LowerCut lt Q) :
    LowerCut lt (cutAdd Add P Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hP.1
    obtain ⟨q, hq⟩ := hQ.1
    obtain ⟨r, ha⟩ := ht p q
    exact ⟨r, p, q, hp, hq, ha⟩
  · obtain ⟨a, ha⟩ := hP.2.1
    obtain ⟨b, hb⟩ := hQ.2.1
    obtain ⟨c, hab⟩ := ht a b
    refine ⟨c, ?_⟩
    intro hsum
    obtain ⟨p, q, hp, hq, hpqc⟩ := hsum
    have hpa := cut_member_below_nonmember lt ho P hP p a hp ha
    have hqb := cut_member_below_nonmember lt ho Q hQ q b hq hb
    exact ho.1 c (codeAdd_strict_both lt Add ho ht hc hm p q c a b c hpqc hab hpa hqb)
  · intro t r htr hr
    obtain ⟨p, q, hp, hq, ha⟩ := hr
    obtain ⟨p', hpp, hpq⟩ := hs p q r t ha htr
    exact ⟨p', q, hP.2.2.1 p' p hpp hp, hq, hpq⟩
  · intro r hr
    obtain ⟨p, q, hp, hq, ha⟩ := hr
    obtain ⟨p', hpp, hltp⟩ := hP.2.2.2 p hp
    obtain ⟨q', hqq, hltq⟩ := hQ.2.2.2 q hq
    obtain ⟨r', hb⟩ := ht p' q'
    exact ⟨r', ⟨p', q', hpp, hqq, hb⟩,
      codeAdd_strict_both lt Add ho ht hc hm p q r p' q' r' ha hb hltp hltq⟩

theorem codeAdd_below_split (lt : σ → σ → Prop) (Add : σ → σ → σ → Prop)
    (hd : CodeDense lt) (hc : CodeAddComm Add) (hs : CodeAddLowerSolve lt Add)
    (a b c r : σ) (ha : Add a b c) (hr : lt r c) :
    ∃ p q, lt p a ∧ lt q b ∧ Add p q r := by
  obtain ⟨t, hrt, htc⟩ := hd r c hr
  obtain ⟨p, hpa, hpbt⟩ := hs a b c t ha htc
  obtain ⟨q, hqb, hqpr⟩ := hs b p t r (hc p b t hpbt) hrt
  exact ⟨p, q, hpa, hqb, hc q p r hqpr⟩

/-- The rational code embedding respects addition, at the level of current coextension. -/
theorem principalCut_add (lt : σ → σ → Prop) (Add : σ → σ → σ → Prop)
    (ho : StrictCodeOrder lt) (hd : CodeDense lt) (ht : CodeAddTotal Add)
    (hc : CodeAddComm Add) (hm : CodeAddRightStrict lt Add)
    (hs : CodeAddLowerSolve lt Add) (a b c : σ) (ha : Add a b c) :
    SameCut (cutAdd Add (principalCut lt a) (principalCut lt b)) (principalCut lt c) := by
  intro r
  constructor
  · intro h
    obtain ⟨p, q, hp, hq, hpqr⟩ := h
    exact codeAdd_strict_both lt Add ho ht hc hm p q r a b c hpqr ha hp hq
  · intro h
    exact codeAdd_below_split lt Add hd hc hs a b c r ha h

theorem cutAdd_zero (lt : σ → σ → Prop) (Add : σ → σ → σ → Prop)
    (hc : CodeAddComm Add) (hm : CodeAddRightStrict lt Add)
    (hs : CodeAddLowerSolve lt Add) (zero : σ) (hz : ∀ p, Add p zero p)
    (P : σ → Prop) (hP : LowerCut lt P) :
    SameCut (cutAdd Add P (principalCut lt zero)) P := by
  intro r
  constructor
  · intro h
    obtain ⟨p, q, hp, hq, ha⟩ := h
    have hrp := hm p q zero r p ha (hz p) hq
    exact hP.2.2.1 r p hrp hp
  · intro hr
    obtain ⟨p, hp, hrp⟩ := hP.2.2.2 r hr
    obtain ⟨q, hq, hqp⟩ := hs zero p p r (hc p zero p (hz p)) hrp
    exact ⟨p, q, hp, hq, hc q p r hqp⟩

end Classicism.Research.ProbabilityCuts
