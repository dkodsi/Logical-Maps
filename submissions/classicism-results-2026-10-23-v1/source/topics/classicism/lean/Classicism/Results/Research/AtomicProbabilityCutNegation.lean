import Classicism.Results.Research.AtomicProbabilityCutArithmetic

/-!
# Rounded reflection of a cut's complement

Shallow C language, current premises, fixed admitted code type. The reflection
is a binary graph. It is not an assumed operation returning an individual.
Theorems prove closure and involution of this cut operation; they do NOT prove
that it is an additive inverse. That latter claim needs a small-gap/Archimedean
argument, not merely dense ordered-group laws on the input codes.

Source: internal Dedekind-real resource required by the probability research
notes; proof developed for this formalization, OpenAI Codex, 22 October 2026.
-/

namespace Classicism.Research.ProbabilityCuts

variable {σ : Type} [Ty σ]

def CodeNegTotal (Neg : σ → σ → Prop) : Prop := ∀ a, ∃ b, Neg a b

def CodeNegInvolutive (Neg : σ → σ → Prop) : Prop := ∀ a b, Neg a b → Neg b a

def CodeNegReverses (lt : σ → σ → Prop) (Neg : σ → σ → Prop) : Prop :=
  ∀ a b a' b', Neg a a' → Neg b b' → (lt a b ↔ lt b' a')

def cutNeg (lt : σ → σ → Prop) (Neg : σ → σ → Prop) (P : σ → Prop) : σ → Prop :=
  fun r => ∃ a b, ¬ P a ∧ Neg a b ∧ lt r b

theorem cutNeg_is_cut (lt : σ → σ → Prop) (Neg : σ → σ → Prop)
    (ho : StrictCodeOrder lt) (hd : CodeDense lt) (hbelow : ∀ a, ∃ b, lt b a)
    (ht : CodeNegTotal Neg) (hr : CodeNegReverses lt Neg)
    (P : σ → Prop) (hP : LowerCut lt P) : LowerCut lt (cutNeg lt Neg P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hP.2.1
    obtain ⟨b, hab⟩ := ht a
    obtain ⟨r, hrb⟩ := hbelow b
    exact ⟨r, a, b, ha, hab, hrb⟩
  · obtain ⟨p, hp⟩ := hP.1
    obtain ⟨q, hpq⟩ := ht p
    refine ⟨q, ?_⟩
    intro hq
    obtain ⟨a, b, ha, hab, hqb⟩ := hq
    have hap := (hr a p b q hab hpq).2 hqb
    exact ha (hP.2.2.1 a p hap hp)
  · intro r t hrt htneg
    obtain ⟨a, b, ha, hab, htb⟩ := htneg
    exact ⟨a, b, ha, hab, ho.2.1 r t b hrt htb⟩
  · intro r hrneg
    obtain ⟨a, b, ha, hab, hrb⟩ := hrneg
    obtain ⟨t, hrt, htb⟩ := hd r b hrb
    exact ⟨t, ⟨a, b, ha, hab, htb⟩, hrt⟩

theorem cutNeg_antitone (lt : σ → σ → Prop) (Neg : σ → σ → Prop)
    (P Q : σ → Prop) (hPQ : Included P Q) :
    Included (cutNeg lt Neg Q) (cutNeg lt Neg P) := by
  intro r hr
  obtain ⟨a, b, ha, hab, hrb⟩ := hr
  exact ⟨a, b, fun hPa => ha (hPQ a hPa), hab, hrb⟩

/-- Roundedness is essential for the forward inclusion; density for the reverse. -/
theorem cutNeg_involutive (lt : σ → σ → Prop) (Neg : σ → σ → Prop)
    (hd : CodeDense lt) (ht : CodeNegTotal Neg) (hi : CodeNegInvolutive Neg)
    (hr : CodeNegReverses lt Neg) (P : σ → Prop) (hP : LowerCut lt P) :
    SameCut (cutNeg lt Neg (cutNeg lt Neg P)) P := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, b, ha, hab, hxb⟩ := hx
    cases em (P x) with
    | inl hPx => exact hPx
    | inr hPx =>
      apply False.elim
      apply ha
      obtain ⟨y, hxy, hyb⟩ := hd x b hxb
      obtain ⟨z, hyz⟩ := ht y
      have hnPy : ¬ P y := fun hPy => hPx (hP.2.2.1 x y hxy hPy)
      have haz := (hr y b z a hyz (hi a b hab)).1 hyb
      exact ⟨y, z, hnPy, hyz, haz⟩
  · intro hPx
    obtain ⟨y, hPy, hxy⟩ := hP.2.2.2 x hPx
    obtain ⟨z, hyz⟩ := ht y
    have hnNeg : ¬ cutNeg lt Neg P z := by
      intro hz
      obtain ⟨a, b, ha, hab, hzb⟩ := hz
      have hay := (hr a y b z hab hyz).2 hzb
      exact ha (hP.2.2.1 a y hay hPy)
    exact ⟨z, y, hnNeg, hi y z hyz, hxy⟩

/-- The easy inclusion in the additive-inverse law. The reverse is deliberately
not asserted without the rational small-gap/Archimedean resource. -/
theorem cutAdd_neg_below_zero (lt : σ → σ → Prop) (Add : σ → σ → σ → Prop)
    (Neg : σ → σ → Prop) (ho : StrictCodeOrder lt)
    (ht : CodeAddTotal Add) (hc : CodeAddComm Add)
    (hm : CodeAddRightStrict lt Add) (zero : σ)
    (hz : ∀ a b, Neg a b → Add a b zero) (P : σ → Prop) (hP : LowerCut lt P) :
    Included (cutAdd Add P (cutNeg lt Neg P)) (principalCut lt zero) := by
  intro r hsum
  obtain ⟨p, q, hp, hq, hpqr⟩ := hsum
  obtain ⟨a, b, ha, hab, hqb⟩ := hq
  have hpa := cut_member_below_nonmember lt ho P hP p a hp ha
  exact codeAdd_strict_both lt Add ho ht hc hm p q r a b zero hpqr (hz a b hab) hpa hqb

end Classicism.Research.ProbabilityCuts
