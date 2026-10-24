import Classicism.Results.Research.AtomicProbabilityCuts

/-!
# Graph addition on cut predicates

All types are fixed relational C types. `Add` is a ternary graph, even when
the code type is e; no forbidden e-to-e operation is formed. Results concern
current coextension, not literal predicate identity, and carry no boxes.

These are logical distribution and transport steps for real addition; proving
that an internal rational graph supplies the stated arithmetic laws, and that
these predicates are proper rounded cuts, remains separate work.
Source: finite-subsupremum proof in canonical-atomic-probability.md, section 2,
and graph-valued real bridge in local-propositional-probability.md (unpaginated).
-/

namespace Classicism.Research.ProbabilityCuts

variable {σ : Type} [Ty σ]

def cutAdd (Add : σ → σ → σ → Prop) (P Q : σ → Prop) : σ → Prop :=
  fun r => ∃ p q, P p ∧ Q q ∧ Add p q r

theorem cutAdd_mono (Add : σ → σ → σ → Prop) (P Q U V : σ → Prop)
    (hPU : Included P U) (hQV : Included Q V) :
    Included (cutAdd Add P Q) (cutAdd Add U V) := by
  intro r hr
  obtain ⟨p, q, hp, hq, ha⟩ := hr
  exact ⟨p, q, hPU p hp, hQV q hq, ha⟩

theorem cutAdd_transport (Add : σ → σ → σ → Prop) (P Q U V : σ → Prop)
    (hPU : SameCut P U) (hQV : SameCut Q V) :
    SameCut (cutAdd Add P Q) (cutAdd Add U V) := by
  intro r
  exact ⟨cutAdd_mono Add P Q U V (fun p => (hPU p).1) (fun q => (hQV q).1) r,
    cutAdd_mono Add U V P Q (fun p => (hPU p).2) (fun q => (hQV q).2) r⟩

theorem cutAdd_union_left (Add : σ → σ → σ → Prop)
    (F : (σ → Prop) → Prop) (Q : σ → Prop) :
    ∀ r, cutAdd Add (unionCut F) Q r ↔ ∃ P, F P ∧ cutAdd Add P Q r := by
  intro r
  constructor
  · intro h
    obtain ⟨p, q, hp, hq, ha⟩ := h
    obtain ⟨P, hP, hPp⟩ := hp
    exact ⟨P, hP, p, q, hPp, hq, ha⟩
  · intro h
    obtain ⟨P, hP, p, q, hp, hq, ha⟩ := h
    exact ⟨p, q, ⟨P, hP, hp⟩, hq, ha⟩

theorem cutAdd_union_right (Add : σ → σ → σ → Prop)
    (P : σ → Prop) (F : (σ → Prop) → Prop) :
    ∀ r, cutAdd Add P (unionCut F) r ↔ ∃ Q, F Q ∧ cutAdd Add P Q r := by
  intro r
  constructor
  · intro h
    obtain ⟨p, q, hp, hq, ha⟩ := h
    obtain ⟨Q, hQ, hQq⟩ := hq
    exact ⟨Q, hQ, p, q, hp, hQq, ha⟩
  · intro h
    obtain ⟨Q, hQ, p, q, hp, hq, ha⟩ := h
    exact ⟨p, q, hp, ⟨Q, hQ, hq⟩, ha⟩

theorem cutAdd_comm (Add : σ → σ → σ → Prop)
    (hcomm : ∀ p q r, Add p q r → Add q p r) (P Q : σ → Prop) :
    SameCut (cutAdd Add P Q) (cutAdd Add Q P) := by
  intro r
  constructor
  · intro h
    obtain ⟨p, q, hp, hq, ha⟩ := h
    exact ⟨q, p, hq, hp, hcomm p q r ha⟩
  · intro h
    obtain ⟨q, p, hq, hp, ha⟩ := h
    exact ⟨p, q, hp, hq, hcomm q p r ha⟩

def GraphAssociative (Add : σ → σ → σ → Prop) : Prop :=
  ∀ a b c r, (∃ u, Add a b u ∧ Add u c r) ↔ ∃ v, Add b c v ∧ Add a v r

theorem cutAdd_assoc (Add : σ → σ → σ → Prop) (hassoc : GraphAssociative Add)
    (P Q U : σ → Prop) :
    SameCut (cutAdd Add (cutAdd Add P Q) U) (cutAdd Add P (cutAdd Add Q U)) := by
  intro r
  constructor
  · intro h
    obtain ⟨u, c, hu, hc, hucr⟩ := h
    obtain ⟨a, b, ha, hb, habu⟩ := hu
    obtain ⟨v, hbcv, havr⟩ := (hassoc a b c r).1 ⟨u, habu, hucr⟩
    exact ⟨a, v, ha, ⟨b, c, hb, hc, hbcv⟩, havr⟩
  · intro h
    obtain ⟨a, v, ha, hv, havr⟩ := h
    obtain ⟨b, c, hb, hc, hbcv⟩ := hv
    obtain ⟨u, habu, hucr⟩ := (hassoc a b c r).2 ⟨v, hbcv, havr⟩
    exact ⟨u, c, ⟨a, b, ha, hb, habu⟩, hc, hucr⟩

end Classicism.Research.ProbabilityCuts
