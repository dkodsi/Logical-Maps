import Classicism.Results.Research.FullTypedLogicalSeparationCTransport
import Classicism.Results.Research.FullTypedLogicalSeparationClosedTypes

/-!
# Full typed logical separation contains actual repository C

Original proof, misc, 23 October 2026, unpaginated. The recursive proof
transformation and grounding argument are described in
research/2026-10-23/operator-characterizations/actual-c-observer-bridge-review.txt.

The premise is the actual repository C derivation, including its recursive
logical Subst premises. The boundary is the paper's fixed language: closed
constant types, closed context types and closed types in every boundary
formula. Intermediate type variables are grounded by an actual proof-tree
transformation. No ClosedH, CFromH or externally supplied support witness
appears in the final endpoint. Local hypotheses remain local.
-/

namespace Classicism.Meta.Research.FullTypedLogicalSeparation
open Classicism.Research.FullTypedLogicalSeparationH

variable {Sig : Signature}

/-- The same-signature, same-sequent actual C endpoint. -/
theorem actual_c_sequent (hSig : ∀ c, (Sig.typeOf c).Closed)
    {Γ : Ctx} (hΓ : Ty.AllClosed Γ) {Δ : List (Formula Sig Γ)}
    (hΔ : ∀ p ∈ Δ, p.closedTypes = true) {p : Formula Sig Γ}
    (hp : p.closedTypes = true) (h : C.Derivable Δ p) :
    Derives OSAx Δ p := by
  obtain ⟨S, hS, hs⟩ := c_closed_sequent hSig hΓ hΔ hp h
  exact supported_c_sequent hS hs

/-- Every actual C theorem in the paper's language is an H+OS theorem. -/
theorem actual_c_theorem (hSig : ∀ c, (Sig.typeOf c).Closed)
    {p : Sentence Sig} (hp : p.closedTypes = true) (h : C.Theorem p) :
    Derives OSAx [] p := by
  obtain ⟨S, hS, hs⟩ := c_closed_theorem hSig hp h
  exact supported_c_theorem hS hs

/-- The full target, with actual repository C rather than a new C presentation.
Barcan and Functionality are the direct H+OS derivations, independently of C. -/
theorem h_full_logical_separation_actual_c
    (hSig : ∀ c, (Sig.typeOf c).Closed) :
    (∀ {Γ : Ctx}, Ty.AllClosed Γ →
      ∀ {Δ : List (Formula Sig Γ)}, (∀ p ∈ Δ, p.closedTypes = true) →
      ∀ {p : Formula Sig Γ}, p.closedTypes = true →
      C.Derivable Δ p → Derives OSAx Δ p) ∧
    (∀ σ : Ty, σ.Closed → Derives OSAx [] (barcanSentence (Sig := Sig) σ)) ∧
    (∀ (σ : Ty) (ρ : RTy), σ.Closed → ρ.Closed →
      Derives OSAx [] (functionalitySentence (Sig := Sig) σ ρ)) :=
  ⟨actual_c_sequent hSig, barcan_os, functionality_os⟩

end Classicism.Meta.Research.FullTypedLogicalSeparation

#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.actual_c_sequent
#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.actual_c_theorem
#print axioms Classicism.Meta.Research.FullTypedLogicalSeparation.h_full_logical_separation_actual_c
