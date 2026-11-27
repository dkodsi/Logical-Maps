import Classicism.StrongPossibility.ProxyVarExistence
import Classicism.StrongPossibility.ProxySeparation
import Classicism.Coalesced.Complete

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Coalesced Completeness Term

noncomputable section
variable {Sig : Signature}

/-- Untyped model transfer used by the canonical descriptor argument. No closed-type
restriction is imposed on the marked term's *internal* syntax. -/
def Predecessors (Sig : Signature) : Prop :=
  ∀ {C : Type} [SmallCategory C] (O : Premodel Sig C), O.IsModel →
    O.HoldsAx AxiomSet.varExistence → Nonempty (O.Dom O.W₀ .e) →
    ∀ f : Term Sig [] Tester, ¬O.HoldsSentence (.app f d) →
      ∃ (D : Type) (_ : SmallCategory D) (B : Premodel Sig D),
        B.IsModel ∧ B.HoldsAx AxiomSet.varExistence ∧ ¬B.HoldsSentence (eq' (.app Q f) d)

variable [Countable Sig.Const]

theorem canonical_vars (w : World Sig) : (canonicalFamily Sig w).HoldsAx AxiomSet.varExistence := by
  intro a ha
  obtain ⟨i,rfl⟩ := ha
  exact (Canonical.holdsSentence_iff w _).2 (w.exists_self_mem (.var i))

/-- Canonicalize any sentence of the *full* Lean signature whenever the input model
contains witnesses at each schematic type variable. -/
theorem canonical_refutation {C : Type} [SmallCategory C] (B : Premodel Sig C) (M : B.IsModel)
    (hv : B.HoldsAx AxiomSet.varExistence) (p : Sentence Sig) (hp : ¬B.HoldsSentence p) :
    ∃ w : World Sig, ¬ (canonicalFamily Sig w).HoldsSentence p := by
  have hneg := (B.holdsSentence_neg M p).2 hp
  have hc := AxiomSet.Consistent.of_model B M (B.holdsAx_union (B.holdsAx_single hneg) hv)
  obtain ⟨w, hw⟩ := exists_world_of_varExistence hc
  refine ⟨w, ((canonicalFamily Sig w).holdsSentence_neg (Canonical.isModel w) p).1 ?_⟩
  exact (Canonical.holdsSentence_iff w _).2 (hw _ ⟨neg p, rfl, rfl⟩)

/-- A universal canonical identity Qf=d forces the truth of f(d) at ALL addresses of
every canonical base point. -/
theorem canonical_diag (build : Predecessors Sig) (f : Term Sig [] Tester)
    (pos : ∀ w : World Sig, (canonicalFamily Sig w).HoldsSentence (eq' (.app Q f) d)) :
    ∀ w : World Sig, (canonicalFamily Sig w).HoldsSentence (box (.app f d)) := by
  intro w
  let O := canonicalFamily Sig w
  have M : O.IsModel := Canonical.isModel w
  apply (O.box_iff_truncate M (.app f d)).mpr
  intro V h
  by_contra hfalse
  let O' := O.truncate h
  obtain ⟨D,instD,B,MB,hvars,hfail⟩ :=
    build O' (O.isModel_truncate h M) (O.holdsAx_varExistence_truncate M (canonical_vars w) h)
      (Canonical.nonempty_dom_e V) f hfalse
  obtain ⟨v,hv⟩ := canonical_refutation B MB hvars _ hfail
  exact hv (pos v)

end
end Classicism.Meta.ProxyDiagonal
