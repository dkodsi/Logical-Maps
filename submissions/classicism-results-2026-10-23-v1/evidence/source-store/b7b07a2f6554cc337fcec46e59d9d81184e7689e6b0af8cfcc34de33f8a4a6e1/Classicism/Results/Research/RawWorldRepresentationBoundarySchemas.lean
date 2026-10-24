import Classicism.Results.Research.RawWorldRepresentationBoundaryCertificates
import Classicism.Syntax.Inhabited

/-! Every relational type is its finite argument list followed by t. This file
assembles actual translated C derivations; it does not insert an object-level
quantifier over types or assume an unknown constant-relation embedding. -/
namespace Classicism.Meta.Research.RawWorldRepresentationBoundary
open AxiomSet

/- The same finite-tuple existence induction used in
`UniformHalfComprehensionClosed`: each closed coordinate is inhabited in C.
It is spelled out here to avoid importing the complete record-audit chain. -/
private theorem drop_forall_block {Sig : Signature} {Ax : AxiomSet Sig}
    (hE : Ax existence_e) : ∀ (σs : List Ty), Ty.AllClosed σs →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {φ : Formula Sig Γ},
      Derivable Ax Δ (Term.forallBlock σs (φ.rename (Ren.wkBlock σs))) →
      Derivable Ax Δ φ
  | [], _, _, _, φ, h => by
      simpa only [Term.forallBlock, Ren.wkBlock, Term.rename_id] using h
  | σ :: σs, hc, Γ, Δ, φ, h => by
      apply Derivable.of_forall_weaken hE σ hc.head
      apply Derivable.allI
      apply drop_forall_block hE σs hc.tail
      have hb := Derivable.allEBlock_vars [σ] (Derivable.rename (Ren.shift (σ := σ)) h)
      simpa only [Term.weaken, Term.rename_rename, Ren.wkBlock, Ctx.block,
        Hyps.weaken, Hyps.rename] using hb

private theorem tuple_existence (σs : List Ty) (hc : Ty.AllClosed σs) :
    C.Theorem (Classicism.P.Existence.listQuoted σs) := by
  change C.Theorem (Term.existsBlock σs
    (Term.eqBlock (Terms.vars σs []) (Terms.vars σs [])))
  apply drop_forall_block C.axioms.existence_e σs hc
  apply Derivable.allIBlock
  exact Derivable.exIBlock_vars σs (Derivable.reflBlock (Terms.vars σs []))

theorem no_raw_wr_all_relational : empty ⟹
    Classicism.Research.RawWorldRepresentationBoundary.NoRawWRRelational.schema := by
  rintro a ⟨ρ, hρ, rfl⟩
  have hd := Theorem.mp
    (Classicism.Research.RawWorldRepresentationBoundary.existence_implies_no_raw_wr_unary.listRule ρ.args)
    (tuple_existence ρ.args (RTy.closed_args hρ))
  exact Theorem.ofC (hd.cast
    (congrArg Classicism.Research.RawWorldRepresentationBoundary.NoRawWRRelational.quoted
      (RTy.ofArgs_args ρ)))

end Classicism.Meta.Research.RawWorldRepresentationBoundary

#print axioms Classicism.Meta.Research.RawWorldRepresentationBoundary.no_raw_wr_all_relational
