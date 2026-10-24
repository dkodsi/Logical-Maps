import Classicism.Results.Research.UniformHalfComprehensionCertificates
import Classicism.Syntax.Inhabited

/-!
# Discharging tuple existence in the C certificates

Only closed object types occur in the paper. The induction below supplies a tuple
at any finite list of such types, using C's Existence axiom precisely at `e`.
This is metatheory about genuine derivations, not a new object-language premise.
-/

namespace Classicism.Meta.Research

theorem drop_forallBlock {Sig : Signature} {Ax : AxiomSet Sig}
    (hE : Ax existence_e) : ∀ (σs : List Ty), Ty.AllClosed σs →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {φ : Formula Sig Γ},
    Derivable Ax Δ (Term.forallBlock σs (φ.rename (Ren.wkBlock σs))) →
    Derivable Ax Δ φ
  | [], _, _, _, φ, h => by
      simpa only [Term.forallBlock, Ren.wkBlock, Term.rename_id] using h
  | σ :: σs, hc, Γ, Δ, φ, h => by
      apply Derivable.of_forall_weaken hE σ hc.head
      apply Derivable.allI
      apply drop_forallBlock hE σs hc.tail
      have hb := Derivable.allEBlock_vars [σ] (Derivable.rename (Ren.shift (σ := σ)) h)
      simpa only [Term.weaken, Term.rename_rename, Ren.wkBlock, Ctx.block,
        Hyps.weaken, Hyps.rename] using hb

theorem tuple_existence (σs : List Ty) (hc : Ty.AllClosed σs) :
    C.Theorem (Classicism.P.Existence.listQuoted σs) := by
  change C.Theorem (Term.existsBlock σs
    (Term.eqBlock (Terms.vars σs []) (Terms.vars σs [])))
  apply drop_forallBlock C.axioms.existence_e σs hc
  apply Derivable.allIBlock
  exact Derivable.exIBlock_vars σs (Derivable.reflBlock (Terms.vars σs []))

theorem uniformPersistent_actuality (σs : List Ty) (hc : Ty.AllClosed σs) :
    C.Theorem (Term.imp
      (Classicism.Research.UniformPersistent.quoted (σs ⇒* RTy.t))
      Classicism.P.Actuality.quoted) :=
  Theorem.mp (Classicism.Research.uniformPersistent_actuality.listRule σs)
    (tuple_existence σs hc)

theorem uniformWeakPersistent_actuality (σs : List Ty) (hc : Ty.AllClosed σs) :
    C.Theorem (Term.imp
      (Classicism.Research.UniformWeakPersistent.quoted (σs ⇒* RTy.t))
      Classicism.P.Actuality.quoted) :=
  Theorem.mp (Classicism.Research.uniformWeakPersistent_actuality.listRule σs)
    (tuple_existence σs hc)

theorem uniformWeakInextensible_actuality (σs : List Ty) (hc : Ty.AllClosed σs) :
    C.Theorem (Term.imp
      (Classicism.Research.UniformWeakInextensible.quoted (σs ⇒* RTy.t))
      Classicism.P.Actuality.quoted) :=
  Theorem.mp (Classicism.Research.uniformWeakInextensible_actuality.listRule σs)
    (tuple_existence σs hc)

theorem uniformInextensible_actuality (σs : List Ty) (hc : Ty.AllClosed σs) :
    C.Theorem (Term.imp
      (Classicism.Research.UniformInextensible.quoted (σs ⇒* RTy.t))
      Classicism.P.Actuality.quoted) :=
  Theorem.mp (Classicism.Research.uniformInextensible_actuality.listRule σs)
    (tuple_existence σs hc)

end Classicism.Meta.Research

#print axioms Classicism.Meta.Research.tuple_existence
#print axioms Classicism.Meta.Research.uniformPersistent_actuality
#print axioms Classicism.Meta.Research.uniformWeakPersistent_actuality
#print axioms Classicism.Meta.Research.uniformWeakInextensible_actuality
#print axioms Classicism.Meta.Research.uniformInextensible_actuality
