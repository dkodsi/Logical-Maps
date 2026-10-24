import Classicism.Semantics.Research.CentralProductChoice

open Classicism.Meta
open Classicism.Meta.Intensional.Central.Product

-- Exact concrete model certificate, without the pending LN gluing argument.
example (L : Type) (a : L) :
    (pureModel (Set Nat) L).IsModel ∧
    (∀ σ : Ty, (pureModel (Set Nat) L).HoldsSentence (Term.box (Sentence.bf σ))) ∧
    (∀ σ τ : Ty, (pureModel (Set Nat) L).HoldsSentence
      (Classicism.P.NecRelationalChoice.quoted σ τ)) ∧
    ¬ (pureModel (Set Nat) L).HoldsSentence Classicism.P.Actuality.quoted :=
  ⟨model_isModel (Set Nat) L _, fun σ => holds_box_bf (Set Nat) L _ σ,
    pure_holds_box_rc (Set Nat) L, not_holds_actuality L a⟩

#print axioms Classicism.Meta.Intensional.Central.Product.model_isModel
#print axioms Classicism.Meta.Intensional.Central.Product.holds_box_bf
#print axioms Classicism.Meta.Intensional.Central.Product.pure_holds_box_rc
#print axioms Classicism.Meta.Intensional.Central.Product.not_holds_actuality
