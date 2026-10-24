import Classicism.Results.Research.ModalConcreteToCDerivation
import Classicism.Results.Research.ModalComprehensionClassicalExtension

/-!
# Translation of the explicit classical and existence extension into C

The two extra global axiom schemas, double-negation elimination in the
implication/falsity basis and type-e existence, are actually proved in C.
Thus `classical_derives_toC` has no target axiom-preservation premise.
This is still one direction; it does not claim a reverse translation of
arbitrary C lambda terms or C's contextual Subst rule.
-/

namespace Classicism.Research.ModalConcreteToC
open Classicism.Meta

variable {Const : Ty → Type}

def falsityC {Γ} : Formula (signature Const) Γ := Term.forall' (.var .zero)

theorem c_falsity_elim {Γ Δ} {q : Formula (signature Const) Γ}
    (h : C.Derivable Δ falsityC) : C.Derivable Δ q :=
  Classicism.Meta.Derivable.allEβ h q

theorem c_defined_dne {Γ} (p : Formula (signature Const) Γ) :
    C.Derivable [] (Term.imp (Term.imp (Term.imp p falsityC) falsityC) p) := by
  apply Classicism.Meta.Derivable.impI
  apply Classicism.Meta.Derivable.orE (Classicism.Meta.Derivable.em p)
  · exact Classicism.Meta.Derivable.hyp₀
  · apply c_falsity_elim
    have hnn : C.Derivable
        [Term.neg p, Term.imp (Term.imp p falsityC) falsityC]
        (Term.imp (Term.imp p falsityC) falsityC) :=
      Classicism.Meta.Derivable.hyp (by simp)
    apply Classicism.Meta.Derivable.impE hnn
    apply Classicism.Meta.Derivable.impI
    have hnp : C.Derivable
        [p, Term.neg p, Term.imp (Term.imp p falsityC) falsityC]
        (Term.neg p) := Classicism.Meta.Derivable.hyp (by simp)
    exact Classicism.Meta.Derivable.notE Classicism.Meta.Derivable.hyp₀ hnp

/-- The actual two explicit source axiom schemas have C derivations. -/
theorem classical_axioms_toC {Γ p}
    (h : ModalComprehensionConcreteSyntax.ClassicalAxioms Const Γ p) :
    C.Derivable [] (toC p) := by
  cases h with
  | dne p => exact c_defined_dne (toC p)
  | exists_e =>
      change C.Derivable [] (Classicism.Meta.existence_e (Sig := signature Const)).close
      exact Classicism.Meta.Derivable.ax rfl

/-- Every derivation of the full displayed classical lambda-free base,
including all its modal/equality/quantifier and strong-SC rules, translates
to the existing C calculus. Local premises remain local. -/
theorem classical_derives_toC {Γ Δ p}
    (h : SourceProof Const (ModalComprehensionConcreteSyntax.ClassicalAxioms Const)
      Γ Δ p) : C.Derivable (Δ.map toC) (toC p) :=
  derives_toC (fun _ _ h => classical_axioms_toC h) h

#print axioms classical_axioms_toC
#print axioms classical_derives_toC

end Classicism.Research.ModalConcreteToC
