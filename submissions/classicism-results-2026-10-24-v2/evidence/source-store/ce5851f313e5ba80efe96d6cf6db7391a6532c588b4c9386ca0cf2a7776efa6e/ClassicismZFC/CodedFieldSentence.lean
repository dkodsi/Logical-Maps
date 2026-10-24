import ClassicismZFC.BooleanNaturals
import ClassicismZFC.RealFieldLaws
import ClassicismZFC.LeastInductive
import ClassicismZFC.CHFieldTransport

/-!
# One finite sentence preserving all real-cardinal witnesses

Original source, misc, 23 October 2026. The field, its least inductive subset,
its actual omega bijection, and injections in both directions between the
field and the power set of omega are retained TOGETHER before ordinary model
extraction. This prevents changing the field between existential witnesses.
The Boolean and ordinary interpretation theorems below compute the actual
finite syntax. No cardinal correspondence is an assumed model-interface field.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open scoped FirstOrder Fol Flypitch

namespace ClassicismZFC.CodedFieldSentence


def functionalF (G : Tm) : Fm :=
  allF fun a => allF fun b => allF fun c => allF fun d =>
    impF (andF (memF (pairT (varT a) (varT c)) G)
      (memF (pairT (varT b) (varT d)) G))
      (impF (eqF (varT a) (varT b)) (eqF (varT c) (varT d)))

def totalF (A B G : Tm) : Fm :=
  allF fun a => impF (memF (varT a) A) (exF fun b =>
    andF (memF (varT b) B) (memF (pairT (varT a) (varT b)) G))

def injectiveF (G : Tm) : Fm :=
  allF fun a => allF fun b => allF fun c => allF fun d =>
    impF (andF (andF (memF (pairT (varT a) (varT c)) G)
      (memF (pairT (varT b) (varT d)) G))
      (eqF (varT c) (varT d))) (eqF (varT a) (varT b))

def injectsF (A B : Tm) : Fm := exF fun G =>
  andF (andF (functionalF (varT G)) (totalF A B (varT G)))
    (injectiveF (varT G))

def supportF (A B G : Tm) : Fm :=
  allF fun x => allF fun y => impF (memF (pairT (varT x) (varT y)) G)
    (andF (memF (varT x) A) (memF (varT y) B))

def surjectiveF (A B G : Tm) : Fm :=
  allF fun y => impF (memF (varT y) B) (exF fun x =>
    andF (memF (varT x) A) (memF (pairT (varT x) (varT y)) G))

def bijectionF (A B G : Tm) : Fm :=
  andF (supportF A B G) (andF (functionalF G)
    (andF (totalF A B G) (andF (injectiveF G) (surjectiveF A B G))))

def inductiveF (R zero one Plus A : Tm) : Fm :=
  andF (allF fun x => impF (memF (varT x) A) (memF (varT x) R))
    (andF (memF zero A) (allF fun x => allF fun y =>
      impF (memF (varT x) R) (impF (memF (varT y) R)
        (impF (memF (varT x) A) (impF (app2F Plus (varT x) one (varT y))
          (memF (varT y) A))))))

def leastF (R zero one Plus N : Tm) : Fm :=
  andF (inductiveF R zero one Plus N) (allF fun A =>
    impF (inductiveF R zero one Plus (varT A))
      (allF fun x => impF (memF (varT x) N) (memF (varT x) (varT A))))

def packageF (R Plus Times Lt zero one N G : Tm) : Fm :=
  andF (completeOrderedFieldF R Plus Times Lt zero one)
    (andF (leastF R zero one Plus N) (andF (bijectionF omT N G)
      (andF (injectsF R (powT omT)) (injectsF (powT omT) R))))

def ExistsPackage : L.Sentence := toSentence <|
  exF fun R => exF fun Plus => exF fun Times => exF fun Lt =>
  exF fun zero => exF fun one => exF fun N => exF fun G =>
    packageF (varT R) (varT Plus) (varT Times) (varT Lt)
      (varT zero) (varT one) (varT N) (varT G)

/- The identical templates in Flypitch's syntax, used only for literal translation. -/
namespace BooleanSyntax

def functionalF (G : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.allF fun a => Flypitch.Erdos501.allF fun b => Flypitch.Erdos501.allF fun c => Flypitch.Erdos501.allF fun d =>
    Flypitch.Erdos501.impF (Flypitch.Erdos501.andF (Flypitch.Erdos501.memF (Flypitch.Erdos501.pairT (Flypitch.Erdos501.varT a) (Flypitch.Erdos501.varT c)) G)
      (Flypitch.Erdos501.memF (Flypitch.Erdos501.pairT (Flypitch.Erdos501.varT b) (Flypitch.Erdos501.varT d)) G))
      (Flypitch.Erdos501.impF (Flypitch.Erdos501.eqF (Flypitch.Erdos501.varT a) (Flypitch.Erdos501.varT b)) (Flypitch.Erdos501.eqF (Flypitch.Erdos501.varT c) (Flypitch.Erdos501.varT d)))

def totalF (A B G : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.allF fun a => Flypitch.Erdos501.impF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT a) A) (Flypitch.Erdos501.exF fun b =>
    Flypitch.Erdos501.andF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT b) B) (Flypitch.Erdos501.memF (Flypitch.Erdos501.pairT (Flypitch.Erdos501.varT a) (Flypitch.Erdos501.varT b)) G))

def injectiveF (G : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.allF fun a => Flypitch.Erdos501.allF fun b => Flypitch.Erdos501.allF fun c => Flypitch.Erdos501.allF fun d =>
    Flypitch.Erdos501.impF (Flypitch.Erdos501.andF (Flypitch.Erdos501.andF (Flypitch.Erdos501.memF (Flypitch.Erdos501.pairT (Flypitch.Erdos501.varT a) (Flypitch.Erdos501.varT c)) G)
      (Flypitch.Erdos501.memF (Flypitch.Erdos501.pairT (Flypitch.Erdos501.varT b) (Flypitch.Erdos501.varT d)) G))
      (Flypitch.Erdos501.eqF (Flypitch.Erdos501.varT c) (Flypitch.Erdos501.varT d))) (Flypitch.Erdos501.eqF (Flypitch.Erdos501.varT a) (Flypitch.Erdos501.varT b))

def injectsF (A B : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm := Flypitch.Erdos501.exF fun G =>
  Flypitch.Erdos501.andF (Flypitch.Erdos501.andF (functionalF (Flypitch.Erdos501.varT G)) (totalF A B (Flypitch.Erdos501.varT G)))
    (injectiveF (Flypitch.Erdos501.varT G))

def supportF (A B G : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.allF fun x => Flypitch.Erdos501.allF fun y => Flypitch.Erdos501.impF (Flypitch.Erdos501.memF (Flypitch.Erdos501.pairT (Flypitch.Erdos501.varT x) (Flypitch.Erdos501.varT y)) G)
    (Flypitch.Erdos501.andF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT x) A) (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT y) B))

def surjectiveF (A B G : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.allF fun y => Flypitch.Erdos501.impF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT y) B) (Flypitch.Erdos501.exF fun x =>
    Flypitch.Erdos501.andF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT x) A) (Flypitch.Erdos501.memF (Flypitch.Erdos501.pairT (Flypitch.Erdos501.varT x) (Flypitch.Erdos501.varT y)) G))

def bijectionF (A B G : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.andF (supportF A B G) (Flypitch.Erdos501.andF (functionalF G)
    (Flypitch.Erdos501.andF (totalF A B G) (Flypitch.Erdos501.andF (injectiveF G) (surjectiveF A B G))))

def inductiveF (R zero one Plus A : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.andF (Flypitch.Erdos501.allF fun x => Flypitch.Erdos501.impF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT x) A) (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT x) R))
    (Flypitch.Erdos501.andF (Flypitch.Erdos501.memF zero A) (Flypitch.Erdos501.allF fun x => Flypitch.Erdos501.allF fun y =>
      Flypitch.Erdos501.impF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT x) R) (Flypitch.Erdos501.impF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT y) R)
        (Flypitch.Erdos501.impF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT x) A) (Flypitch.Erdos501.impF (Flypitch.Erdos501.app2F Plus (Flypitch.Erdos501.varT x) one (Flypitch.Erdos501.varT y))
          (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT y) A))))))

def leastF (R zero one Plus N : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.andF (inductiveF R zero one Plus N) (Flypitch.Erdos501.allF fun A =>
    Flypitch.Erdos501.impF (inductiveF R zero one Plus (Flypitch.Erdos501.varT A))
      (Flypitch.Erdos501.allF fun x => Flypitch.Erdos501.impF (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT x) N) (Flypitch.Erdos501.memF (Flypitch.Erdos501.varT x) (Flypitch.Erdos501.varT A))))

def packageF (R Plus Times Lt zero one N G : Flypitch.Erdos501.Tm) : Flypitch.Erdos501.Fm :=
  Flypitch.Erdos501.andF (Flypitch.Erdos501.CompleteOrderedFieldF R Plus Times Lt zero one)
    (Flypitch.Erdos501.andF (leastF R zero one Plus N) (Flypitch.Erdos501.andF (bijectionF Flypitch.Erdos501.omT N G)
      (Flypitch.Erdos501.andF (injectsF R (Flypitch.Erdos501.powT Flypitch.Erdos501.omT)) (injectsF (Flypitch.Erdos501.powT Flypitch.Erdos501.omT) R))))

def ExistsPackage : Fol.sentence L_ZFC := Flypitch.Erdos501.toSentence <|
  Flypitch.Erdos501.exF fun R => Flypitch.Erdos501.exF fun Plus => Flypitch.Erdos501.exF fun Times => Flypitch.Erdos501.exF fun Lt =>
  Flypitch.Erdos501.exF fun zero => Flypitch.Erdos501.exF fun one => Flypitch.Erdos501.exF fun N => Flypitch.Erdos501.exF fun G =>
    packageF (Flypitch.Erdos501.varT R) (Flypitch.Erdos501.varT Plus) (Flypitch.Erdos501.varT Times) (Flypitch.Erdos501.varT Lt)
      (Flypitch.Erdos501.varT zero) (Flypitch.Erdos501.varT one) (Flypitch.Erdos501.varT N) (Flypitch.Erdos501.varT G)

end BooleanSyntax

set_option maxRecDepth 4096 in
theorem tr_ExistsPackage : tr ExistsPackage = BooleanSyntax.ExistsPackage := rfl

def Positive : L.Sentence := ExistsPackage ⊓ CHTranslation.CH

def Negative : L.Sentence := ExistsPackage ⊓ CHTranslation.CH.not

section Ordinary

open SetLaws CHCardinality
universe u
variable {M : Type u} [L.Structure M]

def RawBijection (A B G : M) : Prop :=
  (∀ x y, Edge G x y → memM x A ∧ memM y B) ∧
  ((∀ a b c d, Edge G a c ∧ Edge G b d → a = b → c = d) ∧
  ((∀ a, memM a A → ∃ b, memM b B ∧ Edge G a b) ∧
  ((∀ a b c d, (Edge G a c ∧ Edge G b d) ∧ c = d → a = b) ∧
    (∀ y, memM y B → ∃ x, memM x A ∧ Edge G x y))))

theorem rawBijection_bijection {A B G : M} (h : RawBijection A B G) :
    CHCardinality.Bijection A B G := by
  refine ⟨⟨h.1, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, _, hy⟩ := h.2.2.1 x hx
    exact ⟨y, hy⟩
  · intro x y z hxy hxz
    exact h.2.1 x x y z ⟨hxy, hxz⟩ rfl
  · intro x y z hxz hyz
    exact h.2.2.2.1 x y z z ⟨⟨hxz, hyz⟩, rfl⟩
  · intro y hy
    obtain ⟨x, _, hx⟩ := h.2.2.2.2 y hy
    exact ⟨x, hx⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Semantic unpacking at the actual eight existential field and graph codes. -/
theorem realize_ExistsPackage_raw :
    (M ⊨ ExistsPackage) ↔
      ∃ R Plus Times Lt zero one N G : M,
        RealFieldSentence.IsField R Plus Times Lt zero one ∧
        LeastInductive.LeastInductive R zero one Plus N ∧
        RawBijection omegaM N G ∧
        (∃ J, CHFieldTransport.RawInjection R (powerM omegaM) J) ∧
        (∃ K, CHFieldTransport.RawInjection (powerM omegaM) R K) := by
  simp [ExistsPackage, packageF, leastF, inductiveF, bijectionF, supportF,
    functionalF, totalF, injectiveF, surjectiveF, injectsF,
    RealFieldSentence.IsField, RealFieldSentence.fieldBody,
    LeastInductive.LeastInductive, LeastInductive.IsInductive,
    RawBijection, CHFieldTransport.RawInjection, Edge,
    completeOrderedFieldF, andsF, isOp2F, allIn, exIn,
    toSentence, allF, exF, andF, orF, impF, notF, app2F, ltF, leF,
    memF, eqF, varT, Sentence.Realize, Formula.Realize,
    memM, pairM, powerM, omegaM, emptyM, Fin.snoc]

theorem field_cardinal_witnesses (hZFC : M ⊨ Erdos501.FOL.ZFC)
    (h : M ⊨ ExistsPackage) :
    ∃ R Plus Times Lt zero one N G : M,
      RealFieldSentence.IsField R Plus Times Lt zero one ∧
      LeastInductive.LeastInductive R zero one Plus N ∧
      CHCardinality.Bijection omegaM N G ∧
      Injects R (powerM omegaM) ∧ Injects (powerM omegaM) R := by
  obtain ⟨R, Plus, Times, Lt, zero, one, N, G, hF, hN, hG, ⟨J, hJ⟩, ⟨K, hK⟩⟩ :=
    realize_ExistsPackage_raw.mp h
  exact ⟨R, Plus, Times, Lt, zero, one, N, G, hF, hN,
    rawBijection_bijection hG, CHFieldTransport.normalize_raw hZFC hJ,
    CHFieldTransport.normalize_raw hZFC hK⟩

end Ordinary

section Boolean

open Fol bSet Flypitch.Erdos501
variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The Boolean value of the actual translated finite package. -/
theorem boolean_realize_ExistsPackage :
    ⟦tr ExistsPackage⟧[V β] =
      ⨆ R : bSet β, ⨆ Plus : bSet β, ⨆ Times : bSet β, ⨆ Lt : bSet β,
      ⨆ zero : bSet β, ⨆ one : bSet β, ⨆ N : bSet β, ⨆ G : bSet β,
        Sem.completeOrderedField R Plus Times Lt zero one ⊓
        (BooleanNaturals.LeastInductive (Fld.mk R Plus Times Lt zero one) N ⊓
        (BooleanNaturals.Bijection omega N G ⊓
        (injects_into R (bv_powerset omega) ⊓ injects_into (bv_powerset omega) R))) := by
  rw [tr_ExistsPackage]
  simp only [BooleanSyntax.ExistsPackage, BooleanSyntax.packageF,
    BooleanSyntax.leastF, BooleanSyntax.inductiveF, BooleanSyntax.bijectionF,
    BooleanSyntax.supportF, BooleanSyntax.functionalF, BooleanSyntax.totalF,
    BooleanSyntax.injectiveF, BooleanSyntax.surjectiveF, BooleanSyntax.injectsF,
    Flypitch.Erdos501.toSentence, Flypitch.Erdos501.allF, Flypitch.Erdos501.exF,
    Flypitch.Erdos501.allIn, Flypitch.Erdos501.exIn, Flypitch.Erdos501.andF,
    Flypitch.Erdos501.orF, Flypitch.Erdos501.impF, Flypitch.Erdos501.iffF,
    Flypitch.Erdos501.notF, Flypitch.Erdos501.memF, Flypitch.Erdos501.eqF,
    Flypitch.Erdos501.varT, Flypitch.Erdos501.omT, Flypitch.Erdos501.powT,
    Flypitch.Erdos501.pairT, Flypitch.Erdos501.empT, Flypitch.Erdos501.ltF,
    Flypitch.Erdos501.leF, Flypitch.Erdos501.appF, Flypitch.Erdos501.app2F,
    Flypitch.Erdos501.isOp2F, Flypitch.Erdos501.andsF, CompleteOrderedFieldF,
    boolean_realize_sentence, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_or,
    boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair', boolean_realize_bounded_term_Powerset',
    boolean_realize_bounded_term_emptyset', boolean_realize_bounded_term_omega',
    boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [Sem.completeOrderedField, Sem.isOp2, Sem.assoc, Sem.comm,
    Sem.ident, Sem.addInv, Sem.mulInv, Sem.distrib, Sem.irrefl, Sem.trans,
    Sem.total, Sem.addCompat, Sem.mulPos, Sem.complete, Sem.lt, Sem.le, Sem.app2,
    BooleanNaturals.LeastInductive, BooleanNaturals.Inductive,
    BooleanNaturals.Bijection, BooleanNaturals.Supported, is_func, is_total,
    is_inj, is_surj, injects_into, is_func']
  rfl

/-- All quantified witnesses are the actual objects constructed in one universe. -/
theorem forced_package_of_field_and_cardinal_maps (F : Fld β)
    (hF : (⊤ : β) ≤ F.COF)
    (hRP : (⊤ : β) ≤ injects_into F.R (bv_powerset omega))
    (hPR : (⊤ : β) ≤ injects_into (bv_powerset omega) F.R) :
    ⊤ ⊩[V β] tr ExistsPackage := by
  change (⊤ : β) ≤ ⟦tr ExistsPackage⟧[V β]
  rw [boolean_realize_ExistsPackage]
  apply le_iSup_of_le F.R
  apply le_iSup_of_le F.plus
  apply le_iSup_of_le F.times
  apply le_iSup_of_le F.ltR
  apply le_iSup_of_le F.zero
  apply le_iSup_of_le F.one
  apply le_iSup_of_le (BooleanNaturals.naturals F)
  apply le_iSup_of_le (BooleanNaturals.numeralGraph F)
  exact le_inf hF (le_inf (BooleanNaturals.naturals_leastInductive F hF)
    (le_inf (BooleanNaturals.numeralGraph_bijection F hF) (le_inf hRP hPR)))

end Boolean

#print axioms field_cardinal_witnesses
#print axioms forced_package_of_field_and_cardinal_maps

end ClassicismZFC.CodedFieldSentence
