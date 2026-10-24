import Classicism.Results.Records.C5

/-!
# Relational real structures and their internal second-order clauses

Direct mathematical source: Zachary Goodsell and Claude Fable 5.1 (Anthropic),
23 October 2026, `writeups/c5-and-necessary-rigid-comprehension-imply-second-order-analytic-necessitism.md`,
"The rigidified structure" and "necessarily a real number structure", together
with `background.md`, "Analysis" (both unpaginated).

This transcription makes the complete-ordered-field convention explicit: the
bounded subproperty must be NONEMPTY. The Background's abbreviated wording omits
that word; the user confirmed this standard reading on 23 October 2026. Including
the empty subproperty would make the real-structure predicate inconsistent.

Every operation is a curried relation. The seven structure components are separate
object parameters: no record type or operation returning an individual is added
to C. Subproperty quantification is internal quantification at `σ → t`.
No external powerset, choice axiom, Atomicity, or categoricity is assumed.
-/

namespace Classicism.Research.Analytic

variable {σ : Type} [Ty σ]

def UpperBound (X : σ → Prop) (le : σ → σ → Prop) (F : σ → Prop) (b : σ) : Prop :=
  X b ∧ ∀ x, F x → le x b

def LeastUpperBound (X : σ → Prop) (le : σ → σ → Prop) (F : σ → Prop) (s : σ) : Prop :=
  UpperBound X le F s ∧ ∀ b, UpperBound X le F b → le s b

def CompleteClause (X : σ → Prop) (le : σ → σ → Prop) (F : σ → Prop) : Prop :=
  ((∀ x, F x → X x) ∧ (∃ x, F x) ∧ (∃ b, UpperBound X le F b)) →
    ∃ s, LeastUpperBound X le F s

def CompleteNonempty (X : σ → Prop) (le : σ → σ → Prop) : Prop :=
  ∀ F : σ → Prop, CompleteClause X le F

def Inductive (X : σ → Prop) (add : σ → σ → σ → Prop)
    (zero one : σ) (F : σ → Prop) : Prop :=
  (∀ x, F x → X x) ∧ F zero ∧ ∀ x y, F x → add x one y → F y

def LeastClause (X : σ → Prop) (add : σ → σ → σ → Prop)
    (zero one : σ) (N F : σ → Prop) : Prop :=
  Inductive X add zero one F → ∀ x, N x → F x

def LeastInductive (X : σ → Prop) (add : σ → σ → σ → Prop)
    (zero one : σ) (N : σ → Prop) : Prop :=
  Inductive X add zero one N ∧ ∀ F : σ → Prop, LeastClause X add zero one N F

/-- A total, functional binary operation on the indicated domain, given by its graph. -/
def BinaryOperation (X : σ → Prop) (op : σ → σ → σ → Prop) : Prop :=
  (∀ x y z, op x y z → X x ∧ X y ∧ X z) ∧
  (∀ x y, X x → X y → ∃ z, op x y z) ∧
  (∀ x y z w, op x y z → op x y w → z = w)

def LinearOrder (X : σ → Prop) (le : σ → σ → Prop) : Prop :=
  (∀ x y, le x y → X x ∧ X y) ∧
  (∀ x, X x → le x x) ∧
  (∀ x y, le x y → le y x → x = y) ∧
  (∀ x y z, le x y → le y z → le x z) ∧
  (∀ x y, X x → X y → le x y ∨ le y x)

def AdditiveLaws (X : σ → Prop) (add : σ → σ → σ → Prop) (zero : σ) : Prop :=
  (∀ x, X x → add x zero x) ∧
  (∀ x y z, add x y z → add y x z) ∧
  (∀ a b c u v w, add a b u → add u c v → add b c w → add a w v) ∧
  (∀ x, X x → ∃ y, add x y zero)

def MultiplicativeLaws (X : σ → Prop) (mul : σ → σ → σ → Prop)
    (zero one : σ) : Prop :=
  (∀ x, X x → mul x one x) ∧
  (∀ x y z, mul x y z → mul y x z) ∧
  (∀ a b c u v w, mul a b u → mul u c v → mul b c w → mul a w v) ∧
  (∀ x, X x → x ≠ zero → ∃ y, mul x y one)

def Distributive (add mul : σ → σ → σ → Prop) : Prop :=
  ∀ a b c s t u v, add b c s → mul a s t → mul a b u → mul a c v → add u v t

def OrderCompatible (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (zero : σ) : Prop :=
  (∀ a b c u v, le a b → X c → add a c u → add b c v → le u v) ∧
  (∀ a b c, le zero a → le zero b → mul a b c → le zero c)

/-- The ordinary ordered-field axioms, with total functional graphs on `X`. -/
def OrderedField (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (zero one : σ) : Prop :=
  X zero ∧ X one ∧ zero ≠ one ∧
  LinearOrder X le ∧ BinaryOperation X add ∧ BinaryOperation X mul ∧
  AdditiveLaws X add zero ∧ MultiplicativeLaws X mul zero one ∧
  Distributive add mul ∧ OrderCompatible X le add mul zero

def Real (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (zero one : σ) (N : σ → Prop) : Prop :=
  OrderedField X le add mul zero one ∧ CompleteNonempty X le ∧
    LeastInductive X add zero one N

def RigidStr (X : σ → Prop) (le : σ → σ → Prop)
    (add mul : σ → σ → σ → Prop) (N : σ → Prop) : Prop :=
  Rigid X ∧ Rigid le ∧ Rigid add ∧ Rigid mul ∧ Rigid N ∧
    ∀ x y, X x → X y → x ≠ y → □ (x ≠ y)

/-! Coextension is used by its two logical directions, never by propositional
extensionality on a hypothesis. These are local, nonmodal transport lemmas. -/

theorem upperBound_coext (X Y F G : σ → Prop) (le le' : σ → σ → Prop)
    (hX : ∀ x, X x ↔ Y x) (hF : ∀ x, F x ↔ G x)
    (hL : ∀ x y, le x y ↔ le' x y) (b : σ) :
    UpperBound X le F b ↔ UpperBound Y le' G b :=
  ⟨fun h => ⟨(hX b).1 h.1, fun x hx => (hL x b).1 (h.2 x ((hF x).2 hx))⟩,
   fun h => ⟨(hX b).2 h.1, fun x hx => (hL x b).2 (h.2 x ((hF x).1 hx))⟩⟩

theorem leastUpperBound_coext (X Y F G : σ → Prop) (le le' : σ → σ → Prop)
    (hX : ∀ x, X x ↔ Y x) (hF : ∀ x, F x ↔ G x)
    (hL : ∀ x y, le x y ↔ le' x y) (s : σ) :
    LeastUpperBound X le F s ↔ LeastUpperBound Y le' G s :=
  ⟨fun h => ⟨(upperBound_coext X Y F G le le' hX hF hL s).1 h.1,
    fun b hb => (hL s b).1 (h.2 b ((upperBound_coext X Y F G le le' hX hF hL b).2 hb))⟩,
   fun h => ⟨(upperBound_coext X Y F G le le' hX hF hL s).2 h.1,
    fun b hb => (hL s b).2 (h.2 b ((upperBound_coext X Y F G le le' hX hF hL b).1 hb))⟩⟩

theorem completeClause_transport (X Y F G : σ → Prop) (le le' : σ → σ → Prop)
    (hX : ∀ x, X x ↔ Y x) (hF : ∀ x, F x ↔ G x)
    (hL : ∀ x y, le x y ↔ le' x y) :
    CompleteClause X le F → CompleteClause Y le' G := by
  intro h hc
  obtain ⟨a, ha⟩ := hc.2.1
  obtain ⟨b, hb⟩ := hc.2.2
  obtain ⟨s, hs⟩ := h ⟨fun x hx => (hX x).2 (hc.1 x ((hF x).1 hx)),
    ⟨a, (hF a).2 ha⟩, b, (upperBound_coext X Y F G le le' hX hF hL b).2 hb⟩
  exact ⟨s, (leastUpperBound_coext X Y F G le le' hX hF hL s).1 hs⟩

theorem completeClause_coext (X Y F G : σ → Prop) (le le' : σ → σ → Prop)
    (hX : ∀ x, X x ↔ Y x) (hF : ∀ x, F x ↔ G x)
    (hL : ∀ x y, le x y ↔ le' x y) :
    CompleteClause X le F ↔ CompleteClause Y le' G :=
  ⟨completeClause_transport X Y F G le le' hX hF hL,
   completeClause_transport Y X G F le' le (fun x => (hX x).symm)
     (fun x => (hF x).symm) (fun x y => (hL x y).symm)⟩

theorem completeNonempty_coext (X Y : σ → Prop) (le le' : σ → σ → Prop)
    (hX : ∀ x, X x ↔ Y x) (hL : ∀ x y, le x y ↔ le' x y) :
    CompleteNonempty X le ↔ CompleteNonempty Y le' :=
  ⟨fun h F => completeClause_transport X Y F F le le' hX (fun _ => Iff.rfl) hL (h F),
   fun h F => completeClause_transport Y X F F le' le (fun x => (hX x).symm)
     (fun _ => Iff.rfl) (fun x y => (hL x y).symm) (h F)⟩

theorem inductive_coext (X Y F G : σ → Prop) (add add' : σ → σ → σ → Prop)
    (zero one : σ) (hX : ∀ x, X x ↔ Y x) (hF : ∀ x, F x ↔ G x)
    (hA : ∀ x y z, add x y z ↔ add' x y z) :
    Inductive X add zero one F ↔ Inductive Y add' zero one G :=
  ⟨fun h => ⟨fun x hx => (hX x).1 (h.1 x ((hF x).2 hx)), (hF zero).1 h.2.1,
     fun x y hx ha => (hF y).1 (h.2.2 x y ((hF x).2 hx) ((hA x one y).2 ha))⟩,
   fun h => ⟨fun x hx => (hX x).2 (h.1 x ((hF x).1 hx)), (hF zero).2 h.2.1,
     fun x y hx ha => (hF y).2 (h.2.2 x y ((hF x).1 hx) ((hA x one y).1 ha))⟩⟩

theorem leastClause_coext (X Y N M F G : σ → Prop) (add add' : σ → σ → σ → Prop)
    (zero one : σ) (hX : ∀ x, X x ↔ Y x) (hN : ∀ x, N x ↔ M x)
    (hF : ∀ x, F x ↔ G x) (hA : ∀ x y z, add x y z ↔ add' x y z) :
    LeastClause X add zero one N F ↔ LeastClause Y add' zero one M G :=
  ⟨fun h hi x hx => (hF x).1
     (h ((inductive_coext X Y F G add add' zero one hX hF hA).2 hi) x ((hN x).2 hx)),
   fun h hi x hx => (hF x).2
     (h ((inductive_coext X Y F G add add' zero one hX hF hA).1 hi) x ((hN x).1 hx))⟩

theorem leastInductive_coext (X Y N M : σ → Prop) (add add' : σ → σ → σ → Prop)
    (zero one : σ) (hX : ∀ x, X x ↔ Y x) (hN : ∀ x, N x ↔ M x)
    (hA : ∀ x y z, add x y z ↔ add' x y z) :
    LeastInductive X add zero one N ↔ LeastInductive Y add' zero one M :=
  ⟨fun h => ⟨(inductive_coext X Y N M add add' zero one hX hN hA).1 h.1,
      fun F => (leastClause_coext X Y N M F F add add' zero one hX hN
        (fun _ => Iff.rfl) hA).1 (h.2 F)⟩,
   fun h => ⟨(inductive_coext X Y N M add add' zero one hX hN hA).2 h.1,
      fun F => (leastClause_coext X Y N M F F add add' zero one hX hN
        (fun _ => Iff.rfl) hA).2 (h.2 F)⟩⟩

/-- The closed internal completeness predicate is invariant under its test's coextension. -/
theorem complete_clause_coext (X : σ → Prop) (le : σ → σ → Prop) :
    ∀ F G : σ → Prop, (∀ x, F x ↔ G x) →
      CompleteClause X le F → CompleteClause X le G :=
  fun F G hF => completeClause_transport X X F G le le (fun _ => Iff.rfl) hF
    (fun _ _ => Iff.rfl)

/-- The closed leastness predicate is invariant under its test's coextension. -/
theorem least_clause_coext (X : σ → Prop) (add : σ → σ → σ → Prop)
    (zero one : σ) (N : σ → Prop) :
    ∀ F G : σ → Prop, (∀ x, F x ↔ G x) →
      LeastClause X add zero one N F → LeastClause X add zero one N G :=
  fun F G hF => (leastClause_coext X X N N F G add add zero one
    (fun _ => Iff.rfl) (fun _ => Iff.rfl) hF (fun _ _ _ => Iff.rfl)).1

theorem binaryOperation_transport (X Y : σ → Prop) (op op' : σ → σ → σ → Prop)
    (hX : ∀ x, X x ↔ Y x) (hO : ∀ x y z, op x y z ↔ op' x y z) :
    BinaryOperation X op → BinaryOperation Y op' := by
  intro h
  refine ⟨?_, ?_, ?_⟩
  · intro x y z ho
    have ht := h.1 x y z ((hO x y z).2 ho)
    exact ⟨(hX x).1 ht.1, (hX y).1 ht.2.1, (hX z).1 ht.2.2⟩
  · intro x y hx hy
    obtain ⟨z, hz⟩ := h.2.1 x y ((hX x).2 hx) ((hX y).2 hy)
    exact ⟨z, (hO x y z).1 hz⟩
  · intro x y z w hz hw
    exact h.2.2 x y z w ((hO x y z).2 hz) ((hO x y w).2 hw)

theorem linearOrder_transport (X Y : σ → Prop) (le le' : σ → σ → Prop)
    (hX : ∀ x, X x ↔ Y x) (hL : ∀ x y, le x y ↔ le' x y) :
    LinearOrder X le → LinearOrder Y le' := by
  intro h
  rcases h with ⟨ht, hr, ha, hs, hc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hl
    exact ⟨(hX x).1 (ht x y ((hL x y).2 hl)).1,
      (hX y).1 (ht x y ((hL x y).2 hl)).2⟩
  · intro x hx
    exact (hL x x).1 (hr x ((hX x).2 hx))
  · intro x y hxy hyx
    exact ha x y ((hL x y).2 hxy) ((hL y x).2 hyx)
  · intro x y z hxy hyz
    exact (hL x z).1 (hs x y z ((hL x y).2 hxy) ((hL y z).2 hyz))
  · intro x y hx hy
    exact (hc x y ((hX x).2 hx) ((hX y).2 hy)).elim
      (fun h => Or.inl ((hL x y).1 h)) (fun h => Or.inr ((hL y x).1 h))

theorem additiveLaws_transport (X Y : σ → Prop) (add add' : σ → σ → σ → Prop)
    (zero : σ) (hX : ∀ x, X x ↔ Y x)
    (hA : ∀ x y z, add x y z ↔ add' x y z) :
    AdditiveLaws X add zero → AdditiveLaws Y add' zero := by
  intro h
  rcases h with ⟨hz, hc, ha, hi⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hA x zero x).1 (hz x ((hX x).2 hx))
  · intro x y z h
    exact (hA y x z).1 (hc x y z ((hA x y z).2 h))
  · intro a b c u v w hab huc hbc
    exact (hA a w v).1 (ha a b c u v w ((hA a b u).2 hab)
      ((hA u c v).2 huc) ((hA b c w).2 hbc))
  · intro x hx
    obtain ⟨y, hy⟩ := hi x ((hX x).2 hx)
    exact ⟨y, (hA x y zero).1 hy⟩

theorem multiplicativeLaws_transport (X Y : σ → Prop) (mul mul' : σ → σ → σ → Prop)
    (zero one : σ) (hX : ∀ x, X x ↔ Y x)
    (hM : ∀ x y z, mul x y z ↔ mul' x y z) :
    MultiplicativeLaws X mul zero one → MultiplicativeLaws Y mul' zero one := by
  intro h
  rcases h with ⟨hu, hc, ha, hi⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hM x one x).1 (hu x ((hX x).2 hx))
  · intro x y z h
    exact (hM y x z).1 (hc x y z ((hM x y z).2 h))
  · intro a b c u v w hab huc hbc
    exact (hM a w v).1 (ha a b c u v w ((hM a b u).2 hab)
      ((hM u c v).2 huc) ((hM b c w).2 hbc))
  · intro x hx hn
    obtain ⟨y, hy⟩ := hi x ((hX x).2 hx) hn
    exact ⟨y, (hM x y one).1 hy⟩

theorem distributive_transport (add add' mul mul' : σ → σ → σ → Prop)
    (hA : ∀ x y z, add x y z ↔ add' x y z)
    (hM : ∀ x y z, mul x y z ↔ mul' x y z) :
    Distributive add mul → Distributive add' mul' :=
  fun h a b c s t u v hs ht hu hv => (hA u v t).1
    (h a b c s t u v ((hA b c s).2 hs) ((hM a s t).2 ht)
      ((hM a b u).2 hu) ((hM a c v).2 hv))

theorem orderCompatible_transport (X Y : σ → Prop) (le le' : σ → σ → Prop)
    (add add' mul mul' : σ → σ → σ → Prop) (zero : σ)
    (hX : ∀ x, X x ↔ Y x) (hL : ∀ x y, le x y ↔ le' x y)
    (hA : ∀ x y z, add x y z ↔ add' x y z)
    (hM : ∀ x y z, mul x y z ↔ mul' x y z) :
    OrderCompatible X le add mul zero → OrderCompatible Y le' add' mul' zero :=
  fun h => ⟨fun a b c u v hl hc hu hv => (hL u v).1
    (h.1 a b c u v ((hL a b).2 hl) ((hX c).2 hc)
      ((hA a c u).2 hu) ((hA b c v).2 hv)),
    fun a b c ha hb hm => (hL zero c).1
      (h.2 a b c ((hL zero a).2 ha) ((hL zero b).2 hb) ((hM a b c).2 hm))⟩

theorem orderedField_transport (X Y : σ → Prop) (le le' : σ → σ → Prop)
    (add add' mul mul' : σ → σ → σ → Prop) (zero one : σ)
    (hX : ∀ x, X x ↔ Y x) (hL : ∀ x y, le x y ↔ le' x y)
    (hA : ∀ x y z, add x y z ↔ add' x y z)
    (hM : ∀ x y z, mul x y z ↔ mul' x y z) :
    OrderedField X le add mul zero one → OrderedField Y le' add' mul' zero one := by
  intro h
  rcases h with ⟨hz, ho, hn, hl, ha, hm, hg, hk, hd, hc⟩
  exact ⟨(hX zero).1 hz, (hX one).1 ho, hn,
    linearOrder_transport X Y le le' hX hL hl,
    binaryOperation_transport X Y add add' hX hA ha,
    binaryOperation_transport X Y mul mul' hX hM hm,
    additiveLaws_transport X Y add add' zero hX hA hg,
    multiplicativeLaws_transport X Y mul mul' zero one hX hM hk,
    distributive_transport add add' mul mul' hA hM hd,
    orderCompatible_transport X Y le le' add add' mul mul' zero hX hL hA hM hc⟩

theorem real_transport (X Y N M : σ → Prop) (le le' : σ → σ → Prop)
    (add add' mul mul' : σ → σ → σ → Prop) (zero one : σ)
    (hX : ∀ x, X x ↔ Y x) (hL : ∀ x y, le x y ↔ le' x y)
    (hA : ∀ x y z, add x y z ↔ add' x y z)
    (hM : ∀ x y z, mul x y z ↔ mul' x y z) (hN : ∀ x, N x ↔ M x) :
    Real X le add mul zero one N → Real Y le' add' mul' zero one M :=
  fun h => ⟨orderedField_transport X Y le le' add add' mul mul' zero one hX hL hA hM h.1,
    (completeNonempty_coext X Y le le' hX hL).1 h.2.1,
    (leastInductive_coext X Y N M add add' zero one hX hN hA).1 h.2.2⟩

theorem real_coext (X Y N M : σ → Prop) (le le' : σ → σ → Prop)
    (add add' mul mul' : σ → σ → σ → Prop) (zero one : σ)
    (hX : ∀ x, X x ↔ Y x) (hL : ∀ x y, le x y ↔ le' x y)
    (hA : ∀ x y z, add x y z ↔ add' x y z)
    (hM : ∀ x y z, mul x y z ↔ mul' x y z) (hN : ∀ x, N x ↔ M x) :
    Real X le add mul zero one N ↔ Real Y le' add' mul' zero one M :=
  ⟨real_transport X Y N M le le' add add' mul mul' zero one hX hL hA hM hN,
   real_transport Y X M N le' le add' add mul' mul zero one
     (fun x => (hX x).symm) (fun x y => (hL x y).symm)
     (fun x y z => (hA x y z).symm) (fun x y z => (hM x y z).symm)
     (fun x => (hN x).symm)⟩

end Classicism.Research.Analytic
