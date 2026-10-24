import Classicism.Results.Research.MaxAtomicityRegularOpenCode
import Classicism.Results.Research.MaxAtomicityJechShelahIndexedGenerators

/-!
# Finite membership syntax for the indexed Jech--Shelah construction

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 749--750,
definitions (1)--(6), and the regular-lower-set construction in
`MaxAtomicityRegularOpenCode`. The formulas and coding organization here are
original formalization work (misc, 23 October 2026).

All syntax below is the existing finite `SetFormula` datatype. The small binder
combinators only insert its ordinary quantifiers and lift the existing variables.
The construction uses subsets of the canonical natural-number node index, so
it requires no particular encoding of finite lists. Arithmetic, growth, and
ancestry are specified by finite recursion laws on the coded natural numbers.

`JSCode` has exactly the free variables (algebra carrier, omega, generator
graph), in that order. Its syntactic definition is not a theorem asserting
that a particular hereditary universe satisfies it. The separate satisfaction
and representation obligations are stated honestly below; there is no axiom
asserting definability, existence, rigidity, or the final C inconsistency.
The designated serial checker owns compilation and axiom inspection.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahSyntax

open MaxAtomicitySetSyntax MaxAtomicitySetSemantics MaxAtomicitySetFormulaTools

/-- A binder with the fresh variable and the old-variable inclusion explicit. -/
def qAll {n : ℕ}
    (p : Fin (n + 1) → (Fin n → Fin (n + 1)) → SetFormula (n + 1)) :
    SetFormula n := .all (p 0 Fin.succ)

def qEx {n : ℕ}
    (p : Fin (n + 1) → (Fin n → Fin (n + 1)) → SetFormula (n + 1)) :
    SetFormula n := .ex (p 0 Fin.succ)

def allIn {n : ℕ} (a : Fin n)
    (p : Fin (n + 1) → (Fin n → Fin (n + 1)) → SetFormula (n + 1)) :
    SetFormula n := qAll fun x s => .imp (.mem x (s a)) (p x s)

def exIn {n : ℕ} (a : Fin n)
    (p : Fin (n + 1) → (Fin n → Fin (n + 1)) → SetFormula (n + 1)) :
    SetFormula n := qEx fun x s => .conj (.mem x (s a)) (p x s)

def leNat {n : ℕ} (a b : Fin n) : SetFormula n := .disj (.eq a b) (.mem a b)

def successor {n : ℕ} (a b : Fin n) : SetFormula n :=
  qAll fun x s => .iff (.mem x (s b)) (.disj (.mem x (s a)) (.eq x (s a)))

def inductiveSet {n : ℕ} (w : Fin n) : SetFormula n :=
  .conj (exIn w fun z _ => empty z)
    (allIn w fun x s => exIn (s w) fun y t => successor (t x) y)

/-- Least inductive set; its adequacy requires the actual omega witness in
the chosen transitive membership universe, not an internal induction shortcut. -/
def omega {n : ℕ} (w : Fin n) : SetFormula n :=
  .conj (inductiveSet w)
    (qAll fun I s => .imp (inductiveSet I) (subset (s w) I))

def graphApp₂ {n : ℕ} (f x y z : Fin n) : SetFormula n :=
  qEx fun xy s => .conj (orderedPair (s x) (s y) xy)
    (graphApp (s f) xy (s z))

/-- Unary function graph with exactly the specified domain and range in w. -/
def unaryOn {n : ℕ} (w f : Fin n) : SetFormula n :=
  .conj (functionGraph f) (.conj (graphDomain f w)
    (allIn w fun x s => exIn (s w) fun y t => graphApp (t (s f)) (t x) y))

/-- A binary graph has only triples of naturals, is right-unique on the
paired input, and is total on w times w. -/
def binaryOn {n : ℕ} (w f : Fin n) : SetFormula n :=
  .conj (functionGraph f) (.conj
    (allIn f fun p s =>
      exIn (s w) fun x t =>
      exIn (t (s w)) fun y u =>
      exIn (u (t (s w))) fun z v =>
      qEx fun xy r => .conj (orderedPair (r (v (u x))) (r (v y)) xy)
        (orderedPair xy (r z) (r (v (u (t p))))))
    (allIn w fun x s => allIn (s w) fun y t => exIn (t (s w)) fun z u =>
      graphApp₂ (u (t (s f))) (u (t x)) (u y) z))

def relationOn {n : ℕ} (w f : Fin n) : SetFormula n :=
  allIn f fun p s => exIn (s w) fun x t => exIn (t (s w)) fun y u =>
    orderedPair (u x) y (u (t p))

def injectiveGraph {n : ℕ} (f : Fin n) : SetFormula n :=
  qAll fun x s => qAll fun y t => qAll fun z u =>
    .imp (.conj (graphApp (u (t (s f))) (u (t x)) z)
      (graphApp (u (t (s f))) (u y) z)) (.eq (u (t x)) (u y))

/-- The finite tuple of auxiliary arithmetic and node-order graphs. -/
structure Parameters (α : Type) where
  w : α
  zero : α
  one : α
  two : α
  add : α
  mul : α
  pow : α
  p : α
  n : α
  offset : α
  ancestor : α

def Parameters.map {α β : Type} (a : Parameters α) (f : α → β) : Parameters β where
  w := f a.w
  zero := f a.zero
  one := f a.one
  two := f a.two
  add := f a.add
  mul := f a.mul
  pow := f a.pow
  p := f a.p
  n := f a.n
  offset := f a.offset
  ancestor := f a.ancestor

def addRecursion {n : ℕ} (a : Parameters (Fin n)) : SetFormula n :=
  .conj (allIn a.w fun x s => graphApp₂ (s a.add) x (s a.zero) x)
    (allIn a.w fun x s =>
      let a := a.map s
      allIn a.w fun y s =>
      let a := a.map s; let x := s x
      allIn a.w fun y' s =>
      let a := a.map s; let x := s x; let y := s y
      allIn a.w fun v s =>
      let a := a.map s; let x := s x; let y := s y; let y' := s y'
      .imp (successor y y') (.iff (graphApp₂ a.add x y' v)
        (exIn a.w fun u s => .conj (graphApp₂ (s a.add) (s x) (s y) u)
          (successor u (s v)))))

def mulRecursion {n : ℕ} (a : Parameters (Fin n)) : SetFormula n :=
  .conj (allIn a.w fun x s => graphApp₂ (s a.mul) x (s a.zero) (s a.zero))
    (allIn a.w fun x s =>
      let a := a.map s
      allIn a.w fun y s =>
      let a := a.map s; let x := s x
      allIn a.w fun y' s =>
      let a := a.map s; let x := s x; let y := s y
      allIn a.w fun v s =>
      let a := a.map s; let x := s x; let y := s y; let y' := s y'
      .imp (successor y y') (.iff (graphApp₂ a.mul x y' v)
        (exIn a.w fun u s => .conj (graphApp₂ (s a.mul) (s x) (s y) u)
          (graphApp₂ (s a.add) u (s x) (s v)))))

def powRecursion {n : ℕ} (a : Parameters (Fin n)) : SetFormula n :=
  .conj (allIn a.w fun x s => graphApp₂ (s a.pow) x (s a.zero) (s a.one))
    (allIn a.w fun x s =>
      let a := a.map s
      allIn a.w fun y s =>
      let a := a.map s; let x := s x
      allIn a.w fun y' s =>
      let a := a.map s; let x := s x; let y := s y
      allIn a.w fun v s =>
      let a := a.map s; let x := s x; let y := s y; let y' := s y'
      .imp (successor y y') (.iff (graphApp₂ a.pow x y' v)
        (exIn a.w fun u s => .conj (graphApp₂ (s a.pow) (s x) (s y) u)
          (graphApp₂ (s a.mul) u (s x) (s v)))))

def growthRecursion {n : ℕ} (a : Parameters (Fin n)) : SetFormula n :=
  .conj (graphApp a.p a.zero a.one)
  (.conj (graphApp a.n a.zero a.one)
  (.conj (graphApp a.offset a.zero a.one)
    (allIn a.w fun k s =>
      let a := a.map s
      allIn a.w fun k' s =>
      let a := a.map s; let k := s k
      allIn a.w fun p s =>
      let a := a.map s; let k := s k; let k' := s k'
      allIn a.w fun n s =>
      let a := a.map s; let k := s k; let k' := s k'; let p := s p
      allIn a.w fun o s =>
      let a := a.map s; let k := s k; let k' := s k'; let p := s p; let n := s n
      allIn a.w fun p' s =>
      let a := a.map s; let k := s k; let k' := s k'; let p := s p; let n := s n; let o := s o
      allIn a.w fun n' s =>
      let a := a.map s; let k := s k; let k' := s k'; let p := s p; let n := s n; let o := s o; let p' := s p'
      allIn a.w fun o' s =>
      let a := a.map s; let k := s k; let k' := s k'; let p := s p; let n := s n; let o := s o; let p' := s p'; let n' := s n'
      .imp (successor k k')
        (.imp (graphApp a.p k p) (.imp (graphApp a.n k n)
          (.imp (graphApp a.offset k o) (.imp (graphApp a.p k' p')
            (.imp (graphApp a.n k' n') (.imp (graphApp a.offset k' o')
              (.conj (graphApp₂ a.mul p n p')
                (.conj (graphApp₂ a.pow a.two p' n') (graphApp₂ a.add o n o'))))))))))))

/-- Node j is one of the immediate children in the block belonging to k. -/
def child {n : ℕ} (a : Parameters (Fin n)) (k j : Fin n) : SetFormula n :=
  exIn a.w fun o s =>
  let a := a.map s; let k := s k; let j := s j
  exIn a.w fun n s =>
  let a := a.map s; let k := s k; let j := s j; let o := s o
  exIn a.w fun endIndex s =>
  let a := a.map s; let k := s k; let j := s j; let o := s o; let n := s n
  .conj (graphApp a.offset k o) (.conj (graphApp a.n k n)
    (.conj (graphApp₂ a.add o n endIndex) (.conj (leNat o j) (.mem j endIndex))))

def ancestorRecursion {n : ℕ} (a : Parameters (Fin n)) : SetFormula n :=
  .conj (relationOn a.w a.ancestor)
    (allIn a.w fun i s =>
      let a := a.map s
      allIn a.w fun j s =>
      let a := a.map s; let i := s i
      .iff (graphApp a.ancestor i j) (.disj (.eq i j)
        (exIn a.w fun k s => .conj (child (a.map s) k (s j))
          (graphApp (s a.ancestor) (s i) k))))

def arithmetic {n : ℕ} (a : Parameters (Fin n)) : SetFormula n :=
  .conj (omega a.w) (.conj (empty a.zero)
  (.conj (successor a.zero a.one) (.conj (successor a.one a.two)
  (.conj (.mem a.zero a.w) (.conj (.mem a.one a.w) (.conj (.mem a.two a.w)
  (.conj (binaryOn a.w a.add) (.conj (binaryOn a.w a.mul) (.conj (binaryOn a.w a.pow)
  (.conj (unaryOn a.w a.p) (.conj (unaryOn a.w a.n) (.conj (unaryOn a.w a.offset)
  (.conj (addRecursion a) (.conj (mulRecursion a) (.conj (powRecursion a)
  (.conj (growthRecursion a) (ancestorRecursion a)))))))))))))))))

/-- An injection from the finite ordinal r into the children of u retained
by T. The graph has exactly domain r; no extra input or output is implicit. -/
def manyChildren {n : ℕ} (a : Parameters (Fin n)) (T u r : Fin n) : SetFormula n :=
  qEx fun f s =>
    let a := a.map s; let T := s T; let u := s u; let r := s r
    .conj (functionGraph f) (.conj (graphDomain f r)
      (.conj (injectiveGraph f)
        (allIn r fun i s => exIn (s T) fun j t =>
          .conj (graphApp (t (s f)) (t i) j) (child (a.map (fun v => t (s v))) (t (s u)) j))))

/-- The indexed version of the actual forcing condition definition. -/
def conditionCode {n : ℕ} (a : Parameters (Fin n)) (T : Fin n) : SetFormula n :=
  .conj (subset T a.w) (.conj (.mem a.zero T)
    (.conj
      (allIn T fun j s => allIn (s a.w) fun i t =>
        .imp (graphApp (t (s a.ancestor)) i (t j)) (.mem i (t (s T))))
      (allIn T fun i s =>
        let a := a.map s; let T := s T
        allIn a.w fun m s =>
        let a := a.map s; let T := s T; let i := s i
        exIn T fun u s =>
        let a := a.map s; let T := s T; let i := s i; let m := s m
        .conj (.neg (.eq i u)) (.conj (graphApp a.ancestor i u)
          (exIn a.w fun p s =>
            let a := a.map s; let T := s T; let u := s u; let m := s m
            exIn a.w fun r s =>
            let a := a.map s; let T := s T; let u := s u; let m := s m; let p := s p
            .conj (graphApp a.p u p) (.conj (graphApp₂ a.pow p m r)
              (manyChildren a T u r)))))))

def posetCarrier {n : ℕ} (a : Parameters (Fin n)) (P : Fin n) : SetFormula n :=
  qAll fun T s => .iff (.mem T (s P)) (conditionCode (a.map s) T)

def inclusionGraph {n : ℕ} (P O : Fin n) : SetFormula n :=
  qAll fun z s => .iff (.mem z (s O))
    (exIn (s P) fun X t => exIn (t (s P)) fun Y u =>
      .conj (orderedPair (u X) Y (u (t z))) (subset (u X) Y))

/-- The open cylinder at index i contains exactly those conditions all of
whose nodes are comparable with i. -/
def generatorOpen {n : ℕ} (a : Parameters (Fin n)) (P i X : Fin n) : SetFormula n :=
  qAll fun T s => .iff (.mem T (s X))
    (.conj (.mem T (s P)) (allIn T fun j t =>
      .disj (graphApp (t (s a.ancestor)) j (t (s i)))
        (graphApp (t (s a.ancestor)) (t (s i)) j)))

def generatorGraph {n : ℕ} (a : Parameters (Fin n)) (P G : Fin n) : SetFormula n :=
  .conj (functionGraph G) (.conj (graphDomain G a.w)
    (allIn a.w fun i s => qAll fun X t =>
      .iff (graphApp (t (s G)) (t i) X)
        (generatorOpen (a.map (fun v => t (s v))) (t (s P)) (t i) X)))

/-- With the auxiliary graphs displayed, the final code is already finite. -/
def codeWith {n : ℕ} (a : Parameters (Fin n)) (c P O G : Fin n) : SetFormula n :=
  .conj (arithmetic a) (.conj (posetCarrier a P) (.conj (inclusionGraph P O)
    (.conj (MaxAtomicityRegularOpenCode.algebraCarrier P O c) (generatorGraph a P G))))

/-- Close the twelve auxiliary graph/set variables. The three remaining
variables are c (0), w (1), and the canonical generator graph G (2). -/
def JSCode : SetFormula 3 :=
  qEx fun z s =>
  let c := s 0; let w := s 1; let G := s 2
  qEx fun one s =>
  let c := s c; let w := s w; let G := s G; let z := s z
  qEx fun two s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one
  qEx fun add s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one; let two := s two
  qEx fun mul s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one; let two := s two; let add := s add
  qEx fun pow s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one; let two := s two; let add := s add; let mul := s mul
  qEx fun p s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one; let two := s two; let add := s add; let mul := s mul; let pow := s pow
  qEx fun n s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one; let two := s two; let add := s add; let mul := s mul; let pow := s pow; let p := s p
  qEx fun offset s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one; let two := s two; let add := s add; let mul := s mul; let pow := s pow; let p := s p; let n := s n
  qEx fun ancestor s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one; let two := s two; let add := s add; let mul := s mul; let pow := s pow; let p := s p; let n := s n; let offset := s offset
  qEx fun P s =>
  let c := s c; let w := s w; let G := s G; let z := s z; let one := s one; let two := s two; let add := s add; let mul := s mul; let pow := s pow; let p := s p; let n := s n; let offset := s offset; let ancestor := s ancestor
  qEx fun O s =>
  codeWith ⟨s w, s z, s one, s two, s add, s mul, s pow, s p, s n, s offset, s ancestor⟩
    (s c) (s P) O (s G)

namespace Ordinary

open MaxAtomicitySetFormulaTools.Ordinary

variable {D : Type*} (R : D → D → Prop)

def LeNat (a b : D) : Prop := a = b ∨ R a b
def Successor (a b : D) : Prop := ∀ x, R x b ↔ R x a ∨ x = a
def InductiveSet (w : D) : Prop :=
  (∃ z, R z w ∧ Empty R z) ∧ ∀ x, R x w → ∃ y, R y w ∧ Successor R x y
def Omega (w : D) : Prop :=
  InductiveSet R w ∧ ∀ I, InductiveSet R I → Subset R w I
def GraphApp₂ (f x y z : D) : Prop :=
  ∃ xy, OrderedPair R x y xy ∧ GraphApp R f xy z
def UnaryOn (w f : D) : Prop :=
  FunctionGraph R f ∧ GraphDomain R f w ∧
    ∀ x, R x w → ∃ y, R y w ∧ GraphApp R f x y
def BinaryOn (w f : D) : Prop :=
  FunctionGraph R f ∧
    (∀ p, R p f → ∃ x, R x w ∧ ∃ y, R y w ∧ ∃ z, R z w ∧
      ∃ xy, OrderedPair R x y xy ∧ OrderedPair R xy z p) ∧
    ∀ x, R x w → ∀ y, R y w → ∃ z, R z w ∧ GraphApp₂ R f x y z
def RelationOn (w f : D) : Prop :=
  ∀ p, R p f → ∃ x, R x w ∧ ∃ y, R y w ∧ OrderedPair R x y p
def InjectiveGraph (f : D) : Prop :=
  ∀ x y z, (GraphApp R f x z ∧ GraphApp R f y z) → x = y

def AddRecursion (a : Parameters D) : Prop :=
  (∀ x, R x a.w → GraphApp₂ R a.add x a.zero x) ∧
    ∀ x, R x a.w → ∀ y, R y a.w → ∀ y', R y' a.w → ∀ v, R v a.w →
      Successor R y y' →
        (GraphApp₂ R a.add x y' v ↔
          ∃ u, R u a.w ∧ GraphApp₂ R a.add x y u ∧ Successor R u v)
def MulRecursion (a : Parameters D) : Prop :=
  (∀ x, R x a.w → GraphApp₂ R a.mul x a.zero a.zero) ∧
    ∀ x, R x a.w → ∀ y, R y a.w → ∀ y', R y' a.w → ∀ v, R v a.w →
      Successor R y y' →
        (GraphApp₂ R a.mul x y' v ↔
          ∃ u, R u a.w ∧ GraphApp₂ R a.mul x y u ∧ GraphApp₂ R a.add u x v)
def PowRecursion (a : Parameters D) : Prop :=
  (∀ x, R x a.w → GraphApp₂ R a.pow x a.zero a.one) ∧
    ∀ x, R x a.w → ∀ y, R y a.w → ∀ y', R y' a.w → ∀ v, R v a.w →
      Successor R y y' →
        (GraphApp₂ R a.pow x y' v ↔
          ∃ u, R u a.w ∧ GraphApp₂ R a.pow x y u ∧ GraphApp₂ R a.mul u x v)
def GrowthRecursion (a : Parameters D) : Prop :=
  GraphApp R a.p a.zero a.one ∧ GraphApp R a.n a.zero a.one ∧
  GraphApp R a.offset a.zero a.one ∧
    ∀ k, R k a.w → ∀ k', R k' a.w → ∀ p, R p a.w → ∀ n, R n a.w →
    ∀ o, R o a.w → ∀ p', R p' a.w → ∀ n', R n' a.w → ∀ o', R o' a.w →
      Successor R k k' → GraphApp R a.p k p → GraphApp R a.n k n →
        GraphApp R a.offset k o → GraphApp R a.p k' p' → GraphApp R a.n k' n' →
          GraphApp R a.offset k' o' →
            GraphApp₂ R a.mul p n p' ∧ GraphApp₂ R a.pow a.two p' n' ∧
              GraphApp₂ R a.add o n o'
def Child (a : Parameters D) (k j : D) : Prop :=
  ∃ o, R o a.w ∧ ∃ n, R n a.w ∧ ∃ endIndex, R endIndex a.w ∧
    GraphApp R a.offset k o ∧ GraphApp R a.n k n ∧ GraphApp₂ R a.add o n endIndex ∧
      LeNat R o j ∧ R j endIndex
def AncestorRecursion (a : Parameters D) : Prop :=
  RelationOn R a.w a.ancestor ∧ ∀ i, R i a.w → ∀ j, R j a.w →
    (GraphApp R a.ancestor i j ↔ i = j ∨
      ∃ k, R k a.w ∧ Child R a k j ∧ GraphApp R a.ancestor i k)
def Arithmetic (a : Parameters D) : Prop :=
  Omega R a.w ∧ Empty R a.zero ∧ Successor R a.zero a.one ∧ Successor R a.one a.two ∧
  R a.zero a.w ∧ R a.one a.w ∧ R a.two a.w ∧
  BinaryOn R a.w a.add ∧ BinaryOn R a.w a.mul ∧ BinaryOn R a.w a.pow ∧
  UnaryOn R a.w a.p ∧ UnaryOn R a.w a.n ∧ UnaryOn R a.w a.offset ∧
  AddRecursion R a ∧ MulRecursion R a ∧ PowRecursion R a ∧
  GrowthRecursion R a ∧ AncestorRecursion R a
def ManyChildren (a : Parameters D) (T u r : D) : Prop :=
  ∃ f, FunctionGraph R f ∧ GraphDomain R f r ∧ InjectiveGraph R f ∧
    ∀ i, R i r → ∃ j, R j T ∧ GraphApp R f i j ∧ Child R a u j
def ConditionCode (a : Parameters D) (T : D) : Prop :=
  Subset R T a.w ∧ R a.zero T ∧
    (∀ j, R j T → ∀ i, R i a.w → GraphApp R a.ancestor i j → R i T) ∧
    ∀ i, R i T → ∀ m, R m a.w → ∃ u, R u T ∧ i ≠ u ∧ GraphApp R a.ancestor i u ∧
      ∃ p, R p a.w ∧ ∃ r, R r a.w ∧ GraphApp R a.p u p ∧
        GraphApp₂ R a.pow p m r ∧ ManyChildren R a T u r
def PosetCarrier (a : Parameters D) (P : D) : Prop :=
  ∀ T, R T P ↔ ConditionCode R a T
def InclusionGraph (P O : D) : Prop :=
  ∀ z, R z O ↔ ∃ X, R X P ∧ ∃ Y, R Y P ∧ OrderedPair R X Y z ∧ Subset R X Y
def GeneratorOpen (a : Parameters D) (P i X : D) : Prop :=
  ∀ T, R T X ↔ R T P ∧ ∀ j, R j T →
    GraphApp R a.ancestor j i ∨ GraphApp R a.ancestor i j
def GeneratorGraph (a : Parameters D) (P G : D) : Prop :=
  FunctionGraph R G ∧ GraphDomain R G a.w ∧ ∀ i, R i a.w → ∀ X,
    GraphApp R G i X ↔ GeneratorOpen R a P i X
def CodeWith (a : Parameters D) (c P O G : D) : Prop :=
  Arithmetic R a ∧ PosetCarrier R a P ∧ InclusionGraph R P O ∧
    MaxAtomicityRegularOpenCode.Ordinary.AlgebraCarrier R P O c ∧ GeneratorGraph R a P G
def JSCode (c w G : D) : Prop :=
  ∃ z one two add mul pow p n offset ancestor P O,
    CodeWith R ⟨w, z, one, two, add, mul, pow, p, n, offset, ancestor⟩ c P O G

end Ordinary

theorem satisfies_leNat {D : Type} {n : ℕ} (a b : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (leNat a b) R ρ ↔ Ordinary.LeNat R (ρ a) (ρ b) := Iff.rfl

theorem satisfies_successor {D : Type} {n : ℕ} (a b : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (successor a b) R ρ ↔ Ordinary.Successor R (ρ a) (ρ b) := Iff.rfl

theorem satisfies_inductiveSet {D : Type} {n : ℕ} (w : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (inductiveSet w) R ρ ↔ Ordinary.InductiveSet R (ρ w) := Iff.rfl

theorem satisfies_omega {D : Type} {n : ℕ} (w : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (omega w) R ρ ↔ Ordinary.Omega R (ρ w) := Iff.rfl

theorem satisfies_graphApp₂ {D : Type} {n : ℕ} (f x y z : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (graphApp₂ f x y z) R ρ ↔
      Ordinary.GraphApp₂ R (ρ f) (ρ x) (ρ y) (ρ z) := Iff.rfl

theorem satisfies_unaryOn {D : Type} {n : ℕ} (w f : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (unaryOn w f) R ρ ↔ Ordinary.UnaryOn R (ρ w) (ρ f) := Iff.rfl

theorem satisfies_binaryOn {D : Type} {n : ℕ} (w f : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (binaryOn w f) R ρ ↔ Ordinary.BinaryOn R (ρ w) (ρ f) := Iff.rfl

theorem satisfies_relationOn {D : Type} {n : ℕ} (w f : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (relationOn w f) R ρ ↔ Ordinary.RelationOn R (ρ w) (ρ f) := Iff.rfl

theorem satisfies_injectiveGraph {D : Type} {n : ℕ} (f : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (injectiveGraph f) R ρ ↔ Ordinary.InjectiveGraph R (ρ f) := Iff.rfl

theorem satisfies_addRecursion {D : Type} {n : ℕ} (a : Parameters (Fin n))
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (addRecursion a) R ρ ↔ Ordinary.AddRecursion R (a.map ρ) := Iff.rfl

theorem satisfies_mulRecursion {D : Type} {n : ℕ} (a : Parameters (Fin n))
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (mulRecursion a) R ρ ↔ Ordinary.MulRecursion R (a.map ρ) := Iff.rfl

theorem satisfies_powRecursion {D : Type} {n : ℕ} (a : Parameters (Fin n))
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (powRecursion a) R ρ ↔ Ordinary.PowRecursion R (a.map ρ) := Iff.rfl

theorem satisfies_growthRecursion {D : Type} {n : ℕ} (a : Parameters (Fin n))
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (growthRecursion a) R ρ ↔ Ordinary.GrowthRecursion R (a.map ρ) := Iff.rfl

theorem satisfies_child {D : Type} {n : ℕ} (a : Parameters (Fin n)) (k j : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (child a k j) R ρ ↔ Ordinary.Child R (a.map ρ) (ρ k) (ρ j) := Iff.rfl

theorem satisfies_ancestorRecursion {D : Type} {n : ℕ} (a : Parameters (Fin n))
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (ancestorRecursion a) R ρ ↔ Ordinary.AncestorRecursion R (a.map ρ) := Iff.rfl

theorem satisfies_arithmetic {D : Type} {n : ℕ} (a : Parameters (Fin n))
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (arithmetic a) R ρ ↔ Ordinary.Arithmetic R (a.map ρ) := Iff.rfl

theorem satisfies_manyChildren {D : Type} {n : ℕ} (a : Parameters (Fin n)) (T u r : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (manyChildren a T u r) R ρ ↔
      Ordinary.ManyChildren R (a.map ρ) (ρ T) (ρ u) (ρ r) := Iff.rfl

theorem satisfies_conditionCode {D : Type} {n : ℕ} (a : Parameters (Fin n)) (T : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (conditionCode a T) R ρ ↔ Ordinary.ConditionCode R (a.map ρ) (ρ T) := Iff.rfl

theorem satisfies_posetCarrier {D : Type} {n : ℕ} (a : Parameters (Fin n)) (P : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (posetCarrier a P) R ρ ↔ Ordinary.PosetCarrier R (a.map ρ) (ρ P) := Iff.rfl

theorem satisfies_inclusionGraph {D : Type} {n : ℕ} (P O : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (inclusionGraph P O) R ρ ↔ Ordinary.InclusionGraph R (ρ P) (ρ O) := Iff.rfl

theorem satisfies_generatorOpen {D : Type} {n : ℕ} (a : Parameters (Fin n)) (P i X : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (generatorOpen a P i X) R ρ ↔
      Ordinary.GeneratorOpen R (a.map ρ) (ρ P) (ρ i) (ρ X) := Iff.rfl

theorem satisfies_generatorGraph {D : Type} {n : ℕ} (a : Parameters (Fin n)) (P G : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (generatorGraph a P G) R ρ ↔ Ordinary.GeneratorGraph R (a.map ρ) (ρ P) (ρ G) := Iff.rfl

theorem satisfies_codeWith {D : Type} {n : ℕ} (a : Parameters (Fin n)) (c P O G : Fin n)
    (R : D → D → Prop) (ρ : Fin n → D) :
    satisfies (codeWith a c P O G) R ρ ↔
      Ordinary.CodeWith R (a.map ρ) (ρ c) (ρ P) (ρ O) (ρ G) := Iff.rfl

/-- Actual finite syntax correctness, including all twelve existential binders.
This theorem expands the code to its explicit ordinary relational specification;
it does not assume or prove the remaining hereditary-universe adequacy theorem. -/
theorem satisfies_JSCode {D : Type} (R : D → D → Prop) (ρ : Fin 3 → D) :
    satisfies JSCode R ρ ↔ Ordinary.JSCode R (ρ 0) (ρ 1) (ρ 2) := Iff.rfl

#print axioms satisfies_binaryOn
#print axioms satisfies_growthRecursion
#print axioms satisfies_conditionCode
#print axioms satisfies_JSCode

end Classicism.Meta.Research.MaxAtomicityJechShelahSyntax
