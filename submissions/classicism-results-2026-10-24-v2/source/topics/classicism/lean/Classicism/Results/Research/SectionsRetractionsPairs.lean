import Classicism.Results.Research.SectionsRetractionsActuality

/-!
# Pair codes, actual-world pins, and relational decoding

Direct source: `research/2026-10-22/notes/functional-choice-by-sections.md`,
§3 (`misc`, original research, 22 October 2026; unpaginated).
Input types may be e. Every constructed operation has relational output.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def pairCode {σ τ : Type} [Ty σ] [Ty τ] (x : σ) (y : τ) : σ → τ → Prop :=
  fun u v => u = x ∧ v = y

theorem pairCode_components {σ τ : Type} [Ty σ] [Ty τ]
    (x x' : σ) (y y' : τ) : pairCode x y = pairCode x' y' → x = x' ∧ y = y' :=
  fun he => (congrFun (congrFun he x) y).mp ⟨rfl, rfl⟩

theorem pairCode_nonzero {σ τ : Type} [Ty σ] [Ty τ] (x : σ) (y : τ) :
    pairCode x y ≠ (fun (_ : σ) (_ : τ) => False) :=
  fun he => (congrFun (congrFun he x) y).mp ⟨rfl, rfl⟩

def pin {σ τ : Type} [Ty σ] [Rel τ] (w : Prop) (x : σ) : σ → τ → Prop :=
  fun u _ => w ∧ u = x

theorem pin_injective {σ τ : Type} [Ty σ] [Rel τ] (w : Prop) (hw : w)
    (x x' : σ) : pin (τ := τ) w x = pin w x' → x = x' :=
  fun he => ((congrFun (congrFun he x) (Rel.top τ)).mp ⟨hw, rfl⟩).2

theorem pin_nonzero {σ τ : Type} [Ty σ] [Rel τ] (w : Prop) (hw : w) (x : σ) :
    pin (τ := τ) w x ≠ (fun (_ : σ) (_ : τ) => False) :=
  fun he => (congrFun (congrFun he x) (Rel.top τ)).mp ⟨hw, rfl⟩

def ValidPair {σ τ : Type} [Ty σ] [Rel τ]
    (U : σ → τ → Prop) (k : σ → τ → Prop) : Prop :=
  ∃ x y, U x y ∧ k = pairCode x y

def PinRange {σ τ : Type} [Ty σ] [Rel τ]
    (w : Prop) (b : σ → τ → Prop) : Prop := ∃ x, b = pin w x

def projectPair {σ τ : Type} [Ty σ] [Rel τ]
    (U : σ → τ → Prop) (w : Prop) (k : σ → τ → Prop) : σ → τ → Prop :=
  fun u _ => w ∧ ∃ x y, U x y ∧ k = pairCode x y ∧ u = x

theorem invalid_bottom {σ τ : Type} [Ty σ] [Rel τ] (U : σ → τ → Prop) :
    ¬ ValidPair U (fun _ _ => False) :=
  fun h => h.elim fun x hx => hx.elim fun y hy => pairCode_nonzero x y hy.2.symm

theorem projectPair_coext {σ τ : Type} [Ty σ] [Rel τ]
    (U : σ → τ → Prop) (w : Prop) (x : σ) (y : τ) :
    (w → U x y) → projectPair U w (pairCode x y) ≡ pin w x := by
  intro hu u v
  constructor
  · intro h
    obtain ⟨a, b, _, he, hux⟩ := h.2
    exact ⟨h.1, hux.trans (pairCode_components x a y b he).1.symm⟩
  · intro h
    exact ⟨h.1, x, y, hu h.1, rfl, h.2⟩

theorem projectPair_actual {σ τ : Type} [Ty σ] [Rel τ]
    (U : σ → τ → Prop) (w : Prop) (hw : ActualWorld w)
    (x : σ) (y : τ) (hu : U x y) : projectPair U w (pairCode x y) = pin w x :=
  intensionality _ _ (modal_K _ _ (nec% (projectPair_coext U w x y))
    ((le_iff_prop w (U x y)).mp (hw.2 (U x y) hu)))

def decodePair {σ ν : Type} [Ty σ] [Ty ν]
    (k : σ → (ν → Prop) → Prop) (x : σ) : ν → Prop :=
  fun u => ∃ y, k x y ∧ y u

theorem decodePair_code {σ ν : Type} [Ty σ] [Ty ν] (x : σ) (y : ν → Prop) :
    decodePair (pairCode x y) x = y :=
  funext fun u => propext
    ⟨fun h => h.elim fun z hz => hz.1.2 ▸ hz.2,
     fun h => ⟨y, ⟨rfl, rfl⟩, h⟩⟩

def mix {ν : Type} [Ty ν] (p : Prop) (a b : ν → Prop) : ν → Prop :=
  fun u => (p ∧ a u) ∨ (¬ p ∧ b u)

theorem mix_true {ν : Type} [Ty ν] (a b : ν → Prop) : mix True a b = a :=
  funext fun u => propext
    ⟨fun h => h.elim And.right (fun h => (h.1 trivial).elim),
     fun h => Or.inl ⟨trivial, h⟩⟩

theorem mix_false {ν : Type} [Ty ν] (a b : ν → Prop) : mix False a b = b :=
  funext fun u => propext
    ⟨fun h => h.elim (fun h => h.1.elim) And.right,
     fun h => Or.inr ⟨fun hf => hf, h⟩⟩

def mixPair {σ τ : Type} [Ty σ] [Ty τ]
    (p : Prop) (a b : σ → τ → Prop) : σ → τ → Prop :=
  fun u v => (p ∧ a u v) ∨ (¬ p ∧ b u v)

theorem mixPair_true {σ τ : Type} [Ty σ] [Ty τ] (a b : σ → τ → Prop) :
    mixPair True a b = a := funext fun u => mix_true (a u) (b u)

theorem mixPair_false {σ τ : Type} [Ty σ] [Ty τ] (a b : σ → τ → Prop) :
    mixPair False a b = b := funext fun u => mix_false (a u) (b u)

def slotsPair {σ τ : Type} [Ty σ] [Ty τ]
    (q s : σ → τ → Prop) (r : Prop) : σ → τ → Prop :=
  fun u v => slotsT (q u v) (s u v) r

theorem slotsPair_false {σ τ : Type} [Ty σ] [Ty τ] (q s : σ → τ → Prop) :
    slotsPair q s False = q :=
  funext fun u => funext fun v => slotsT_false (q u v) (s u v)

theorem slotsPair_true {σ τ : Type} [Ty σ] [Ty τ] (q s : σ → τ → Prop) :
    slotsPair q s True = s :=
  funext fun u => funext fun v => slotsT_true (q u v) (s u v)

end Classicism.Research.Splitting
