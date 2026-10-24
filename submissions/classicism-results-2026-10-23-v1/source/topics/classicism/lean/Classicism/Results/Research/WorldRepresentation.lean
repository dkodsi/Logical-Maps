import Classicism.Results.Research.ActualityCore
import Classicism.Results.Records.C5

/-!
# Admitted world-indexed representation

Direct source: `research/2026-10-22/notes/structural-world-representation.md`,
§§2–4 (original research, `misc`, 22 October 2026, unpaginated).

The family is an admitted object, not an external powerset. The normalization
guard `Atom w` is retained. The principal theorem assumes the single displayed
`NecPlenitude Prop Prop` instance and derives its modal prerequisites through
existing checked C proofs. Explicit operations below have one trailing argument;
the separate certificate driver requires their actual tuple `.listRule`.
No atom-coordinate classification or actual-world kernel is duplicated.
-/

namespace Classicism.Research.WorldRepresentation
open Classicism.Paper Classicism.P Classicism.Proofs

def At (w p : Prop) : Prop := w ≤ p

theorem atom_possible (w : Prop) (hw : Atom w) : ◇ w :=
  fun h => not_le_neg_of_atom hw (le_neg_of_eq_false w h)

theorem at_true (w : Prop) : At w True := le_top_prop w

theorem not_at_false (w : Prop) (hw : Atom w) : ¬ At w False := fun h =>
  not_le_neg_of_atom hw (le_trans_prop w False (¬ w) h (bot_le_prop (¬ w)))

theorem at_and (w p q : Prop) : At w (p ∧ q) ↔ (At w p ∧ At w q) :=
  ⟨fun h => ⟨le_trans_prop _ _ _ h (and_le_left_prop p q),
    le_trans_prop _ _ _ h (and_le_right_prop p q)⟩,
    fun h => le_and_prop w p q h.1 h.2⟩

theorem at_neg (w p : Prop) (hw : Atom w) : At w (¬ p) ↔ ¬ At w p :=
  ⟨fun hn hp => not_le_neg_of_atom hw (le_neg_of_le_both_rel w p hp hn),
    fun hn => (atom_le_or_le_neg w p hw).elim (fun hp => (hn hp).elim) (fun h => h)⟩

theorem at_or_step (w p q : Prop) :
    (w → p ∨ q) → (w → ¬ p) → w → q :=
  fun hpq hn hw => (hpq hw).elim (fun hp => (hn hw hp).elim) (fun hq => hq)

theorem at_or (w p q : Prop) (hw : Atom w) : At w (p ∨ q) ↔ (At w p ∨ At w q) := by
  constructor
  · intro h
    exact (em (At w p)).elim Or.inl (fun hn => Or.inr
      (le_of_box_incl (modal_K _ _ (modal_K _ _ (nec% (at_or_step w p q))
        ((le_iff_prop _ _).1 h)) ((le_iff_prop _ _).1 ((at_neg w p hw).2 hn)))))
  · intro h
    exact h.elim (fun hp => le_trans_prop _ _ _ hp (le_or_left_prop p q))
      (fun hq => le_trans_prop _ _ _ hq (le_or_right_prop p q))

theorem at_current (w p : Prop) (hw : Atom w) (ht : w) : At w p ↔ p :=
  ⟨fun h => imp_of_le_prop w p h ht, fun hp =>
    (atom_le_or_le_neg w p hw).elim (fun h => h)
      (fun h => (imp_of_le_prop w (¬ p) h ht hp).elim)⟩

theorem actualWorld_of_true_atom (w : Prop) (hw : Atom w) (ht : w) : ActualWorld w :=
  ⟨ht, fun p hp => (at_current w p hw ht).2 hp⟩

theorem true_atom_unique (w v : Prop) (hw : Atom w) (hv : Atom v) (htw : w) (htv : v) :
    w = v := Research.actualWorld_unique w v
      (actualWorld_of_true_atom w hw htw) (actualWorld_of_true_atom v hv htv)

theorem at_all {σ : Type} [Ty σ] (bf : Barcan σ) (w : Prop) (F : σ → Prop) :
    At w (∀ x, F x) ↔ ∀ x, At w (F x) := by
  constructor
  · intro h x
    exact le_of_box_incl (modal_K _ _
      (nec% (fun (h : w → ∀ x, F x) (hw : w) => h hw x)) ((le_iff_prop _ _).1 h))
  · intro h
    exact le_of_box_incl (modal_K _ _
      (nec% (fun (h : ∀ x, w → F x) (hw : w) (x : σ) => h x hw))
      (bf (fun x => w → F x) (fun x => (le_iff_prop _ _).1 (h x))))

theorem at_identity {σ : Type} [Ty σ] (nd : NecessityOfDistinctness σ)
    (w : Prop) (hw : Atom w) (a b : σ) : At w (a = b) ↔ a = b :=
  ⟨fun h => eq_of_dia_eq nd a b
    (dia_mono _ _ ((le_iff_prop _ _).1 h) (atom_possible w hw)),
    fun h => le_of_box_incl (box_imp_of_box w (a = b) (necessity_of_identity a b h))⟩

theorem atom_necessary (c5 : NecNecessityOfDistinctnessT) (w : Prop) (hw : Atom w) :
    □ (Atom w) :=
  modal_K _ _ (nec% (atom_of_decides w)) ((box_and_eq _ _).mpr
    ⟨box_elim c5 w False (atom_possible w hw),
      necessary_nd_implies_bf c5 (fun p => w ≤ p ∨ w ≤ ¬ p)
        (fun p => box_le_or_le w p (atom_le_or_le_neg w p hw))⟩)

theorem atoms_persistent (c5 : NecNecessityOfDistinctnessT) :
    Persistent (fun w : Prop => Atom w) :=
  modal_K _ _ (nec% (fun (h : NecNecessityOfDistinctnessT) (w : Prop) =>
    atom_necessary h w)) (modal_four _ c5)

/-- C5 turns persistence into necessary falsity of current negative instances.
This pointwise statement works at every relational type via existing laws. -/
theorem persistent_negative {τ : Type} [Rel τ] [Pointwise τ]
    (c5 : NecNecessityOfDistinctnessT) (X : τ) (hX : Persistent X) :
    WeaklyPersistent (Rel.neg X) :=
  neg_incl_boxAt_of_b X (b_of_nd_t (box_elim c5)) (top_boxAt_of_box X (boxAt X) hX)

theorem at_constant (w p : Prop) (hw : Atom w)
    (hp : p → □ p) (hn : ¬ p → □ (¬ p)) : At w p ↔ p :=
  ⟨fun hAt => (em p).elim (fun h => h) (fun hnot =>
    (not_le_neg_of_atom hw (le_neg_of_le_both_rel w p hAt
      (le_of_box_incl (box_imp_of_box w (¬ p) (hn hnot))))).elim),
    fun h => le_of_box_incl (box_imp_of_box w p (hp h))⟩

theorem atomic_coverage (at_ : AtomicityT) (p : Prop) :
    (∀ w : Prop, Atom w → At w p) ↔ □ p := by
  constructor
  · intro h
    apply (em (□ p)).elim (fun hp => hp)
    intro hn
    apply (at_ (¬ p)).elim
    · intro hz
      exact box_of_neg_le_neg_neg p hz
    · intro hs
      obtain ⟨w, hw, hwp⟩ := hs
      exact (not_le_neg_of_atom hw (le_neg_of_le_both_rel w p (h w hw) hwp)).elim
  · intro hp w _
    exact le_of_box_incl (box_imp_of_box w p hp)

theorem at_box (c5 : NecNecessityOfDistinctnessT) (at_ : AtomicityT)
    (w p : Prop) (hw : Atom w) :
    At w (□ p) ↔ ∀ v : Prop, Atom v → At v p := by
  have hb : At w (□ p) ↔ □ p := at_constant w (□ p) hw (modal_four p)
    (fun hn => box_elim c5 p True hn)
  exact hb.trans (atomic_coverage at_ p).symm

/-! ## Canonical admitted families with one trailing argument -/
section unary
variable {σ : Type} [Ty σ]

def Encode (X : σ → Prop) : Prop → σ → Prop := fun w x => Atom w ∧ At w (X x)
def Decode (F : Prop → σ → Prop) : σ → Prop := fun x => ∃ w, Atom w ∧ w ∧ F w x
def AtomSupport : Prop → σ → Prop := fun w _ => Atom w
def Admissible (F : Prop → σ → Prop) : Prop := Rigid F ∧ F ≤ AtomSupport

theorem encode_below (X : σ → Prop) : Encode X ≤ AtomSupport :=
  le_of_box_incl (nec% (fun (w : Prop) (x : σ) (h : Encode X w x) => h.1))

theorem encode_weakly_persistent (c5 : NecNecessityOfDistinctnessT) (X : σ → Prop) :
    WeaklyPersistent (Encode X) := fun w x h =>
  (box_and_eq _ _).mpr ⟨atom_necessary c5 w h.1, box_le_prop w (X x) h.2⟩

theorem encode_persistent (c5 : NecNecessityOfDistinctnessT) (X : σ → Prop) :
    Persistent (Encode X) :=
  modal_K _ _ (nec% (fun h : NecNecessityOfDistinctnessT => encode_weakly_persistent h X))
    (modal_four _ c5)

/-- Both object quantifiers are closed explicitly. No inference from unary BF
to a tuple BF is left implicit in this binary intermediate proof. -/
theorem binary_weakly_inextensible (F : Prop → σ → Prop)
    (c5 : NecNecessityOfDistinctnessT) (hF : Persistent F) : WeaklyInextensible F :=
  fun Z hZ => necessary_nd_implies_bf c5 (fun w => ∀ x, F w x → Z w x)
    (fun w => necessary_nd_implies_bf c5 (fun x => F w x → Z w x)
      (fun x => (em (F w x)).elim
        (fun hf => box_imp_of_box _ _ (hZ w x hf))
        (fun hn => box_imp_of_box_not _ _ (persistent_negative c5 F hF w x hn))))

theorem binary_inextensible (F : Prop → σ → Prop)
    (c5 : NecNecessityOfDistinctnessT) (hF : Persistent F) : Inextensible F :=
  modal_K _ _ (modal_K _ _ (nec% (binary_weakly_inextensible F))
    (modal_four _ c5)) (modal_four _ hF)

theorem encode_admissible (c5 : NecNecessityOfDistinctnessT) (X : σ → Prop) :
    Admissible (Encode X) :=
  ⟨⟨encode_persistent c5 X, binary_inextensible (Encode X) c5 (encode_persistent c5 X)⟩,
    encode_below X⟩

theorem decode_encode_current (X : σ → Prop) (act : Actuality) :
    Decode (Encode X) ≡ X := by
  intro x
  constructor
  · intro h
    obtain ⟨w, hw, ht, hX⟩ := h
    exact (at_current w (X x) hw ht).1 hX.2
  · intro hx
    obtain ⟨w, hw⟩ := act
    exact ⟨w, ActualityCore.actualWorld_atom w hw, hw.1,
      ActualityCore.actualWorld_atom w hw, hw.2 (X x) hx⟩

theorem decode_encode (na : NecActuality) (X : σ → Prop) : Decode (Encode X) = X :=
  intensionality _ _ (modal_K _ _ (nec% (decode_encode_current X)) na)

theorem decode_at_true_atom (F : Prop → σ → Prop) (w : Prop) (x : σ) :
    Atom w → w → (Decode F x ↔ F w x) := fun hw ht =>
  ⟨fun h => h.elim fun v hv =>
    (true_atom_unique v w hv.1 hw hv.2.1 ht) ▸ hv.2.2,
    fun h => ⟨w, hw, ht, h⟩⟩

theorem at_transport (w p q : Prop) (h : □ (w → (p ↔ q))) : At w p ↔ At w q :=
  ⟨fun hp => le_of_box_incl (modal_K _ _ (modal_K _ _
      (nec% (fun (he : w → (p ↔ q)) (hp : w → p) (hw : w) => (he hw).1 (hp hw))) h)
      ((le_iff_prop _ _).1 hp)),
    fun hq => le_of_box_incl (modal_K _ _ (modal_K _ _
      (nec% (fun (he : w → (p ↔ q)) (hq : w → q) (hw : w) => (he hw).2 (hq hw))) h)
      ((le_iff_prop _ _).1 hq))⟩

theorem encode_decode_current (c5 : NecNecessityOfDistinctnessT)
    (F : Prop → σ → Prop) (hF : Admissible F) : Encode (Decode F) ≡ F := by
  intro w x
  have pos : F w x → □ (F w x) := weaklyPersistent_of_persistent hF.1.1 w x
  have neg : ¬ F w x → □ (¬ F w x) := persistent_negative c5 F hF.1.1 w x
  constructor
  · intro h
    have he := modal_K _ _ (nec% (decode_at_true_atom F w x)) (atom_necessary c5 w h.1)
    exact (at_constant w (F w x) h.1 pos neg).1
      ((at_transport w (Decode F x) (F w x) he).1 h.2)
  · intro h
    have hw : Atom w := incl_of_le hF.2 w x h
    have he := modal_K _ _ (nec% (decode_at_true_atom F w x)) (atom_necessary c5 w hw)
    exact ⟨hw, (at_transport w (Decode F x) (F w x) he).2
      ((at_constant w (F w x) hw pos neg).2 h)⟩

theorem rigid_ext {τ : Type} [Rel τ] [Order τ] [Pointwise τ]
    (F G : τ) (hF : Rigid F) (hG : Rigid G) (h : F ≡ G) : F = G :=
  le_antisymm_rel F G
    (le_of_box_incl (weaklyInextensible_of_inextensible hF.2 G
      (incl_trans F G (boxAt G) (incl_of_coext F G h)
        (weaklyPersistent_of_persistent hG.1))))
    (le_of_box_incl (weaklyInextensible_of_inextensible hG.2 F
      (incl_trans G F (boxAt F) (incl_of_coext' F G h)
        (weaklyPersistent_of_persistent hF.1))))

theorem encode_decode (c5 : NecNecessityOfDistinctnessT)
    (F : Prop → σ → Prop) (hF : Admissible F) : Encode (Decode F) = F :=
  rigid_ext _ _ (encode_admissible c5 (Decode F)).1 hF.1
    (encode_decode_current c5 F hF)

theorem encode_injective (na : NecActuality) (X Y : σ → Prop)
    (h : Encode X = Encode Y) : X = Y :=
  (decode_encode na X).symm.trans ((congrArg Decode h).trans (decode_encode na Y))

/-- The meet and relative-negation identities are already closed C identities. -/
theorem encode_meet (X Y : σ → Prop) : Encode (Rel.and X Y) = Rel.and (Encode X) (Encode Y) :=
  funext fun w => funext fun x => propext
    ⟨fun h => ⟨⟨h.1, ((at_and w (X x) (Y x)).1 h.2).1⟩,
      ⟨h.1, ((at_and w (X x) (Y x)).1 h.2).2⟩⟩,
      fun h => ⟨h.1.1, (at_and w (X x) (Y x)).2 ⟨h.1.2, h.2.2⟩⟩⟩

theorem encode_join (X Y : σ → Prop) : Encode (Rel.or X Y) = Rel.or (Encode X) (Encode Y) :=
  funext fun w => funext fun x => propext
    ⟨fun h => ((at_or w (X x) (Y x) h.1).1 h.2).elim
      (fun hp => Or.inl ⟨h.1, hp⟩) (fun hq => Or.inr ⟨h.1, hq⟩),
      fun h => h.elim (fun hp => ⟨hp.1, (at_or w (X x) (Y x) hp.1).2 (Or.inl hp.2)⟩)
        (fun hq => ⟨hq.1, (at_or w (X x) (Y x) hq.1).2 (Or.inr hq.2)⟩)⟩

theorem encode_neg (X : σ → Prop) :
    Encode (Rel.neg X) = Rel.and AtomSupport (Rel.neg (Encode X)) :=
  funext fun w => funext fun x => propext
    ⟨fun h => ⟨h.1, fun hp => (at_neg w (X x) h.1).1 h.2 hp.2⟩,
      fun h => ⟨h.1, (at_neg w (X x) h.1).2 (fun hp => h.2 ⟨h.1, hp⟩)⟩⟩

theorem encode_bottom : Encode (Rel.bot (σ → Prop)) = Rel.bot (Prop → σ → Prop) :=
  funext fun w => funext fun _ => propext
    ⟨fun h => not_at_false w h.1 h.2, False.elim⟩

theorem encode_top : Encode (Rel.top (σ → Prop)) = AtomSupport :=
  funext fun w => funext fun _ => propext
    ⟨And.left, fun hw => ⟨hw, at_true w⟩⟩

end unary

def Representation (σ : Type) [Ty σ] : Prop :=
  (∀ X : σ → Prop, Admissible (Encode X) ∧ Decode (Encode X) = X) ∧
  (∀ F : Prop → σ → Prop, Admissible F → Encode (Decode F) = F)

theorem necessary_plenitude_representation {σ : Type} [Ty σ] :
    NecPlenitude Prop Prop → Representation σ := fun pl =>
  have c5 := necessary_plenitude_r_implies_necessary_distinctness_necessary_r pl
  have na := necessary_plenitude_r_implies_necessary_actuality pl
  ⟨fun X => ⟨encode_admissible c5 X, decode_encode na X⟩,
    fun F hF => encode_decode c5 F hF⟩

end Classicism.Research.WorldRepresentation
