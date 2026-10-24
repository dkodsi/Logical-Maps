import Classicism.Results.Research.AnalyticStructures

/-!
# Rigidification for internal real structures

Formalization begun 23 October 2026. The source argument is the upstream
`c5-and-necessary-rigid-comprehension-imply-second-order-analytic-necessitism`
write-up: connection by Zachary Goodsell; proof by Claude Fable 5.1 (Anthropic),
prompted by Goodsell, after Bacon, Corollary 5.1 (draft 9 October 2025).
These are new Lean proofs, not a change to the source attribution.

All property quantifiers below are internal typed quantifiers. No external
powerset, Atomicity, Actuality, or added axiom is used.
-/

namespace Classicism.Research.Analytic
open Classicism.Paper Classicism.P

variable {σ : Type} [Ty σ]

def Settled (p : Prop) : Prop := (p → □ p) ∧ (¬ p → □ (¬ p))

theorem settled_of_box_persistence
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) (p : Prop)
    (hp : □ (p → □ p)) : Settled p := by
  refine ⟨modal_T _ hp, ?_⟩
  intro hn
  apply (em (◇ p)).elim
  · intro hd
    exact (hn (Proofs.b_dia_box_imp (Proofs.b_of_nd_t (modal_T _ c5)) p
      (dia_mono _ _ hp hd))).elim
  · exact box_not_of_not_dia _

theorem settled_not (p : Prop) (hp : Settled p) : Settled (¬ p) := by
  refine ⟨hp.2, ?_⟩
  intro hn
  have h : p := (em p).elim id (fun hn' => (hn hn').elim)
  exact modal_K _ _ (nec% (fun (h : p) (hn : ¬ p) => hn h)) (hp.1 h)

theorem settled_and (p q : Prop) (hp : Settled p) (hq : Settled q) :
    Settled (p ∧ q) := by
  constructor
  · intro h
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hp : p) (hq : q) => And.intro hp hq)) (hp.1 h.1)) (hq.1 h.2)
  · intro h
    apply (em p).elim
    · intro hpt
      exact modal_K _ _ (nec% (fun (hn : ¬ q) (ha : p ∧ q) => hn ha.2))
        (hq.2 (fun hqt => h ⟨hpt, hqt⟩))
    · intro hpn
      exact modal_K _ _ (nec% (fun (hn : ¬ p) (ha : p ∧ q) => hn ha.1)) (hp.2 hpn)

theorem settled_imp (p q : Prop) (hp : Settled p) (hq : Settled q) :
    Settled (p → q) := by
  constructor
  · intro h
    apply (em p).elim
    · intro hpt
      exact modal_K _ _ (nec% (fun (hq : q) (_ : p) => hq)) (hq.1 (h hpt))
    · intro hpn
      exact modal_K _ _ (nec% (fun (hn : ¬ p) (h : p) => (hn h).elim)) (hp.2 hpn)
  · intro h
    have hpt : p := (em p).elim id (fun hn => (h (fun hp => (hn hp).elim)).elim)
    have hqn : ¬ q := fun hq => h (fun _ => hq)
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hp : p) (hn : ¬ q) (hi : p → q) => hn (hi hp)))
      (hp.1 hpt)) (hq.2 hqn)

theorem settled_or (p q : Prop) (hp : Settled p) (hq : Settled q) :
    Settled (p ∨ q) := by
  constructor
  · intro h
    exact h.elim
      (fun h => modal_K _ _ (nec% (fun (hp : p) => Or.inl hp : p → p ∨ q)) (hp.1 h))
      (fun h => modal_K _ _ (nec% (fun (hq : q) => Or.inr hq : q → p ∨ q)) (hq.1 h))
  · intro h
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hnp : ¬ p) (hnq : ¬ q) (h : p ∨ q) => h.elim hnp hnq))
      (hp.2 (fun hp => h (Or.inl hp)))) (hq.2 (fun hq => h (Or.inr hq)))

theorem settled_all
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (F : σ → Prop) (hF : ∀ x, Settled (F x)) : Settled (∀ x, F x) := by
  constructor
  · intro h
    exact Proofs.bf_of_box_nd_t c5 F (fun x => (hF x).1 (h x))
  · intro h
    have hw : ∃ x, ¬ F x := (em (∃ x, ¬ F x)).elim id fun hn =>
      (h (fun x => (em (F x)).elim id (fun hx => (hn ⟨x, hx⟩).elim))).elim
    obtain ⟨x, hx⟩ := hw
    exact modal_K _ _ (nec% (fun (hx : ¬ F x) (ha : ∀ x, F x) => hx (ha x)))
      ((hF x).2 hx)

theorem settled_exists
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (F : σ → Prop) (hF : ∀ x, Settled (F x)) : Settled (∃ x, F x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact modal_K _ _ (nec% (fun (hx : F x) => (show ∃ x, F x from ⟨x, hx⟩)))
      ((hF x).1 hx)
  · intro h
    exact modal_K _ _ (nec% (fun (hn : ∀ x, ¬ F x) (he : ∃ x, F x) =>
      he.elim fun x hx => hn x hx))
      (Proofs.bf_of_box_nd_t c5 (fun x => ¬ F x)
        (fun x => (hF x).2 (fun hx => h ⟨x, hx⟩)))

theorem settled_eq
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) (x y : σ) : Settled (x = y) :=
  ⟨necessity_of_identity x y, Proofs.nd_of_nd_t (modal_T _ c5) x y⟩

theorem rigid_necessary {ρ : Type} [Rel ρ] (R : ρ) (h : Rigid R) : □ (Rigid R) :=
  modal_K _ _ (nec% (rigid_iff_box_weaklyRigid R).2)
    (modal_four _ ((rigid_iff_box_weaklyRigid R).1 h))

theorem rigid_settled {ρ : Type} [Rel ρ]
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) (R : ρ) : Settled (Rigid R) :=
  settled_of_box_persistence c5 _ (nec% (rigid_necessary R))

theorem membership_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (X : σ → Prop) (hX : Persistent X) (x : σ) : Settled (X x) :=
  settled_of_box_persistence c5 _ (converse_barcan _ hX x)

theorem membership2_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (R : σ → σ → Prop) (hR : Persistent R) (x y : σ) : Settled (R x y) :=
  settled_of_box_persistence c5 _ (converse_barcan _ (converse_barcan _ hR x) y)

theorem membership3_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (R : σ → σ → σ → Prop) (hR : Persistent R) (x y z : σ) : Settled (R x y z) :=
  settled_of_box_persistence c5 _
    (converse_barcan _ (converse_barcan _ (converse_barcan _ hR x) y) z)

theorem rigid_reduction (Q : (σ → Prop) → Prop)
    (rc : RigidComprehension (σ → Prop))
    (coext : ∀ F G : σ → Prop, (∀ x, F x ↔ G x) → Q F → Q G)
    (h : ∀ F, Rigid F → Q F) : ∀ F, Q F := by
  intro F
  obtain ⟨G, hG, he⟩ := rc F
  exact coext G F (fun x => (he x).symm) (h G hG)

/-- The second-order transport step, to be instantiated with the explicit
internal completeness and leastness clauses. Its modal premises are displayed. -/
theorem all_necessary_of_rigid_instances
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension (σ → Prop)))
    (Q : (σ → Prop) → Prop)
    (coext : □ (∀ F G : σ → Prop, (∀ x, F x ↔ G x) → Q F → Q G))
    (stable : ∀ F, Rigid F → Q F → □ (Q F))
    (h : ∀ F, Q F) : □ (∀ F, Q F) := by
  have hr : □ (∀ F, Rigid F → Q F) := Proofs.bf_of_box_nd_t c5 _ fun F =>
    (em (Rigid F)).elim
      (fun hf => modal_K _ _ (nec% (fun (hq : Q F) (_ : Rigid F) => hq))
        (stable F hf (h F)))
      (fun hf => modal_K _ _ (nec% (fun (hn : ¬ Rigid F) (hr : Rigid F) =>
        (hn hr).elim)) ((rigid_settled c5 F).2 hf))
  exact modal_K _ _ (modal_K _ _ (modal_K _ _ (nec% (rigid_reduction Q)) nrc) coext) hr

theorem complete_clause_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (X : σ → Prop) (le : σ → σ → Prop) (F : σ → Prop)
    (hX : Rigid X) (hle : Rigid le) (hF : Rigid F) :
    Settled (CompleteClause X le F) := by
  unfold CompleteClause LeastUpperBound UpperBound
  repeat' first
    | apply settled_and
    | apply settled_imp
    | apply settled_all c5 <;> intro x
    | apply settled_exists c5 <;> intro x
    | exact membership_settled c5 X hX.1 _
    | exact membership_settled c5 F hF.1 _
    | exact membership2_settled c5 le hle.1 _ _

theorem inductive_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (X : σ → Prop) (add : σ → σ → σ → Prop) (zero one : σ)
    (F : σ → Prop) (hX : Rigid X) (hadd : Rigid add) (hF : Rigid F) :
    Settled (Inductive X add zero one F) := by
  unfold Inductive
  repeat' first
    | apply settled_and
    | apply settled_imp
    | apply settled_all c5 <;> intro x
    | exact membership_settled c5 X hX.1 _
    | exact membership_settled c5 F hF.1 _
    | exact membership3_settled c5 add hadd.1 _ _ _

theorem least_clause_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (X : σ → Prop) (add : σ → σ → σ → Prop) (zero one : σ)
    (N F : σ → Prop) (hX : Rigid X) (hadd : Rigid add)
    (hN : Rigid N) (hF : Rigid F) : Settled (LeastClause X add zero one N F) :=
  settled_imp _ _ (inductive_settled c5 X add zero one F hX hadd hF)
    (settled_all c5 _ fun x => settled_imp _ _
      (membership_settled c5 N hN.1 x) (membership_settled c5 F hF.1 x))

/-- Completeness ranges over all internal NONEMPTY bounded subproperties.
The only comprehension premise is its necessary unary instance. -/
theorem complete_nonempty_necessary
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension (σ → Prop)))
    (X : σ → Prop) (le : σ → σ → Prop) (hX : Rigid X) (hle : Rigid le)
    (h : CompleteNonempty X le) : □ (CompleteNonempty X le) :=
  all_necessary_of_rigid_instances c5 nrc (CompleteClause X le)
    (nec% (complete_clause_coext X le))
    (fun F hF => (complete_clause_settled c5 X le F hX hle hF).1) h

theorem least_inductive_necessary
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension (σ → Prop)))
    (X : σ → Prop) (add : σ → σ → σ → Prop) (zero one : σ)
    (N : σ → Prop) (hX : Rigid X) (hadd : Rigid add) (hN : Rigid N)
    (h : LeastInductive X add zero one N) : □ (LeastInductive X add zero one N) := by
  have hi : □ (Inductive X add zero one N) :=
    (inductive_settled c5 X add zero one N hX hadd hN).1 h.1
  have hl : □ (∀ F, LeastClause X add zero one N F) :=
    all_necessary_of_rigid_instances c5 nrc (LeastClause X add zero one N)
      (nec% (least_clause_coext X add zero one N))
      (fun F hF => (least_clause_settled c5 X add zero one N F hX hadd hN hF).1) h.2
  exact modal_K _ _ (modal_K _ _
    (nec% (fun (hi : Inductive X add zero one N)
      (hl : ∀ F, LeastClause X add zero one N F) =>
      (show LeastInductive X add zero one N from ⟨hi, hl⟩))) hi) hl

theorem ordered_field_settled
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (X : σ → Prop) (le : σ → σ → Prop) (add mul : σ → σ → σ → Prop)
    (zero one : σ) (hX : Rigid X) (hle : Rigid le) (hadd : Rigid add)
    (hmul : Rigid mul) : Settled (OrderedField X le add mul zero one) := by
  unfold OrderedField LinearOrder BinaryOperation AdditiveLaws MultiplicativeLaws
    Distributive OrderCompatible
  repeat' first
    | apply settled_and
    | apply settled_or
    | apply settled_not
    | apply settled_imp
    | apply settled_all c5 <;> intro x
    | apply settled_exists c5 <;> intro x
    | exact settled_eq c5 _ _
    | exact membership_settled c5 X hX.1 _
    | exact membership2_settled c5 le hle.1 _ _
    | exact membership3_settled c5 add hadd.1 _ _ _
    | exact membership3_settled c5 mul hmul.1 _ _ _

/-- A rigid real structure remains real necessarily, with completeness and
leastness proved from internal comprehension rather than assumed as stability. -/
theorem real_necessary
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension (σ → Prop)))
    (X : σ → Prop) (le : σ → σ → Prop) (add mul : σ → σ → σ → Prop)
    (zero one : σ) (N : σ → Prop) (hr : RigidStr X le add mul N)
    (h : Real X le add mul zero one N) : □ (Real X le add mul zero one N) := by
  have hf := (ordered_field_settled c5 X le add mul zero one
    hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1).1 h.1
  have hc := complete_nonempty_necessary c5 nrc X le hr.1 hr.2.1 h.2.1
  have hn := least_inductive_necessary c5 nrc X add zero one N
    hr.1 hr.2.2.1 hr.2.2.2.2.1 h.2.2
  exact modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (hf : OrderedField X le add mul zero one)
      (hc : CompleteNonempty X le) (hn : LeastInductive X add zero one N) =>
      (show Real X le add mul zero one N from ⟨hf, hc, hn⟩))) hf) hc) hn

theorem of_possible_of_settled (p : Prop) (hs : Settled p) (hd : ◇ p) : p :=
  (em p).elim id (fun hn => (not_dia_of_box_not p (hs.2 hn) hd).elim)

theorem box_of_possible_box
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) (p : Prop) (hd : ◇ □ p) : □ p :=
  of_possible_of_settled _
    (settled_of_box_persistence c5 _ (nec% (modal_four p))) hd

theorem rigid_of_possible {ρ : Type} [Rel ρ]
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q))) (R : ρ) (hd : ◇ (Rigid R)) : Rigid R :=
  of_possible_of_settled _ (rigid_settled c5 R) hd

/-- Rigidify an existing real structure. Zero and one are retained. -/
theorem rigidify_actual
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension (σ → Prop)))
    (rc2 : RigidComprehension (σ → σ → Prop))
    (rc3 : RigidComprehension (σ → σ → σ → Prop))
    (X : σ → Prop) (le : σ → σ → Prop) (add mul : σ → σ → σ → Prop)
    (zero one : σ) (N : σ → Prop) (h : Real X le add mul zero one N) :
    ∃ Y le' add' mul' M, RigidStr Y le' add' mul' M ∧
      □ (Real Y le' add' mul' zero one M) := by
  obtain ⟨Y, hY, eX⟩ := (modal_T _ nrc) X
  obtain ⟨le', hle, eL⟩ := rc2 le
  obtain ⟨add', hadd, eA⟩ := rc3 add
  obtain ⟨mul', hmul, eM⟩ := rc3 mul
  obtain ⟨M, hN, eN⟩ := (modal_T _ nrc) N
  have hr : RigidStr Y le' add' mul' M :=
    ⟨hY, hle, hadd, hmul, hN,
      fun x y _ _ => Proofs.nd_of_nd_t (modal_T _ c5) x y⟩
  have hy : Real Y le' add' mul' zero one M :=
    real_transport X Y N M le le' add add' mul mul' zero one eX eL eA eM eN h
  exact ⟨Y, le', add', mul', M, hr,
    real_necessary c5 nrc Y le' add' mul' zero one M hr hy⟩

def HasReal (σ : Type) [Ty σ] : Prop :=
  ∃ (X : σ → Prop) (le : σ → σ → Prop) (add mul : σ → σ → σ → Prop)
    (zero one : σ) (N : σ → Prop), Real X le add mul zero one N

def HasRigidReal (σ : Type) [Ty σ] : Prop :=
  ∃ (X : σ → Prop) (le : σ → σ → Prop) (add mul : σ → σ → σ → Prop)
    (zero one : σ) (N : σ → Prop),
    RigidStr X le add mul N ∧ □ (Real X le add mul zero one N)

theorem rigidify_exists
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension (σ → Prop)))
    (rc2 : RigidComprehension (σ → σ → Prop))
    (rc3 : RigidComprehension (σ → σ → σ → Prop))
    (h : HasReal σ) : HasRigidReal σ := by
  obtain ⟨X, le, add, mul, zero, one, N, h⟩ := h
  obtain ⟨Y, le', add', mul', M, hr, hy⟩ :=
    rigidify_actual c5 nrc rc2 rc3 X le add mul zero one N h
  exact ⟨Y, le', add', mul', zero, one, M, hr, hy⟩

theorem rigid_real_of_possible
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (X : σ → Prop) (le : σ → σ → Prop) (add mul : σ → σ → σ → Prop)
    (zero one : σ) (N : σ → Prop)
    (hd : ◇ (RigidStr X le add mul N ∧ □ (Real X le add mul zero one N))) :
    RigidStr X le add mul N ∧ □ (Real X le add mul zero one N) := by
  have hX := rigid_of_possible c5 X (dia_mono _ _
    (nec% (fun (h : RigidStr X le add mul N ∧ □ (Real X le add mul zero one N)) => h.1.1)) hd)
  have hle := rigid_of_possible c5 le (dia_mono _ _
    (nec% (fun (h : RigidStr X le add mul N ∧ □ (Real X le add mul zero one N)) => h.1.2.1)) hd)
  have hadd := rigid_of_possible c5 add (dia_mono _ _
    (nec% (fun (h : RigidStr X le add mul N ∧ □ (Real X le add mul zero one N)) => h.1.2.2.1)) hd)
  have hmul := rigid_of_possible c5 mul (dia_mono _ _
    (nec% (fun (h : RigidStr X le add mul N ∧ □ (Real X le add mul zero one N)) => h.1.2.2.2.1)) hd)
  have hN := rigid_of_possible c5 N (dia_mono _ _
    (nec% (fun (h : RigidStr X le add mul N ∧ □ (Real X le add mul zero one N)) => h.1.2.2.2.2.1)) hd)
  have hreal := box_of_possible_box c5 _ (dia_mono _ _
    (nec% (fun (h : RigidStr X le add mul N ∧ □ (Real X le add mul zero one N)) => h.2)) hd)
  exact ⟨⟨hX, hle, hadd, hmul, hN,
    fun x y _ _ => Proofs.nd_of_nd_t (modal_T _ c5) x y⟩, hreal⟩

/-- First milestone: an ALREADY POSSIBLE internal real structure yields a
rigid actual structure that is necessarily real. All three necessary RC
instances are explicit; no existence of canonical reals is presupposed. -/
theorem rigidify_possible
    (c5 : □ (∀ p q : Prop, p ≠ q → □ (p ≠ q)))
    (nrc : □ (RigidComprehension (σ → Prop)))
    (nrc2 : □ (RigidComprehension (σ → σ → Prop)))
    (nrc3 : □ (RigidComprehension (σ → σ → σ → Prop)))
    (h : ◇ (HasReal σ)) : HasRigidReal σ := by
  have hi : □ (HasReal σ → HasRigidReal σ) :=
    modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (rigidify_exists (σ := σ))) (modal_four _ c5))
      (modal_four _ nrc)) nrc2) nrc3
  have hd : ◇ (HasRigidReal σ) := dia_mono _ _ hi h
  obtain ⟨X, hd⟩ := dia_exists_of_bf (Proofs.bf_of_box_nd_t c5) _ hd
  obtain ⟨le, hd⟩ := dia_exists_of_bf (Proofs.bf_of_box_nd_t c5) _ hd
  obtain ⟨add, hd⟩ := dia_exists_of_bf (Proofs.bf_of_box_nd_t c5) _ hd
  obtain ⟨mul, hd⟩ := dia_exists_of_bf (Proofs.bf_of_box_nd_t c5) _ hd
  obtain ⟨zero, hd⟩ := dia_exists_of_bf (Proofs.bf_of_box_nd_t c5) _ hd
  obtain ⟨one, hd⟩ := dia_exists_of_bf (Proofs.bf_of_box_nd_t c5) _ hd
  obtain ⟨N, hd⟩ := dia_exists_of_bf (Proofs.bf_of_box_nd_t c5) _ hd
  exact ⟨X, le, add, mul, zero, one, N, rigid_real_of_possible c5 X le add mul zero one N hd⟩

end Classicism.Research.Analytic
