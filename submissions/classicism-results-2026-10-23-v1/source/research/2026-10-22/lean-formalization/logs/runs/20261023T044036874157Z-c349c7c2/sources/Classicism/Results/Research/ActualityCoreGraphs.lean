import Classicism.Results.Research.ActualityCore

/-!
# Supported graphs and represented quantifier transfer

Direct sources: `research/2026-10-22/notes/actuality-world-slice-core.md`,
§§3–4, 7–8; `notes/gallin-extensional-core.md`, §§3–5 (original research,
`misc`, 22 October 2026, unpaginated).

These are object-language shallow C proofs. Graphs may have individual outputs;
no operation of type `e → e` is formed. All family/predicate quantifiers are
admitted higher-order quantifiers. This module supplies current graph and
predicate interfaces, not the missing recursive interpretation of all syntax.
-/

namespace Classicism.Research.ActualityCore
open Classicism.Paper Classicism.P

section graphs
variable {σ ρ κ υ : Type} [Ty σ] [Ty ρ] [Ty κ] [Ty υ]

def Graph (w : Prop) (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) :
    σ → ρ → Prop := fun x y => w ∧ D x ∧ R y ∧ G x y

def GraphAgreement (D : σ → Prop) (R : ρ → Prop) (G H : σ → ρ → Prop) : Prop :=
  ∀ x y, D x → R y → (G x y ↔ H x y)

def SerialOn (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) : Prop :=
  ∀ x, D x → ∃ y, R y ∧ G x y

def SingleValuedOn (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) : Prop :=
  ∀ x y z, D x → R y → R z → G x y → G x z → y = z

def InjectiveOn (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) : Prop :=
  ∀ x y z, D x → D y → R z → G x z → G y z → x = y

def SurjectiveOn (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) : Prop :=
  ∀ y, R y → ∃ x, D x ∧ G x y

theorem graph_supported (w : Prop) (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) :
    Supported w (Graph w D R G) :=
  le_of_box_incl (nec% (fun x y (h : Graph w D R G x y) => h.1))

theorem graph_current (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) :
    GraphAgreement D R (Graph w D R G) G :=
  fun _ _ hx hy => ⟨fun h => h.2.2.2, fun h => ⟨hw.1, hx, hy, h⟩⟩

theorem graph_kernel (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (R : ρ → Prop) (G H : σ → ρ → Prop) :
    Graph w D R G = Graph w D R H ↔ GraphAgreement D R G H := by
  constructor
  · intro h x y hx hy
    have he := congrFun (congrFun h x) y
    exact ⟨fun hg => (Eq.mp he ⟨hw.1, hx, hy, hg⟩).2.2.2,
      fun hh => (Eq.mpr he ⟨hw.1, hx, hy, hh⟩).2.2.2⟩
  · intro h
    exact localized_eq w hw _ _ (graph_supported w D R G) (graph_supported w D R H)
      (fun x y => ⟨fun hg => ⟨hg.1, hg.2.1, hg.2.2.1,
        (h x y hg.2.1 hg.2.2.1).1 hg.2.2.2⟩,
        fun hh => ⟨hh.1, hh.2.1, hh.2.2.1,
          (h x y hh.2.1 hh.2.2.1).2 hh.2.2.2⟩⟩)

theorem serial_agreement (D : σ → Prop) (R : ρ → Prop) (G H : σ → ρ → Prop)
    (h : GraphAgreement D R G H) : SerialOn D R G ↔ SerialOn D R H :=
  ⟨fun hg x hx => (hg x hx).elim fun y hy => ⟨y, hy.1, (h x y hx hy.1).1 hy.2⟩,
    fun hh x hx => (hh x hx).elim fun y hy => ⟨y, hy.1, (h x y hx hy.1).2 hy.2⟩⟩

theorem singleValued_agreement (D : σ → Prop) (R : ρ → Prop) (G H : σ → ρ → Prop)
    (h : GraphAgreement D R G H) : SingleValuedOn D R G ↔ SingleValuedOn D R H :=
  ⟨fun hg x y z hx hy hz hxy hxz => hg x y z hx hy hz
      ((h x y hx hy).2 hxy) ((h x z hx hz).2 hxz),
    fun hh x y z hx hy hz hxy hxz => hh x y z hx hy hz
      ((h x y hx hy).1 hxy) ((h x z hx hz).1 hxz)⟩

theorem injective_agreement (D : σ → Prop) (R : ρ → Prop) (G H : σ → ρ → Prop)
    (h : GraphAgreement D R G H) : InjectiveOn D R G ↔ InjectiveOn D R H :=
  ⟨fun hg x y z hx hy hz hxy hyz => hg x y z hx hy hz
      ((h x z hx hz).2 hxy) ((h y z hy hz).2 hyz),
    fun hh x y z hx hy hz hxy hyz => hh x y z hx hy hz
      ((h x z hx hz).1 hxy) ((h y z hy hz).1 hyz)⟩

theorem surjective_agreement (D : σ → Prop) (R : ρ → Prop) (G H : σ → ρ → Prop)
    (h : GraphAgreement D R G H) : SurjectiveOn D R G ↔ SurjectiveOn D R H :=
  ⟨fun hg y hy => (hg y hy).elim fun x hx => ⟨x, hx.1, (h x y hx.1 hy).1 hx.2⟩,
    fun hh y hy => (hh y hy).elim fun x hx => ⟨x, hx.1, (h x y hx.1 hy).2 hx.2⟩⟩

theorem graph_preserves_function (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) :
    (SerialOn D R (Graph w D R G) ∧ SingleValuedOn D R (Graph w D R G)) ↔
      (SerialOn D R G ∧ SingleValuedOn D R G) :=
  ⟨fun h => ⟨(serial_agreement D R _ G (graph_current w hw D R G)).1 h.1,
      (singleValued_agreement D R _ G (graph_current w hw D R G)).1 h.2⟩,
    fun h => ⟨(serial_agreement D R _ G (graph_current w hw D R G)).2 h.1,
      (singleValued_agreement D R _ G (graph_current w hw D R G)).2 h.2⟩⟩

def Compose (R : ρ → Prop) (G : σ → ρ → Prop) (H : ρ → κ → Prop) :
    σ → κ → Prop := fun x z => ∃ y, R y ∧ G x y ∧ H y z

theorem compose_serial (D : σ → Prop) (R : ρ → Prop) (S : κ → Prop)
    (G : σ → ρ → Prop) (H : ρ → κ → Prop)
    (hG : SerialOn D R G) (hH : SerialOn R S H) : SerialOn D S (Compose R G H) :=
  fun x hx => (hG x hx).elim fun y hy => (hH y hy.1).elim fun z hz =>
    ⟨z, hz.1, y, hy.1, hy.2, hz.2⟩

theorem compose_singleValued (D : σ → Prop) (R : ρ → Prop) (S : κ → Prop)
    (G : σ → ρ → Prop) (H : ρ → κ → Prop)
    (hG : SingleValuedOn D R G) (hH : SingleValuedOn R S H) :
    SingleValuedOn D S (Compose R G H) := by
  intro x y z hx hy hz hxy hxz
  obtain ⟨a, ha, hxa, hay⟩ := hxy
  obtain ⟨b, hb, hxb, hbz⟩ := hxz
  have hab := hG x a b hx ha hb hxa hxb
  exact hH a y z ha hy hz hay (hab.symm ▸ hbz)

theorem compose_injective (D : σ → Prop) (R : ρ → Prop) (S : κ → Prop)
    (G : σ → ρ → Prop) (H : ρ → κ → Prop)
    (hG : InjectiveOn D R G) (hH : InjectiveOn R S H) :
    InjectiveOn D S (Compose R G H) := by
  intro x y z hx hy hz hxz hyz
  obtain ⟨a, ha, hxa, haz⟩ := hxz
  obtain ⟨b, hb, hyb, hbz⟩ := hyz
  have hab := hH a b z ha hb hz haz hbz
  exact hG x y a hx hy ha hxa (hab.symm ▸ hyb)

theorem compose_surjective (D : σ → Prop) (R : ρ → Prop) (S : κ → Prop)
    (G : σ → ρ → Prop) (H : ρ → κ → Prop)
    (hG : SurjectiveOn D R G) (hH : SurjectiveOn R S H) :
    SurjectiveOn D S (Compose R G H) :=
  fun z hz => (hH z hz).elim fun y hy => (hG y hy.1).elim fun x hx =>
    ⟨x, hx.1, y, hy.1, hx.2, hy.2⟩

theorem compose_assoc (R : ρ → Prop) (S : κ → Prop)
    (G : σ → ρ → Prop) (H : ρ → κ → Prop) (K : κ → υ → Prop) :
    Compose S (Compose R G H) K = Compose R G (Compose S H K) :=
  funext fun x => funext fun z => propext
    ⟨fun h => h.elim fun b hb => hb.2.1.elim fun a ha =>
      ⟨a, ha.1, ha.2.1, b, hb.1, ha.2.2, hb.2.2⟩,
      fun h => h.elim fun a ha => ha.2.2.elim fun b hb =>
        ⟨b, hb.1, ⟨a, ha.1, ha.2.1, hb.2.1⟩, hb.2.2⟩⟩

theorem compose_normalized (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (R : ρ → Prop) (S : κ → Prop)
    (G : σ → ρ → Prop) (H : ρ → κ → Prop) :
    Graph w D S (Compose R (Graph w D R G) (Graph w R S H)) =
      Graph w D S (Compose R G H) :=
  (graph_kernel w hw D S _ _).2 fun x z hx hz =>
    ⟨fun h => h.elim fun y hy => ⟨y, hy.1, hy.2.1.2.2.2, hy.2.2.2.2.2⟩,
      fun h => h.elim fun y hy => ⟨y, hy.1, ⟨hw.1, hx, hy.1, hy.2.1⟩,
        ⟨hw.1, hy.1, hz, hy.2.2⟩⟩⟩

theorem compose_left_identity (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) :
    Graph w D R (Compose D (Equality w D) G) = Graph w D R G :=
  (graph_kernel w hw D R _ _).2 fun x y hx _ =>
    ⟨fun h => h.elim fun z hz => hz.2.1.2.2.2.symm ▸ hz.2.2,
      fun h => ⟨x, hx, ⟨hw.1, hx, hx, rfl⟩, h⟩⟩

theorem compose_right_identity (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop) :
    Graph w D R (Compose R G (Equality w R)) = Graph w D R G :=
  (graph_kernel w hw D R _ _).2 fun x y _ hy =>
    ⟨fun h => h.elim fun z hz => hz.2.2.2.2.2 ▸ hz.2.1,
      fun h => ⟨y, hy, h, hw.1, hy, hy, rfl⟩⟩

end graphs

/-! ## Realizing graph-selected relational outputs in the supported core -/
section realization
variable {σ ρ : Type} [Ty σ] [Ty ρ]

def Realize (w : Prop) (D : σ → Prop) (A : ρ → Prop)
    (G : σ → (ρ → Prop) → Prop) : σ → ρ → Prop :=
  fun x z => w ∧ D x ∧ A z ∧ ∃ Y : ρ → Prop, Domain w A Y ∧ G x Y ∧ Y z

theorem realize_supported (w : Prop) (D : σ → Prop) (A : ρ → Prop)
    (G : σ → (ρ → Prop) → Prop) (x : σ) : Supported w (Realize w D A G x) :=
  le_of_box_incl (nec% (fun (z : ρ) (h : Realize w D A G x z) => h.1))

theorem realize_below (w : Prop) (D : σ → Prop) (A : ρ → Prop)
    (G : σ → (ρ → Prop) → Prop) (x : σ) : Realize w D A G x ≤ A :=
  le_of_box_incl (nec% (fun (z : ρ) (h : Realize w D A G x z) => h.2.2.1))

theorem realize_selected (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (A : ρ → Prop) (hA : Supported w A)
    (G : σ → (ρ → Prop) → Prop) (x : σ) (Y : ρ → Prop)
    (hx : D x) (hY : Domain w A Y) (hG : G x Y)
    (hu : ∀ Z : ρ → Prop, Domain w A Z → G x Z → Z = Y) :
    Realize w D A G x = Y :=
  localized_eq w hw _ _ (realize_supported w D A G x)
    (le_trans_rel _ _ _ hY.2 hA)
    (fun z => ⟨fun h => h.2.2.2.elim fun Z hZ => (hu Z hZ.1 hZ.2.1) ▸ hZ.2.2,
      fun h => ⟨hw.1, hx, incl_of_le hY.2 z h, Y, hY, hG, h⟩⟩)

/-- Literal operation values follow from graph functionality in the local core.
Only the displayed relational-output type is claimed here. -/
theorem realize_functional_graph (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (A : ρ → Prop) (hA : Supported w A)
    (G : σ → (ρ → Prop) → Prop)
    (hs : SerialOn D (Domain w A) G)
    (hu : SingleValuedOn D (Domain w A) G) :
    ∀ x, D x → Domain w A (Realize w D A G x) ∧ G x (Realize w D A G x) := by
  intro x hx
  obtain ⟨Y, hY, hGY⟩ := hs x hx
  have he := realize_selected w hw D A hA G x Y hx hY hGY
    (fun Z hZ hGZ => hu x Z Y hx hZ hY hGZ hGY)
  exact ⟨⟨hw.1, realize_below w D A G x⟩, he.symm ▸ hGY⟩

end realization

/-! ## Quantifying over precisely the represented current extensions -/
section predicates
variable {σ : Type} [Ty σ]

def BaseSupport (w : Prop) (D : σ → Prop) : σ → Prop := fun x => w ∧ D x
def Predicate (w : Prop) (D P : σ → Prop) : σ → Prop := Cut (BaseSupport w D) P

theorem predicate_current (w : Prop) (hw : ActualWorld w) (D P : σ → Prop) :
    ∀ x, D x → (Predicate w D P x ↔ P x) :=
  fun _ hx => ⟨And.right, fun hp => ⟨⟨hw.1, hx⟩, hp⟩⟩

def ExtensionInvariant (D : σ → Prop) (H : (σ → Prop) → Prop) : Prop :=
  ∀ P Q : σ → Prop, (∀ x, D x → (P x ↔ Q x)) → (H P ↔ H Q)

theorem predicate_forall_transfer (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (H : (σ → Prop) → Prop) (hi : ExtensionInvariant D H) :
    (∀ P : σ → Prop, H P) ↔
      (∀ P : σ → Prop, P ≤ BaseSupport w D → H P) :=
  ⟨fun h P _ => h P,
    fun h P => (hi (Predicate w D P) P (predicate_current w hw D P)).1
      (h (Predicate w D P) (cut_le (BaseSupport w D) P))⟩

theorem predicate_exists_transfer (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (H : (σ → Prop) → Prop) (hi : ExtensionInvariant D H) :
    (∃ P : σ → Prop, H P) ↔
      (∃ P : σ → Prop, P ≤ BaseSupport w D ∧ H P) :=
  ⟨fun h => h.elim fun P hp => ⟨Predicate w D P, cut_le (BaseSupport w D) P,
    (hi (Predicate w D P) P (predicate_current w hw D P)).2 hp⟩,
    fun h => h.elim fun P hp => ⟨P, hp.2⟩⟩

def HasMinimal (D : σ → Prop) (G : σ → σ → Prop) (P : σ → Prop) : Prop :=
  (∃ x, D x ∧ P x) → ∃ m, D m ∧ P m ∧ ∀ y, D y → P y → ¬ G y m

def RepresentedWellFounded (D : σ → Prop) (G : σ → σ → Prop) : Prop :=
  ∀ P : σ → Prop, HasMinimal D G P

theorem hasMinimal_invariant (D : σ → Prop) (G : σ → σ → Prop) :
    ExtensionInvariant D (HasMinimal D G) := by
  intro P Q he
  constructor
  · intro h hQ
    obtain ⟨x, hx, hqx⟩ := hQ
    obtain ⟨m, hm, hpm, hmin⟩ := h ⟨x, hx, (he x hx).2 hqx⟩
    exact ⟨m, hm, (he m hm).1 hpm,
      fun y hy hqy => hmin y hy ((he y hy).2 hqy)⟩
  · intro h hP
    obtain ⟨x, hx, hpx⟩ := hP
    obtain ⟨m, hm, hqm, hmin⟩ := h ⟨x, hx, (he x hx).1 hpx⟩
    exact ⟨m, hm, (he m hm).2 hqm,
      fun y hy hpy => hmin y hy ((he y hy).1 hpy)⟩

theorem represented_wellFounded_transfer (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (G : σ → σ → Prop) :
    RepresentedWellFounded D G ↔
      ∀ P : σ → Prop, P ≤ BaseSupport w D → HasMinimal D G P :=
  predicate_forall_transfer w hw D (HasMinimal D G) (hasMinimal_invariant D G)

end predicates

def GraphNormalization (σ ρ : Type) [Ty σ] [Ty ρ] : Prop :=
  ∀ (w : Prop) (D : σ → Prop) (R : ρ → Prop) (G : σ → ρ → Prop),
    ActualWorld w →
      ((SerialOn D R (Graph w D R G) ∧ SingleValuedOn D R (Graph w D R G)) ↔
        (SerialOn D R G ∧ SingleValuedOn D R G)) ∧
      (InjectiveOn D R (Graph w D R G) ↔ InjectiveOn D R G) ∧
      (SurjectiveOn D R (Graph w D R G) ↔ SurjectiveOn D R G)

theorem graph_normalization_law {σ ρ : Type} [Ty σ] [Ty ρ] : GraphNormalization σ ρ :=
  fun w D R G hw => ⟨graph_preserves_function w hw D R G,
    injective_agreement D R _ G (graph_current w hw D R G),
    surjective_agreement D R _ G (graph_current w hw D R G)⟩

def GraphRealization (σ ρ : Type) [Ty σ] [Ty ρ] : Prop :=
  ∀ (w : Prop) (D : σ → Prop) (A : ρ → Prop) (G : σ → (ρ → Prop) → Prop),
    ActualWorld w → Supported w A → SerialOn D (Domain w A) G →
      SingleValuedOn D (Domain w A) G →
        ∀ x, D x → Domain w A (Realize w D A G x) ∧ G x (Realize w D A G x)

theorem graph_realization_law {σ ρ : Type} [Ty σ] [Ty ρ] : GraphRealization σ ρ :=
  fun w D A G hw hA hs hu => realize_functional_graph w hw D A hA G hs hu

def PredicateTransfer (σ : Type) [Ty σ] : Prop :=
  ∀ (w : Prop) (D : σ → Prop) (H : (σ → Prop) → Prop),
    ActualWorld w → ExtensionInvariant D H →
      ((∀ P : σ → Prop, H P) ↔
        (∀ P : σ → Prop, P ≤ BaseSupport w D → H P)) ∧
      ((∃ P : σ → Prop, H P) ↔
        (∃ P : σ → Prop, P ≤ BaseSupport w D ∧ H P))

theorem predicate_transfer_law {σ : Type} [Ty σ] : PredicateTransfer σ :=
  fun w D H hw hi => ⟨predicate_forall_transfer w hw D H hi,
    predicate_exists_transfer w hw D H hi⟩

end Classicism.Research.ActualityCore
