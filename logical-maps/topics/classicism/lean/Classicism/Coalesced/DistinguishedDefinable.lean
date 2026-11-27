import Classicism.Coalesced.Definable
import Classicism.Coalesced.Distinguished

/-!
# Definable domains with one distinguished entrance to each component

At the new root, an entity has one closed term as its description on all
distinguished entrances. The interpretation of the constants in each component
is fixed in advance. The current row of a relation may be freely chosen.
-/

namespace Classicism.Meta.Coalesced.DistinguishedDefinable

open CategoryTheory Classicism.Meta.Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
variable (A : ∀ k, Premodel Sig (C k))

def selector : Selector (baseArrows A) A where
  sel ρ _ := {X | ∃ t : Term Sig [] (.rel ρ), ∀ k,
    rootTransport X (dist A k) = (A k).sem (𝟙 _) t .nil}
  shift_mem _ _ m X := by
    rintro ⟨t, ht⟩
    exact ⟨t, fun k => (rootTransport_shift m X (dist A k)).trans (ht k)⟩

abbrev names (σ : Ty) := {c : Sig.Const // Sig.typeOf c = σ}

def nameAtom (σ : Ty) : AtomAction (baseArrows A) A σ :=
  pointAtom A σ (names (Sig := Sig) σ) fun k c =>
    castD (D := (A k).Dom (A k).W₀) c.2 ((A k).I c.1)

noncomputable abbrev action :=
  selAction (nameAtom A .e) (fun i => nameAtom A (.var i)) (selector A)

noncomputable abbrev inclusion :=
  selIncl (nameAtom A .e) (fun i => nameAtom A (.var i)) (selector A)

noncomputable def descriptor : ∀ σ : Ty, (action A).D σ → Term Sig [] σ
  | .e, x => constAt x.1 x.2
  | .var _, x => constAt x.1 x.2
  | .rel _, x => Classical.choose x.2.2

theorem descriptor_at : ∀ (σ : Ty) (x : (action A).D σ) (k : ι),
    (A k).sem (𝟙 _) (descriptor A σ x) .nil =
    (A k).Incl σ _ ((action A).tr σ (dist A k) x)
  | .e, x, k => by
    rw [descriptor, sem_constAt]
    simp [action, nameAtom, pointAtom, selAction, dist]
  | .var _, x, k => by
    rw [descriptor, sem_constAt]
    simp [action, nameAtom, pointAtom, selAction, dist]
  | .rel ρ, x, k =>
    (Classical.choose_spec x.2.2 k).symm.trans
      (incl_relLevel_tr (selector A) ρ _ (dist A k) x).symm

noncomputable def valueAt (c : Sig.Const) : ∀ (σ : Ty), Sig.typeOf c = σ → (action A).D σ
  | .e, h => ⟨c, h⟩
  | .var _, h => ⟨c, h⟩
  | .rel ρ, h =>
    let y := fun k => castD (D := (A k).Dom (A k).W₀) h ((A k).I c)
    ⟨unionTuples A y, fun j => ⟨_, (rootTransport_unionTuples A y j).symm⟩,
      constAt c h, fun k => by
        rw [rootTransport_unionTuples, sem_constAt]
        simp only [Functor.map_id_apply]
        rfl⟩

noncomputable abbrev value (c : Sig.Const) := valueAt A c _ rfl

theorem transportsAt (c : Sig.Const) (k : ι) : ∀ (σ : Ty) (h : Sig.typeOf c = σ),
    (action A).tr σ (dist A k) (valueAt A c σ h) =
    castD (D := (A k).Dom (A k).W₀) h ((A k).I c)
  | .e, h => (A k).inner _ |>.map_id_apply _ _
  | .var _, h => (A k).inner _ |>.map_id_apply _ _
  | .rel ρ, h => by
    apply (A k).incl_injective ρ _
    refine (incl_relLevel_tr (selector A) ρ _ (dist A k) _).trans ?_
    let y := fun j => castD (D := (A j).Dom (A j).W₀) h ((A j).I c)
    exact (rootTransport_unionTuples A y _).trans
      (congrArg ((A k).incl ρ _) (((A k).inner (.rel ρ)).map_id_apply _ (y k)))

theorem transports : TransportsConstants (action A) (value A) :=
  fun c k => transportsAt A c k _ rfl

variable (ne : Nonempty (names (Sig := Sig) .e))

noncomputable abbrev model :=
  (action A).coalescedSum (inclusion A) ne (value A)

private theorem transport_of_root {ρ : RTy}
    (Y : Intension (action A).inner ρ (CoalescedSum.base _)) (k : ι) :
    rootTransport {q | ofRT (nameAtom A .e) (fun i => nameAtom A (.var i)) (selector A) q ∈ Y}
      (dist A k) = (action A).transport (k := k) (V := (A k).W₀) (dist A k) Y := by
  ext ⟨U, a, j⟩
  rfl

theorem isModel (M : ∀ k, (A k).IsModel) : (model A ne).IsModel := by
  have hQ : (action A).ComponentsAreModels (value A) := componentsAreModels (transports A) M
  apply ((action A).isModel_iff (inclusion A) ne (value A)).2
  refine ⟨hQ, (rootClosed_iff_selected _ _ _ ne (value A) hQ).2 ?_⟩
  intro m Γ ρ t g
  let sub : Sub Sig Γ [] := fun σ v => descriptor A σ (g.get v)
  refine ⟨t.subst sub, fun k => ?_⟩
  refine (transport_of_root A _ k).trans ?_
  have hp := (model A ne).sem_push (CoalescedSum.endo (baseArrows A) m) t g
    (CoalescedSum.arr (baseArrows A) (dist A k))
  refine (congrArg (action A).compI hp.symm).trans ?_
  refine ((action A).sem_arr (inclusion A) ne (value A) (dist A k) t _).trans ?_
  refine ((A k).rebase_sem_congr (funext fun c => transports A c k) (𝟙 _) t _).trans ?_
  rw [(A k).sem_subst (M k)]
  congr 1
  apply IEnv.ext
  intro σ v
  apply (A k).Incl_injective σ _
  refine Eq.trans ?_ (((A k).Incl_subEnv_get (M k) _ _ _ v).trans (descriptor_at A σ (g.get v) k)).symm
  exact congrArg ((A k).Incl σ _) (IEnv.get_map _ v g)

end Classicism.Meta.Coalesced.DistinguishedDefinable
