import Classicism.Semantics.IdeallyFull

/-!
# External support controls for actual typed intensional models

An extension of the pinning proof in `IdeallyFull`: support is independent of
the typed individual action. The model and its recursive domains are built
below; no field asserts term closure or existence of a countermodel.
The controls are instantiated concretely in `CentralSupportedProduct`.
The source proof strategy is Appendix D, as formalized in `IdeallyFull`;
the external-support extension is new research, 22 October 2026.
-/

namespace Classicism.Meta.Intensional.Central
open CategoryTheory

variable {C : Type} [SmallCategory C]

structure Control (C : Type) [SmallCategory C] where
  Key : C → Type
  zero : ∀ W, Key W
  join : ∀ {W}, Key W → Key W → Key W
  Agree : ∀ {W V}, Key W → (W ⟶ V) → (W ⟶ V) → Prop
  join_left : ∀ {W V} (s t : Key W) (h i : W ⟶ V), Agree (join s t) h i → Agree s h i
  join_right : ∀ {W V} (s t : Key W) (h i : W ⟶ V), Agree (join s t) h i → Agree t h i
  push : ∀ {W V}, (W ⟶ V) → Key W → Key V
  comp : ∀ {W V U} (h : W ⟶ V) (s : Key W) (i j : V ⟶ U),
    Agree (push h s) i j → Agree s (h ≫ i) (h ≫ j)

variable (Q : Control C)

def SupportedBy (F : C ⥤ Type) {W : C} (s : Q.Key W) (x : F.obj W) : Prop :=
  ∀ (V : C) (h i : W ⟶ V), Q.Agree s h i → F.map h x = F.map i x

def Supported (F : C ⥤ Type) {W : C} (x : F.obj W) : Prop :=
  ∃ s : Q.Key W, SupportedBy Q F s x

theorem supported_map {F : C ⥤ Type} {W V : C} {x : F.obj W}
    (hx : Supported Q F x) (h : W ⟶ V) : Supported Q F (F.map h x) := by
  obtain ⟨s, hs⟩ := hx
  refine ⟨Q.push h s, fun U i j hij => ?_⟩
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
  exact hs U (h ≫ i) (h ≫ j) (Q.comp h s i j hij)

abbrev supportedAction (F : C ⥤ Type) : C ⥤ Type where
  obj W := {x : F.obj W // Supported Q F x}
  map h := TypeCat.ofHom fun x => ⟨F.map h x.1, supported_map Q x.2 h⟩
  map_id W := by ext ⟨x, hx⟩ : 3; simp
  map_comp h i := by ext ⟨x, hx⟩ : 3; simp

variable (De : C ⥤ Type)

noncomputable abbrev Domain (σ : Ty) : C ⥤ Type :=
  @Ty.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De
    (fun _ ih => supportedAction Q (intensionAction ih)) (fun _ => De)
    pointAction (fun _ _ ihσ ihρ => prodAction ihσ ihρ) σ

noncomputable abbrev Arguments (ρ : RTy) : C ⥤ Type :=
  @RTy.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De
    (fun _ ih => supportedAction Q (intensionAction ih)) (fun _ => De)
    pointAction (fun _ _ ihσ ihρ => prodAction ihσ ihρ) ρ

abbrev RelDomain (ρ : RTy) : C ⥤ Type :=
  supportedAction Q (intensionAction (Arguments Q De ρ))

abbrev Raw (ρ : RTy) (W : C) : Type :=
  Set (Σ V : C, (Arguments Q De ρ).obj V × (W ⟶ V))

def args : ∀ (ρ : RTy) (V : C), Args (Domain Q De) ρ V → (Arguments Q De ρ).obj V
  | .t, _, a => a
  | .arr _ ρ, V, a => (a.1, args ρ V a.2)

def args' : ∀ (ρ : RTy) (V : C), (Arguments Q De ρ).obj V → Args (Domain Q De) ρ V
  | .t, _, a => a
  | .arr _ ρ, V, a => (a.1, args' ρ V a.2)

theorem args_args' : ∀ (ρ : RTy) (V : C) (a : (Arguments Q De ρ).obj V),
    args Q De ρ V (args' Q De ρ V a) = a
  | .t, _, _ => rfl
  | .arr _ ρ, V, a => by
    change (a.1, args Q De ρ V (args' Q De ρ V a.2)) = a
    rw [args_args' ρ V a.2]

theorem args'_args : ∀ (ρ : RTy) (V : C) (a : Args (Domain Q De) ρ V),
    args' Q De ρ V (args Q De ρ V a) = a
  | .t, _, _ => rfl
  | .arr _ ρ, V, a => by
    change (a.1, args' Q De ρ V (args Q De ρ V a.2)) = a
    rw [args'_args ρ V a.2]

def read (ρ : RTy) (W : C) (A : Raw Q De ρ W) : Intension (Domain Q De) ρ W :=
  {p | (⟨p.1, args Q De ρ p.1 p.2.1, p.2.2⟩ : Σ V : C,
    (Arguments Q De ρ).obj V × (W ⟶ V)) ∈ A}

def unread (ρ : RTy) (W : C) (F : Intension (Domain Q De) ρ W) : Raw Q De ρ W :=
  {p | (⟨p.1, args' Q De ρ p.1 p.2.1, p.2.2⟩ : Tuple (Domain Q De) ρ W) ∈ F}

theorem read_unread (ρ : RTy) (W : C) (F : Intension (Domain Q De) ρ W) :
    read Q De ρ W (unread Q De ρ W F) = F := by
  ext ⟨V, a, i⟩
  simp [read, unread, args'_args]

theorem unread_read (ρ : RTy) (W : C) (A : Raw Q De ρ W) :
    unread Q De ρ W (read Q De ρ W A) = A := by
  ext ⟨V, a, i⟩
  simp [read, unread, args_args']

theorem read_map (ρ : RTy) {W V : C} (h : W ⟶ V) (A : Raw Q De ρ W) :
    read Q De ρ V ((intensionAction (Arguments Q De ρ)).map h A) =
      Intension.map (Domain Q De) h (read Q De ρ W A) := by
  ext ⟨U, a, i⟩
  exact Iff.rfl

theorem unread_map (ρ : RTy) {W V : C} (h : W ⟶ V) (F : Intension (Domain Q De) ρ W) :
    unread Q De ρ V (Intension.map (Domain Q De) h F) =
      (intensionAction (Arguments Q De ρ)).map h (unread Q De ρ W F) := by
  ext ⟨U, a, i⟩
  exact Iff.rfl

def incl (ρ : RTy) (W : C) (A : (RelDomain Q De ρ).obj W) : Intension (Domain Q De) ρ W :=
  read Q De ρ W A.1

theorem incl_map (ρ : RTy) {W V : C} (h : W ⟶ V) (A : (RelDomain Q De ρ).obj W) :
    incl Q De ρ V ((RelDomain Q De ρ).map h A) =
      Intension.map (Domain Q De) h (incl Q De ρ W A) := read_map Q De ρ h A.1

theorem incl_injective (ρ : RTy) (W : C) : Function.Injective (incl Q De ρ W) := by
  intro A B e
  apply Subtype.ext
  have h := congrArg (unread Q De ρ W) e
  simpa only [incl, unread_read] using h

theorem range_incl (ρ : RTy) (W : C) (F : Intension (Domain Q De) ρ W) :
    F ∈ Set.range (incl Q De ρ W) ↔
      ∃ s : Q.Key W, ∀ (V : C) (h i : W ⟶ V), Q.Agree s h i →
        Intension.map (Domain Q De) h F = Intension.map (Domain Q De) i F := by
  constructor
  · rintro ⟨⟨A, s, hs⟩, rfl⟩
    refine ⟨s, fun V h i hi => ?_⟩
    change Intension.map (Domain Q De) h (read Q De ρ W A) =
      Intension.map (Domain Q De) i (read Q De ρ W A)
    rw [← read_map, ← read_map, hs V h i hi]
  · rintro ⟨s, hs⟩
    refine ⟨⟨unread Q De ρ W F, s, fun V h i hi => ?_⟩, read_unread Q De ρ W F⟩
    rw [← unread_map, ← unread_map, hs V h i hi]

noncomputable def model {Sig : Signature} (W₀ : C)
    (hne : ∀ W, Nonempty (De.obj W))
    (I : ∀ c : Sig.Const, (Domain Q De (Sig.typeOf c)).obj W₀) : Premodel Sig C where
  W₀ := W₀
  inner := Domain Q De
  nonempty_e := hne
  incl := incl Q De
  incl_map := incl_map Q De
  incl_injective := incl_injective Q De
  I := I

section closure
variable {Sig : Signature} (B : Premodel Sig C)

def SupportedO (σ : Ty) {W : C} (s : Q.Key W) (x : Outer B.inner σ W) : Prop :=
  ∀ (V : C) (h i : W ⟶ V), Q.Agree s h i →
    Outer.map B.inner σ h x = Outer.map B.inner σ i x

theorem supportedO_left {σ : Ty} {W : C} {s : Q.Key W} (t : Q.Key W)
    {x : Outer B.inner σ W} (hx : SupportedO Q B σ s x) : SupportedO Q B σ (Q.join s t) x :=
  fun V h i hi => hx V h i (Q.join_left s t h i hi)

theorem supportedO_right {σ : Ty} {W : C} (s : Q.Key W) {t : Q.Key W}
    {x : Outer B.inner σ W} (hx : SupportedO Q B σ t x) : SupportedO Q B σ (Q.join s t) x :=
  fun V h i hi => hx V h i (Q.join_right s t h i hi)

theorem supportedO_incl_iff (σ : Ty) {W : C} (s : Q.Key W) (x : B.Dom W σ) :
    SupportedO Q B σ s (B.Incl σ W x) ↔ SupportedBy Q (B.inner σ) s x := by
  constructor
  · intro hs V h i hi
    apply B.Incl_injective
    rw [B.Incl_map, B.Incl_map]
    exact hs V h i hi
  · intro hs V h i hi
    rw [← B.Incl_map, ← B.Incl_map, hs V h i hi]

theorem supportedO_apply {σ : Ty} {ρ : RTy} {W : C} {s : Q.Key W}
    {F : Intension B.inner (.arr σ ρ) W} {x : Outer B.inner σ W}
    (hF : SupportedO Q B (.rel (.arr σ ρ)) s F) (hx : SupportedO Q B σ s x) :
    SupportedO Q B (.rel ρ) s (B.apply F x) := by
  intro V h i hi
  rw [Outer.map_rel, Outer.map_rel, ← B.apply_map, ← B.apply_map, hx V h i hi]
  have e := hF V h i hi
  rw [Outer.map_rel, Outer.map_rel] at e
  rw [e]

theorem push_eq {Γ : Ctx} {W V : C} (g : IEnv (B.Dom W) Γ) (s : Q.Key W)
    (hg : ∀ τ (v : Var Γ τ), SupportedO Q B τ s (B.Incl τ W (g.get v)))
    {h i : W ⟶ V} (hi : Q.Agree s h i) : B.push h g = B.push i g := by
  apply IEnv.ext
  intro τ v
  simp only [Premodel.push, IEnv.get_map]
  exact (supportedO_incl_iff Q B τ s (g.get v)).1 (hg τ v) V h i hi

/-- Dependence is on whole transported parameters, including constants, not
on the supports of all objects quantified over by a term. -/
theorem sem_supported : ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : B.W₀ ⟶ W)
    (t : Term Sig Γ σ) (g : IEnv (B.Dom W) Γ) (s : Q.Key W),
    (∀ τ (v : Var Γ τ), SupportedO Q B τ s (B.Incl τ W (g.get v))) →
    (∀ c ∈ t.consts, SupportedO Q B _ s (B.Incl _ W ((B.inner _).map h (B.I c)))) →
    SupportedO Q B σ s (B.sem h t g)
  | _, _, _, _, .var v, g, s, hg, _ => hg _ v
  | _, _, _, _, .const c, _, s, _, hc => hc c (Set.mem_singleton c)
  | _, _, _, h, .app f a, g, s, hg, hc =>
    supportedO_apply Q B
      (sem_supported h f g s hg (fun c hc' => hc c (Term.consts_app_left f a hc')))
      (sem_supported h a g s hg (fun c hc' => hc c (Term.consts_app_right f a hc')))
  | _, _, _, h, .lam b, g, s, hg, hc => by
    intro V h' i' hi
    rw [← B.sem_push, ← B.sem_push, push_eq Q B g s hg hi]
    apply B.sem_congr_const
    intro c hc'
    rw [Functor.map_comp, Functor.map_comp]
    exact (supportedO_incl_iff Q B _ s _).1 (hc c hc') V h' i' hi
  | _, _, _, _, .and, _, _, _, _ | _, _, _, _, .or, _, _, _, _
  | _, _, _, _, .not, _, _, _, _ | _, _, _, _, .all _, _, _, _, _
  | _, _, _, _, .ex _, _, _, _, _ | _, _, _, _, .eq _, _, _, _, _
  | _, _, _, _, .constR _, _, _, _, _ | _, _, _, _, .negR _, _, _, _, _
  | _, _, _, _, .andR _, _, _, _, _ | _, _, _, _, .orR _, _, _, _, _
  | _, _, _, _, .coextR _, _, _, _, _ | _, _, _, _, .boxR _, _, _, _, _
  | _, _, _, _, .inclR _, _, _, _, _ => fun _ _ _ _ => rfl

theorem env_supported
    (hall : ∀ (σ : Ty) (W : C) (x : B.Dom W σ),
      ∃ s : Q.Key W, SupportedO Q B σ s (B.Incl σ W x)) :
    ∀ {Γ : Ctx} {W : C} (g : IEnv (B.Dom W) Γ),
      ∃ s : Q.Key W, ∀ τ (v : Var Γ τ), SupportedO Q B τ s (B.Incl τ W (g.get v))
  | _, W, .nil => ⟨Q.zero W, fun _ v => nomatch v⟩
  | _, _, .cons x g => by
    obtain ⟨s, hs⟩ := env_supported hall g
    obtain ⟨t, ht⟩ := hall _ _ x
    refine ⟨Q.join s t, fun τ v => ?_⟩
    cases v with
    | zero => exact supportedO_right Q B s ht
    | succ v => exact supportedO_left Q B t (hs _ v)

theorem constants_supported
    (hall : ∀ (σ : Ty) (W : C) (x : B.Dom W σ),
      ∃ s : Q.Key W, SupportedO Q B σ s (B.Incl σ W x))
    {Γ : Ctx} {σ : Ty} {W : C} (h : B.W₀ ⟶ W) (t : Term Sig Γ σ) :
    ∃ s : Q.Key W, ∀ c ∈ t.consts,
      SupportedO Q B _ s (B.Incl _ W ((B.inner _).map h (B.I c))) := by
  classical
  have key : ∀ T : Finset Sig.Const, ∃ s : Q.Key W, ∀ c ∈ T,
      SupportedO Q B _ s (B.Incl _ W ((B.inner _).map h (B.I c))) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨Q.zero W, by simp⟩
    | @insert c T hc ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨u, hu⟩ := hall _ _ ((B.inner _).map h (B.I c))
      refine ⟨Q.join s u, fun d hd => ?_⟩
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact supportedO_right Q B s hu
      · exact supportedO_left Q B u (hs d hd)
  obtain ⟨s, hs⟩ := key (Term.consts_finite t).toFinset
  exact ⟨s, fun c hc => hs c ((Term.consts_finite t).mem_toFinset.2 hc)⟩

theorem isModel_of_support
    (hall : ∀ (σ : Ty) (W : C) (x : B.Dom W σ),
      ∃ s : Q.Key W, SupportedO Q B σ s (B.Incl σ W x))
    (hinner : ∀ (ρ : RTy) (W : C) (F : Intension B.inner ρ W),
      (∃ s : Q.Key W, SupportedO Q B (.rel ρ) s F) → F ∈ Set.range (B.incl ρ W)) :
    B.IsModel := fun {_ σ W} h t g => by
  obtain ⟨s, hs⟩ := env_supported Q B hall g
  obtain ⟨u, hu⟩ := constants_supported Q B hall h t
  have hp := sem_supported Q B h t g (Q.join s u)
    (fun τ v => supportedO_left Q B u (hs τ v))
    (fun c hc => supportedO_right Q B s (hu c hc))
  cases σ with
  | e => exact ⟨_, rfl⟩
  | rel ρ => exact hinner ρ W _ ⟨Q.join s u, hp⟩
  | var _ => exact ⟨_, rfl⟩

end closure

variable {Sig : Signature} {W₀ : C} {hne : ∀ W, Nonempty (De.obj W)}
  {I : ∀ c : Sig.Const, (Domain Q De (Sig.typeOf c)).obj W₀}

local notation "B" => model Q De W₀ hne I

theorem all_supported (he : ∀ W (x : De.obj W), Supported Q De x) :
    ∀ (σ : Ty) (W : C) (x : B.Dom W σ),
      ∃ s : Q.Key W, SupportedO Q B σ s (B.Incl σ W x)
  | .e, W, x => (he W x).elim fun s hs =>
      ⟨s, (supportedO_incl_iff Q B .e s x).2 hs⟩
  | .rel ρ, W, x => (range_incl Q De ρ W _).1 ⟨x, rfl⟩
  | .var n, W, x => (he W x).elim fun s hs =>
      ⟨s, (supportedO_incl_iff Q B (.var n) s x).2 hs⟩

/-- Actual closure of the recursively built model, for every interpretation. -/
theorem model_isModel (he : ∀ W (x : De.obj W), Supported Q De x) : B.IsModel :=
  isModel_of_support Q B (all_supported Q De he)
    fun ρ W F hf => (range_incl Q De ρ W F).2 hf

end Classicism.Meta.Intensional.Central
