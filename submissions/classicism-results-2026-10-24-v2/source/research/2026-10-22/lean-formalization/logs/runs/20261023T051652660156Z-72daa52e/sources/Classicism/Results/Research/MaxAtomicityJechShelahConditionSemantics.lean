import Classicism.Results.Research.MaxAtomicityJechShelahArithmeticSemantics
import Classicism.Results.Research.MaxAtomicityCodedFunctions
import Classicism.Results.Research.MaxAtomicityCanonicalCompletion
import Classicism.Results.Research.MaxAtomicitySelectorTransport

/-!
# Exact condition, completion, and generator semantics for JSCode

The finite child-injection witnesses are actual small graphs. Indexed condition
soundness and completeness then give precisely the concrete tree codes. The
poset, inclusion graph, regular-open carrier, and canonical generator graph are
therefore determined, without a formula-adequacy assumption.

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 749--750,
definitions (1)--(6), plus the original explicit coding proof (misc,
23 October 2026). The existence theorem at the end isolates only the arithmetic
witness construction, whose actual certificate is supplied separately.
Compilation belongs to the designated serial checker.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahConditionSemantics

open MaxAtomicityHereditaryUniverse MaxAtomicityHereditaryGraphs
open MaxAtomicityJechShelahTrees MaxAtomicityJechShelahCylinders
open MaxAtomicityJechShelahSetCodes MaxAtomicityJechShelahIndexedGenerators
open MaxAtomicityJechShelahRigidityCriterion MaxAtomicityJechShelahIndexCoding
open MaxAtomicitySetCodeAbsoluteness MaxAtomicityCodedFunctions
open MaxAtomicityJechShelahSyntax MaxAtomicityJechShelahArithmeticSemantics
open MaxAtomicityCanonicalCompletion

noncomputable section

abbrev D := B → B
abbrev R := codeRelation B

def indices (X : D) : Set ℕ := {n | R (number n) X}

theorem indices_tree (T : Condition) : indices (treeEmbedding T) = nodeIndices T := by
  apply Set.ext
  intro n
  change present B (number n) ∈ present B (treeEmbedding T) ↔ n ∈ nodeIndices T
  rw [present_naturalEmbedding, present_treeEmbedding, treeCode, mem_realCode]

theorem tree_subset_omega (T : Condition) : O.Subset R (treeEmbedding T) canonicalNaturals := by
  apply (subset_iff B _ _).2
  rw [present_treeEmbedding, canonicalNaturals, present_encode]
  exact realCode_subset_naturalsCode (nodeIndices T)

theorem subset_omega_real {X : D} (hX : O.Subset R X canonicalNaturals) :
    present B X = realCode (indices X) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    have hzH := universeSet_transitive B _ (present_mem B X) z hz
    have hx : R (encode B z hzH) X := (encoded_mem B _ _ _).2 hz
    obtain ⟨n, hn⟩ := (canonical_number_range _).1 (hX _ hx)
    have hval : natural n = z := (present_naturalEmbedding n).symm.trans
      ((congrArg (present B) hn).trans (present_encode B z hzH))
    rw [← hval, mem_realCode]
    exact hn.symm ▸ hx
  · intro hz
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp hz
    have hmem : natural n.val ∈ present B X := by
      simpa only [indices, R, codeRelation, present_naturalEmbedding] using n.property
    exact hn ▸ hmem

theorem manyChildren_iff {a : Parameters D} (ha : Decoded a) (X : D)
    (hX : O.Subset R X canonicalNaturals) (u r : ℕ) :
    Ordinary.ManyChildren R a X (number u) (number r) ↔
      ∃ g : Fin r → ℕ, Function.Injective g ∧
        ∀ i, R (number (g i)) X ∧ Child u (g i) := by
  classical
  constructor
  · rintro ⟨f, hf, hdom, hinj, hchildren⟩
    have hex : ∀ i : Fin r, ∃ j : ℕ,
        R (number j) X ∧ O.GraphApp R f (number i.val) (number j) ∧ Child u j := by
      intro i
      obtain ⟨j, hjX, hij, hchild⟩ := hchildren (number i.val) ((number_mem i.val r).2 i.isLt)
      obtain ⟨j, rfl⟩ := (canonical_number_range j).1 (hX j hjX)
      exact ⟨j, hjX, hij, (child_decoded ha.omega ha.add ha.n ha.offset u j).1 hchild⟩
    let g : Fin r → ℕ := fun i => Classical.choose (hex i)
    have hg : ∀ i, R (number (g i)) X ∧ O.GraphApp R f (number i.val) (number (g i)) ∧ Child u (g i) :=
      fun i => Classical.choose_spec (hex i)
    refine ⟨g, ?_, fun i => ⟨(hg i).1, (hg i).2.2⟩⟩
    intro i j hij
    apply Fin.val_injective
    apply naturalEmbedding.injective
    exact hinj (number i.val) (number j.val) (number (g i))
      ⟨(hg i).2.1, by simpa only [hij] using (hg j).2.1⟩
  · rintro ⟨g, hg, hchildren⟩
    let e : Fin r ↪ B :=
      ({ toFun := fun i : Fin r => i.val, inj' := Fin.val_injective } : Fin r ↪ ℕ).trans
        (Infinite.natEmbedding B)
    let input : Fin r → D := fun i => number i.val
    let output : Fin r → D := fun i => number (g i)
    have hin : Function.Injective input := naturalEmbedding.injective.comp Fin.val_injective
    have hout : Function.Injective output := naturalEmbedding.injective.comp hg
    let f := functionCode e input output
    refine ⟨f, functionCode_function e input output hin,
      functionCode_domain e input output (number r) ?_,
      functionCode_injective e input output hout, ?_⟩
    · intro x
      rw [canonical_predecessor]
      constructor
      · rintro ⟨i, hi, hix⟩
        exact ⟨⟨i, hi⟩, hix⟩
      · rintro ⟨i, hix⟩
        exact ⟨i.val, i.isLt, hix⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := (canonical_predecessor r x).1 hx
      let j : Fin r := ⟨i, hi⟩
      exact ⟨number (g j), (hchildren j).1,
        (functionCode_app e input output _ _).2 ⟨j, rfl, rfl⟩,
        (child_decoded ha.omega ha.add ha.n ha.offset u (g j)).2 (hchildren j).2⟩

theorem conditionCode_iff_indices {a : Parameters D} (ha : Decoded a) (X : D) :
    Ordinary.ConditionCode R a X ↔ O.Subset R X canonicalNaturals ∧ IndexCondition (indices X) := by
  constructor
  · rintro ⟨hsub, hz, hdown, hbushy⟩
    have hX : O.Subset R X canonicalNaturals := ha.omega ▸ hsub
    refine ⟨hX, by simpa only [ha.zero] using hz, ?_, ?_⟩
    · intro j hj i hij
      exact hdown (number j) hj (number i) (ha.omega.symm ▸ number_in_omega i)
        ((ha.ancestor i j).2 hij)
    · intro i hi m
      obtain ⟨u, huX, hne, hanc, p, hpw, r, hrw, hup, hpmr, hmany⟩ :=
        hbushy (number i) hi (number m) (ha.omega.symm ▸ number_in_omega m)
      obtain ⟨u, rfl⟩ := (canonical_number_range u).1 (hX u huX)
      rw [ha.omega] at hpw hrw
      obtain ⟨p, rfl⟩ := (canonical_number_range p).1 hpw
      obtain ⟨r, rfl⟩ := (canonical_number_range r).1 hrw
      have hp := (ha.p u p).1 hup
      have hr := (ha.pow p m r).1 hpmr
      subst p
      subst r
      obtain ⟨g, hg, hchildren⟩ := (manyChildren_iff ha X hX u _).1 hmany
      exact ⟨u, huX, fun heq => hne (congrArg number heq), (ha.ancestor i u).1 hanc,
        g, hg, hchildren⟩
  · rintro ⟨hX, hz, hdown, hbushy⟩
    refine ⟨ha.omega.symm ▸ hX, by simpa only [ha.zero] using hz, ?_, ?_⟩
    · intro j hjX i hiw hij
      obtain ⟨j, rfl⟩ := (canonical_number_range j).1 (hX j hjX)
      rw [ha.omega] at hiw
      obtain ⟨i, rfl⟩ := (canonical_number_range i).1 hiw
      exact hdown j hjX i ((ha.ancestor i j).1 hij)
    · intro i hiX m hmw
      obtain ⟨i, rfl⟩ := (canonical_number_range i).1 (hX i hiX)
      rw [ha.omega] at hmw
      obtain ⟨m, rfl⟩ := (canonical_number_range m).1 hmw
      obtain ⟨u, hu, hne, hanc, g, hg, hchildren⟩ := hbushy i hiX m
      exact ⟨number u, hu, fun heq => hne (naturalEmbedding.injective heq),
        (ha.ancestor i u).2 hanc,
        number (growthP u), ha.omega.symm ▸ number_in_omega _,
        number (growthP u ^ m), ha.omega.symm ▸ number_in_omega _,
        (ha.p u _).2 rfl, (ha.pow _ _ _).2 rfl,
        (manyChildren_iff ha X hX u _).2 ⟨g, hg, hchildren⟩⟩

/-- The actual condition codes, with both directions and no restriction to
previously named trees. -/
theorem conditionCode_iff_tree {a : Parameters D} (ha : Decoded a) (X : D) :
    Ordinary.ConditionCode R a X ↔ ∃ T : Condition, treeEmbedding T = X := by
  rw [conditionCode_iff_indices ha]
  constructor
  · rintro ⟨hX, hI⟩
    let T := ofIndexCondition (indices X) hI
    refine ⟨T, present_injective B ?_⟩
    rw [present_treeEmbedding, treeCode, nodeIndices_ofIndexCondition]
    exact (subset_omega_real hX).symm
  · rintro ⟨T, rfl⟩
    exact ⟨tree_subset_omega T, by rw [indices_tree]; exact nodeIndices_indexCondition T⟩

theorem canonical_posetCarrier {a : Parameters D} (ha : Decoded a) :
    Ordinary.PosetCarrier R a canonicalPoset :=
  fun X => (canonical_poset_range X).trans (conditionCode_iff_tree ha X).symm

theorem posetCarrier_unique {a : Parameters D} (ha : Decoded a) (P : D)
    (hP : Ordinary.PosetCarrier R a P) : P = canonicalPoset := by
  apply codeRelation_extensional B
  intro X
  exact (hP X).trans (canonical_posetCarrier ha X).symm

theorem canonical_inclusionGraph : Ordinary.InclusionGraph R canonicalPoset canonicalOrder := by
  intro z
  constructor
  · intro hz
    change present B z ∈ present B (encode B orderGraph orderGraph_mem_universe) at hz
    rw [present_encode, orderGraph, graphOf, ZFSet.mem_range] at hz
    obtain ⟨p, hp⟩ := hz
    refine ⟨treeEmbedding p.val.1, (canonical_poset_range _).2 ⟨_, rfl⟩,
      treeEmbedding p.val.2, (canonical_poset_range _).2 ⟨_, rfl⟩, ?_, ?_⟩
    · apply (orderedPair_iff B _ _ _).2
      simpa only [present_treeEmbedding] using hp.symm
    · apply (subset_iff B _ _).2
      rw [present_treeEmbedding, present_treeEmbedding]
      exact (treeCode_subset_iff _ _).2 p.property
  · rintro ⟨X, hX, Y, hY, hp, hsub⟩
    obtain ⟨T, rfl⟩ := (canonical_poset_range X).1 hX
    obtain ⟨S, rfl⟩ := (canonical_poset_range Y).1 hY
    have hp' := (orderedPair_iff B _ _ _).1 hp
    have hsub' := (subset_iff B _ _).1 hsub
    rw [present_treeEmbedding, present_treeEmbedding] at hp' hsub'
    change present B z ∈ present B (encode B orderGraph orderGraph_mem_universe)
    rw [present_encode, hp', mem_orderGraph]
    exact (treeCode_subset_iff T S).1 hsub'

theorem inclusionGraph_unique (O : D)
    (hO : Ordinary.InclusionGraph R canonicalPoset O) : O = canonicalOrder := by
  apply codeRelation_extensional B
  intro z
  exact (hO z).trans (canonical_inclusionGraph z).symm

theorem all_comparable_iff {a : Parameters D} (ha : Decoded a) (T : Condition) (i : ℕ) :
    (∀ j, R j (treeEmbedding T) →
      O.GraphApp R a.ancestor j (number i) ∨ O.GraphApp R a.ancestor (number i) j) ↔
      ∀ j ∈ nodeIndices T, Ancestor j i ∨ Ancestor i j := by
  constructor
  · intro h j hj
    have hj' : R (number j) (treeEmbedding T) := by
      change j ∈ indices (treeEmbedding T)
      rw [indices_tree]
      exact hj
    exact (or_congr (ha.ancestor j i) (ha.ancestor i j)).1 (h _ hj')
  · intro h j hj
    obtain ⟨j, rfl⟩ := (canonical_number_range j).1 (tree_subset_omega T j hj)
    have hj' : j ∈ nodeIndices T := by
      rw [← indices_tree]
      exact hj
    exact (or_congr (ha.ancestor j i) (ha.ancestor i j)).2 (h j hj')

theorem canonical_generatorOpen {a : Parameters D} (ha : Decoded a) (i : ℕ) :
    Ordinary.GeneratorOpen R a canonicalPoset (number i)
      (carrierEmbedding (indexedGenerator i)) := by
  intro X
  constructor
  · intro hX
    obtain ⟨T, rfl, hT⟩ := (carrier_represents (indexedGenerator i) X).1 hX
    exact ⟨(canonical_poset_range _).2 ⟨T, rfl⟩,
      (all_comparable_iff ha T i).2 ((mem_indexedGenerator_iff T i).1 hT)⟩
  · rintro ⟨hX, hcomp⟩
    obtain ⟨T, rfl⟩ := (canonical_poset_range X).1 hX
    exact (carrier_represents (indexedGenerator i) _).2
      ⟨T, rfl, (mem_indexedGenerator_iff T i).2 ((all_comparable_iff ha T i).1 hcomp)⟩

theorem generatorOpen_iff {a : Parameters D} (ha : Decoded a) (i : ℕ) (X : D) :
    Ordinary.GeneratorOpen R a canonicalPoset (number i) X ↔
      X = carrierEmbedding (indexedGenerator i) := by
  constructor
  · intro hX
    apply codeRelation_extensional B
    intro T
    exact (hX T).trans (canonical_generatorOpen ha i T).symm
  · rintro rfl
    exact canonical_generatorOpen ha i

theorem canonicalGraph_eq_functionCode :
    canonicalGraph = functionCode (Infinite.natEmbedding B) number
      (fun n => carrierEmbedding (indexedGenerator n)) := by
  apply present_injective B
  rw [canonicalGraph, present_encode, present_functionCode]
  simp only [MaxAtomicityHereditaryGraphs.generatorGraph, present_naturalEmbedding,
    present_carrierEmbedding]

theorem canonicalGraph_function : O.FunctionGraph R canonicalGraph := by
  rw [canonicalGraph_eq_functionCode]
  exact functionCode_function _ _ _ naturalEmbedding.injective

theorem canonicalGraph_domain : MaxAtomicitySetFormulaTools.Ordinary.GraphDomain R
    canonicalGraph canonicalNaturals := by
  rw [canonicalGraph_eq_functionCode]
  exact functionCode_domain _ _ _ _ canonical_number_range

theorem canonical_generatorGraph {a : Parameters D} (ha : Decoded a) :
    Ordinary.GeneratorGraph R a canonicalPoset canonicalGraph := by
  refine ⟨canonicalGraph_function, ha.omega.symm ▸ canonicalGraph_domain, ?_⟩
  intro i hi X
  rw [ha.omega] at hi
  obtain ⟨i, rfl⟩ := (canonical_number_range i).1 hi
  exact (canonical_graph i X).trans (generatorOpen_iff ha i X).symm

theorem graphs_equal {F G : D}
    (hF : MaxAtomicitySetFormulaTools.Ordinary.GraphOnlyPairs R F)
    (hG : MaxAtomicitySetFormulaTools.Ordinary.GraphOnlyPairs R G)
    (happ : ∀ x y, O.GraphApp R F x y ↔ O.GraphApp R G x y) : F = G := by
  have hle : ∀ F G : D,
      MaxAtomicitySetFormulaTools.Ordinary.GraphOnlyPairs R F →
      (∀ x y, O.GraphApp R F x y → O.GraphApp R G x y) → O.Subset R F G := by
    intro F G hF happ p hp
    obtain ⟨x, y, hpPair⟩ := hF p hp
    obtain ⟨q, hqPair, hqG⟩ := happ x y ⟨p, hpPair, hp⟩
    have hpq : p = q := present_injective B
      (((orderedPair_iff B _ _ _).1 hpPair).trans ((orderedPair_iff B _ _ _).1 hqPair).symm)
    exact hpq.symm ▸ hqG
  apply codeRelation_extensional B
  intro p
  exact ⟨hle F G hF (fun x y => (happ x y).1) p,
    hle G F hG (fun x y => (happ x y).2) p⟩

theorem generatorGraph_unique {a : Parameters D} (ha : Decoded a) (G : D)
    (hG : Ordinary.GeneratorGraph R a canonicalPoset G) : G = canonicalGraph := by
  apply graphs_equal hG.1.1 canonicalGraph_function.1
  intro x y
  constructor
  · intro hxy
    have hx : R x a.w := (hG.2.1 x).2 ⟨y, hxy⟩
    have hxw := ha.omega ▸ hx
    obtain ⟨i, rfl⟩ := (canonical_number_range x).1 hxw
    have hy := (generatorOpen_iff ha i y).1 ((hG.2.2 _ hx y).1 hxy)
    exact (canonical_graph i y).2 hy
  · intro hxy
    have hx : R x canonicalNaturals := (canonicalGraph_domain x).2 ⟨y, hxy⟩
    obtain ⟨i, rfl⟩ := (canonical_number_range x).1 hx
    exact (hG.2.2 _ (ha.omega.symm ▸ hx) y).2
      ((generatorOpen_iff ha i y).2 ((canonical_graph i y).1 hxy))

theorem codeWith_unique {a : Parameters D} {c P O G : D}
    (h : Ordinary.CodeWith R a c P O G) :
    c = canonicalCarrier ∧ a.w = canonicalNaturals ∧ G = canonicalGraph := by
  obtain ⟨har, hP, hO, hc, hG⟩ := h
  have ha := arithmetic_decoded har
  have hP' := posetCarrier_unique ha P hP
  subst P
  have hO' := inclusionGraph_unique O hO
  subst O
  exact ⟨algebraCarrier_unique c hc, ha.omega, generatorGraph_unique ha G hG⟩

theorem canonical_sound : MaxAtomicitySelectorTransport.CanonicalSound JSCode := by
  intro c w G h
  have h' := (satisfies_JSCode R (MaxAtomicityPureSelector.triple c w G)).1 h
  obtain ⟨z, one, two, add, mul, pow, p, n, offset, ancestor, P, O, hc⟩ := h'
  exact codeWith_unique hc

theorem canonical_exists_of_arithmetic
    (hex : ∃ a : Parameters D, a.w = canonicalNaturals ∧ Ordinary.Arithmetic R a) :
    MaxAtomicitySelectorTransport.CanonicalExists JSCode := by
  obtain ⟨a, hw, har⟩ := hex
  have ha := arithmetic_decoded har
  apply (satisfies_JSCode R (MaxAtomicityPureSelector.triple canonicalCarrier canonicalNaturals canonicalGraph)).2
  refine ⟨a.zero, a.one, a.two, a.add, a.mul, a.pow, a.p, a.n, a.offset, a.ancestor,
    canonicalPoset, canonicalOrder, ?_⟩
  have heq : Parameters.mk canonicalNaturals a.zero a.one a.two a.add a.mul a.pow a.p a.n
      a.offset a.ancestor = a := by
    cases a
    cases hw
    rfl
  rw [heq]
  exact ⟨har, canonical_posetCarrier ha, canonical_inclusionGraph, canonical_algebraCarrier,
    canonical_generatorGraph ha⟩

#print axioms manyChildren_iff
#print axioms conditionCode_iff_tree
#print axioms canonical_generatorGraph
#print axioms canonical_sound
#print axioms canonical_exists_of_arithmetic

end

end Classicism.Meta.Research.MaxAtomicityJechShelahConditionSemantics
