import Classicism.Models.NominalFiniteStrata

/-!
# Concrete world actions for the nominal hierarchy

These are the specified Sym(A) atom worlds, trivial natural-number worlds, and
tagged atom worlds A×N. Finite and countable support ideals are instantiated,
with the SAME trivial-action Nat individual domain supplied by Hierarchy.dom.
The unordered-pair example and the nontrivial IC/FC/RC classifications are not
claimed here. The actual generated individual IC instance holds in every
example. Distinct orbit sequences give boxed operational Dedekind infinity in
the trivial and tagged examples.

Sources: nominal-choice-classification-20261022.md §§1,6–7 and
countable-support-choice-countermodel-20261022.md construction; local research,
unpaginated, misc. Uncompiled candidate, ordinary classical metatheory.
-/

namespace Classicism.Meta.Nominal.Examples
noncomputable section

def atoms (Atom : Type) : Action (Equiv.Perm Atom) where
  Carrier := Atom
  act g a := g a
  one_act _ := rfl
  mul_act _ _ _ := rfl

def atomWorlds (Atom : Type) (I : SupportIdeal (atoms Atom))
    (hI : ∀ a : Atom, I.Small {a}) : Nom (atoms Atom) I where
  obj := atoms Atom
  supported a := ⟨{a}, hI a, fun g hg => hg a (Set.mem_singleton a)⟩

def finiteAtomWorlds (Atom : Type) : Nom (atoms Atom) (finiteIdeal (atoms Atom)) :=
  atomWorlds Atom (finiteIdeal (atoms Atom)) (fun a => Set.finite_singleton a)

def countableAtomWorlds (Atom : Type) : Nom (atoms Atom) (countableIdeal (atoms Atom)) :=
  atomWorlds Atom (countableIdeal (atoms Atom)) (fun a => Set.countable_singleton a)

def trivialNaturalWorlds (Atom : Type) (I : SupportIdeal (atoms Atom)) : Nom (atoms Atom) I :=
  trivialNom (atoms Atom) I Nat

def taggedAtomWorlds (Atom : Type) (I : SupportIdeal (atoms Atom))
    (hI : ∀ a : Atom, I.Small {a}) : Nom (atoms Atom) I :=
  productNom (atomWorlds Atom I hI) (trivialNaturalWorlds Atom I)

theorem trivial_natural_orbits (Atom : Type) (I : SupportIdeal (atoms Atom)) (n m : Nat) :
    Orbit (trivialNaturalWorlds Atom I) n m → n = m := by
  rintro ⟨g, hg⟩
  exact hg

theorem tagged_orbits (Atom : Type) (I : SupportIdeal (atoms Atom))
    (hI : ∀ a : Atom, I.Small {a}) (a : Atom) (n m : Nat) :
    Orbit (taggedAtomWorlds Atom I hI) (a, n) (a, m) → n = m := by
  rintro ⟨g, hg⟩
  exact congrArg Prod.snd hg

theorem trivial_natural_boxed_dedInfT (Atom : Type) (I : SupportIdeal (atoms Atom)) (w : Nat) :
    Hierarchy.Holds (trivialNaturalWorlds Atom I) (Hierarchy.pureConstants _) () w
      (Term.box Hierarchy.dedInfT) :=
  Hierarchy.orbit_sequence_boxed_dedInfT _ id (trivial_natural_orbits Atom I) w

theorem tagged_boxed_dedInfT (Atom : Type) (I : SupportIdeal (atoms Atom))
    (hI : ∀ a : Atom, I.Small {a}) (a : Atom) (w : taggedAtomWorlds Atom I hI) :
    Hierarchy.Holds (taggedAtomWorlds Atom I hI) (Hierarchy.pureConstants _) () w
      (Term.box Hierarchy.dedInfT) :=
  Hierarchy.orbit_sequence_boxed_dedInfT _ (fun n => (a, n)) (tagged_orbits Atom I hI a) w

theorem trivial_natural_all_IC (Atom : Type) (I : SupportIdeal (atoms Atom)) (σ : Ty) (w : Nat) :
    Hierarchy.Holds (trivialNaturalWorlds Atom I) (Hierarchy.pureConstants _) () w
      (P.IntensionalChoice.quoted σ) :=
  Hierarchy.trivial_intensionalChoice_quoted _ (fun _ _ => rfl) σ w

/-- The finite-support atom model in the source, A=N and E=N with distinct actions. -/
def finiteNaturalAtoms := finiteAtomWorlds Nat

/-- The source's simplest infinitely-many-moving-orbits world action. -/
def finiteTaggedNaturalAtoms := taggedAtomWorlds Nat (finiteIdeal (atoms Nat))
  (fun a => Set.finite_singleton a)

/-- The larger-support hierarchy on an externally uncountable atom type. This
definition alone does not certify its countable-reservoir IC theorem. -/
def countableSequenceAtoms := countableAtomWorlds (Nat → Bool)

theorem finite_atoms_individual_boxed_IC (w : finiteNaturalAtoms) :
    Hierarchy.Holds finiteNaturalAtoms (Hierarchy.pureConstants _) () w
      (P.NecIntensionalChoice.quoted .e) :=
  Hierarchy.individuals_boxed_intensionalChoice_quoted _ w

theorem countable_atoms_individual_boxed_IC (w : countableSequenceAtoms) :
    Hierarchy.Holds countableSequenceAtoms (Hierarchy.pureConstants _) () w
      (P.NecIntensionalChoice.quoted .e) :=
  Hierarchy.individuals_boxed_intensionalChoice_quoted _ w

end
end Classicism.Meta.Nominal.Examples
