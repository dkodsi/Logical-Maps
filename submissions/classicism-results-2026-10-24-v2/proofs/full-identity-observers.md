# Full identity observer laws and their bounds

Original mathematical argument, direct source misc; unpaginated.

1. QUALIFICATIONS

For fixed X:(tt)t put

  S_X := forall p,q [p=q IFF forall O(X(O)->O(p IFF q))].

Pointwise full identity laws include

  forall p,q O(p AND q)=(Op AND Oq),
  forall F:sigma t O(forall x:sigma Fx)=(forall x:sigma O(Fx)).

Composite identity instead identifies the corresponding lambda-p,q or
lambda-F operations. Composite identity implies pointwise identity in H;
the converse is not automatic in C. BF_t suffices for upgrading the Boolean
laws, and BF_(sigma t) for upgrading a pointwise quantifier law. The proofs
below keep these readings distinct and the main countermodels cover both.

Boolean qualification includes top, bottom, negation, conjunction and
disjunction. Quantifier lists are finite; all finite lists form a schema.
Primitive equality requires its own typed preservation law. Fixing (x=y)
and requiring O(p=q)=(Op=Oq) are different conditions; neither is silently
included in Boolean/quantifier qualification.

2. SUPPORTING BOUNDS

For full identity universal commutation the proved bounds over C remain

  BOX BF_Delta -> S_X -> BF_Delta.

They hold for both pointwise and composite identity readings. The upper
bound uses the necessity operator; the lower follows by applying qualified
tests to a family whose every member equals top. The argument neither
necessitates an unboxed BF premise nor gives existential commutation for
necessity. Whether either bound is exact remains unresolved here.

Boolean qualification gives a separate positive bound:
Atomicity_t + BF_t + BOX BF_Delta implies full composite separation.
Under C5+Atomicity_t this separation holds necessarily. The complete proof
and positive structural criteria are in positive-operator-representation.txt.

3. SUBSTANTIVE COUNTERMODELS

reverse-entailment-countermodel.txt excludes Boolean
separation in qualitative contrast at W0, despite C5+Actuality+necessary BF.
At W1 of the same construction full Boolean/quantifier separation holds,
but is not necessary; see local-and-necessary-operator-separation.txt
sections 2-5 for the admitted witnesses and their composite laws.

ordered-symmetry-observers.txt gives a stronger distinction. In an everywhere
atomless C5 model, full Boolean separation holds necessarily, while full
quantifier separation fails at the ordered object already for type e.
Necessary BF holds at every type. Invariant ultrafilters supply admitted
Boolean operators; quantifier preservation forces an impossible selection
from their finite supports. The other object has full quantifier separation.

These are substantive failures of implication. The formula
BOX S_X iff K_X=(lambda p.BOX p), with K_X(p)=forall O(X(O)->Op), is only
the routine C reformulation of necessary separation, not an additional
classification theorem.

4. NO CONJUNCTION OF CATALOG CONDITIONS CHARACTERIZES SEPARATION

For full Boolean qualification, alone or with any fixed finite list of
full universal/existential commutation laws, no conjunction of the current
132 catalog conditions characterizes S_X over C. Semantic failure of a
whole recorded schema may also be used as a negative condition. The same
argument covers the schema of all finite type lists.

Let N be qualitative contrast at W0. It fails S_X and its complete catalog
profile has 74 holds and 58 failures, using the supplemental necessary-
Transversal proof in database-combination-obstruction.txt section 3.
Three positive models cover all its coordinates:

  finite-support-permutations: 104 agreements not previously covered;
  henkin-without-relational-choice: 24 further agreements;
  qualitative contrast at W1: the remaining 4 agreements.

The permutation model's finitely supported transport operators meet the
full composite laws at all future inputs. In the extensional Henkin model
the identity operator qualifies and separates. This retains the source's
relative-consistency construction from a model of ZF without choice.
At W1 the witnesses are verified in the local/necessary separation note.
Only C5 and failure of No Pure Contingency are needed as W1 catalog inputs:
NOT Actuality is true there and false at W0. Signature constants retain
exactly the top interpretation.

For every catalog principle P, some positive model agrees with N on P.
Any positive or negative catalog condition necessary for S_X must therefore
hold in N. Their conjunction holds in N, where S_X fails, so it cannot
characterize S_X. Different positive models may cover different coordinates;
this does not rule out arbitrary Boolean combinations with disjunctions.

The reproducible full-identity-combination-audit.py and its JSON retain all
132 witnesses and recorded inference chains. They use proved records with
empty engine background and explicitly labelled supplemental research
inputs. The W1 inputs are not database edits. No complete W1 profile or
matching complete positive/negative profile pair has been established.

5. BASE-H LIMIT

Boolean/quantifier separation alone still does not imply C over H. The
four-proposition model in operator-model-separations.txt section 1 has full
Boolean/quantifier separating operators, including the composite laws,
while (x=x)=top fails. The H formulation in [Logical Observers](logical-observers.md) includes equality laws.
