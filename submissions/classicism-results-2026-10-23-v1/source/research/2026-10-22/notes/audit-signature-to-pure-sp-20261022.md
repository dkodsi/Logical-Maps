# Signature Strong Possibility versus pure Strong Possibility

22 October 2026. Independent ordinary mathematical audit by an OpenAI Codex research agent. No main-record edits, promotions, Lean work, human checking or literature-novelty claim.

Target: `topics/classicism/results/strong-possibility-signature-r-implies-strong-possibility-r.yaml`, currently conjectured. The exact signature-SP and signature-Max records, the proof of signature SP⇒signature Max, and the audited profile construction were checked.

## 1. Decisive result

**The proposed pure-consistency-preservation route is false for every signature admitted by the map.** Let

    A_1:=F∧E_1,
    U:=Atom_t(A_1).

Then

    Con(Max(C)+U),
    Max(C(Σ))⊢¬U

whenever Σ contains at least one relational nonlogical constant. This includes finite or infinite signatures, with or without individual names. It is an explicit pure-sentence nonconservativity witness, not merely the failure of a particular attempted expansion.

Moreover

    SP_pure⊢U,
    SP_Σ⊢¬Diamond_ne U.

The second theory therefore refutes a specific instance of the first theory's Strong Possibility schema. Consequently

    SP_Σ entails SP_pure  iff  SP_Σ is inconsistent.

This does **not** settle the conjectured implication unconditionally: consistency of SP_Σ remains unproved here. It shows that a proof of that implication for an admitted signature would also be a proof of inconsistency of its antecedent. A related reflection argument cannot evade this obstruction while retaining a consistent SP_Σ.

## 2. Why the pure atom assertion is Max-consistent

The singleton pure-profile model in `profile-root-construction-20261022.md` §§1–4, independently audited in `audit-profile-20261022.md`, satisfies pure Max and U. The relevant construction facts are these.

Root propositions have an arbitrary actual truth bit and a pure one-individual-variable profile T(z), interpreted through all complete component points. Every full extensional one-individual pointed structure has the same pure theory. Thus on A_1-points every T(z) has one fixed truth value. At the root A_1 is actually false because the root proposition domain is infinite. It follows that for any root p,

    p∧A_1=A_1 or bottom.

An A_1 component witnesses A_1≠bottom. Hence A_1 is an atom at that root. The proof uses full entity profiles and descendant truth separation, not an identification of all actually true propositions.

This supplies the consistency fact licensing the pure SP instance Diamond_ne U. Atomhood expands to

    A_1≠bottom ∧ ∀p[p≤A_1→(p=bottom∨p=A_1)],

where ≤ is an identity of Boolean terms. Therefore U is a universal finite Boolean combination of typed identities. The audited identity-reflection lemma gives

    C⊢Diamond_ne U→U.

Thus SP_pure⊢U. No optional premise is necessitated in either step.

## 3. Two signature-Max instances split the same cell

Choose any relational constant c:τ of Σ. Write τ=σ_1…σ_h t, with h possibly0. Define

    R(c):=∀x_1^σ1…x_h^σh c[x_1,…,x_h],

with R(c)=c for the empty tuple. All these types are admitted; the output is t.

In a full extensional one-individual model, interpret c first as the top relation and then as the bottom relation. Every argument type is nonempty, so R(c) is respectively true and false. Interpret all other constants arbitrarily, choosing one fixed individual for any individual names and, for example, top relations for the other relational names. Therefore both sentences

    A_1∧R(c),       A_1∧¬R(c)

are C(Σ)-consistent. This does not presume a generic expansion of an arbitrary pure-Max model. It constructs two elementary C(Σ) models solely to establish the two required schema side conditions.

Signature Max in its proved-equivalent possibility form entails

    Diamond(A_1∧R(c)),
    Diamond(A_1∧¬R(c)).

These two propositions are nonzero disjoint parts of A_1. Hence signature Max entails ¬Atom(A_1), that is ¬U. Only these two additional Max instances are needed for the contradiction with U.

The argument does not depend on the number or interpretation of individual names. It also does not require Σ to be finite. For infinite signatures no infinite diagram is asserted: each displayed sentence uses only the one selected c, and the other constants have harmless interpretations in the two consistency models.

The proved signature-SP⇒signature-Max record now gives SP_Σ⊢¬U. Contraposition of the C-theorem Diamond_ne U→U yields

    SP_Σ⊢¬Diamond_ne U.

But Diamond_ne U is one of the licensed pure-SP axioms by §2. This is the promised explicit incompatible instance.

## 4. What precisely is wrong with the record's “iff” caveat

The record correctly warns that conservativity of C under added constants is not conservativity of Max(C). Its concluding unconditional equivalence between the proposed SP arrow and consistency preservation omits an antecedent-consistency qualification.

Let CP(Σ) abbreviate

    for every closed pure P,
    Con(Max(C)+P) implies Con(Max(C(Σ))+P).

If CP(Σ) holds, then every pure-SP axiom is directly a signature-SP instance, so the arrow holds. This direction does not require consistency of SP_Σ.

Conversely suppose CP(Σ) fails, witnessed by pure P. Then Max(C(Σ))⊢¬P. The signature version of the audited finite-support reflection proof gives

    SP_Σ⊢Box_ne¬P, hence SP_Σ⊢¬Diamond_ne P.

To see the scope, a proof of ¬P from signature Max uses finitely many signature inequalities Q. Within C(Σ) their support gives Diamond Q→¬P; only this discharged C(Σ)-theorem is necessitated, and actual Q witnesses Box_ne¬P. Thus no optional signature-Max axiom is boxed.

Pure SP includes Diamond_ne P because P is pure-Max-consistent. Consequently, if SP_Σ entails pure SP while CP fails, SP_Σ is inconsistent. In classical metatheoretic terms the correct general relation is

    [SP_Σ entails SP_pure]
      iff [CP(Σ) or SP_Σ is inconsistent].

Equivalently, **under Con(SP_Σ)** the record's iff is correct. For every map-admitted signature §3 proves ¬CP(Σ), so the arrow is exactly equivalent to inconsistency of SP_Σ.

The concrete U witness permits the shorter identity-reflection proof in §3; the finite-support argument here explains the general logical correction to the record's caveat. The original YAML was left untouched.

## 5. Consequences that do and do not follow

Verified consequences:

- Max(C(Σ)) is not conservative over pure Max for pure sentences, for every admitted Σ.
- No pure-SP model has an expansion satisfying signature Max for an admitted Σ. This includes specially chosen proposed generic or separated expansions.
- C+SP_pure+SP_Σ is inconsistent, since signature SP entails signature Max.
- If Con(SP_Σ), every SP_Σ model is a countermodel to the proposed signature-to-pure implication and specifically falsifies the pure axiom Diamond_ne U.
- If the signature-to-pure implication is proved, SP_Σ is inconsistent. Conversely inconsistency proves that implication by explosion.
- The reverse lift, pure SP⇒SP_Σ, is similarly equivalent to inconsistency of pure SP.

Not established here:

- a model of SP_Σ;
- consistency or inconsistency of pure SP;
- consistency or inconsistency of signature SP;
- an unconditional model separation refuting the conjectured arrow.

The signature profile model establishes the needed Max-consistency facts and finite atom decompositions. Its actual-root behavior does not make it a full SP model. It cannot be used to remove the conditional clause in the countermodel consequence.

For finite Σ the more detailed result in `finite-c5-signature-cells-20261022.md` strengthens the numerical contrast: under SP_Σ, A_1 has exactly the product of the singleton extensional type-domain sizes of its relational constants, which is at least2. Under pure SP, it has exactly1 atom. This corroborates the obstruction but adds no missing consistency proof.

## 6. Sharp boundary for signatures containing only individual names

This subsection is outside the map's standing convention that an admitted Σ contains a relational constant. It clarifies why individual names must not be conflated with relational names.

### Exactly one individual name

Let Σ={a:e}, with no relational constants. Then every pure-Max model, expanded by any choice of a current individual for a, satisfies Max(C(a)). In particular CP({a}) holds.

Use the audited unary Possibility+ consequence of pure Max: if a pure P(x) is C-consistent for some individual, then

    Max(C)⊢∀x Diamond P(x).

Its proof is constructive at the consistency level. Given a C-model with P(b), attach a singleton coalesced root whose sole individual maps to b. The resulting C-model satisfies the pure sentence

    Q:=E_1∧∀x Diamond P(x).

Hence pure Max gives Diamond Q. At a Q-point every transported current individual is its sole individual and possibly satisfies P. Base4 then yields Diamond P(x) for each actual x. This proof does not require the original model itself to admit a generic named expansion.

Now any closed C(a)-consistent sentence is P(a) for a pure P(x). The displayed consequence gives Diamond P(a) in every expansion of every pure-Max model by an arbitrary actual a. Those are all the signature possibility-Max instances. Since pure optional conditions retain their truth under the expansion, every pure-Max-consistent pure P remains consistent with Max(C(a)).

Therefore SP_{a:e}⇒SP_pure follows directly by restricting its schema to pure P. No converse SP implication is proved here: the unary ordinary-possibility argument is not automatically a distinctness-preserving-possibility argument.

### Two or more individual names

Let a,b:e be distinct symbols in Σ. Put A_2:=F∧E_2. The singleton pure-profile model makes Atom(A_2) consistent with pure Max. But both

    A_2∧a=b,       A_2∧a≠b

are C(Σ)-consistent in full extensional two-individual models. Two signature-Max instances split A_2. Thus CP(Σ) fails. As before pure SP's Atom(A_2) law makes the two SP theories incompatible, and the signature-to-pure arrow is equivalent to inconsistency of SP_Σ.

Together with §3 this exactly classifies **pure-Max consistency preservation under added constant symbols**: it holds for the empty signature and for one individual constant alone; it fails as soon as there is a relational constant or at least two individual constants. This classification concerns Max consistency preservation. It is not an unqualified classification of SP implications, because an inconsistent antecedent entails every theory.

## 7. Status

**Settled:** explicit pure nonconservativity for every map-admitted signature, two-instance splitter obstruction, and the reduction of the conjectured arrow to inconsistency of signature SP. The isolated one-individual-name exception is proved separately.

**Unsettled:** consistency of signature SP, and therefore the conjectured implication itself as an unconditional theorem/nonimplication question. The next required ingredient is a consistency or inconsistency result for the antecedent, not a generic-expansion or conservativity proof, since the latter is already impossible in the map's admitted signatures.

## 8. A positive comparison lemma for infinite reservoirs of names

This does not alter the pure-to-signature obstruction. It identifies a setting where a language-extension conservativity argument really does work, and prevents an unjustified extrapolation of the finite-signature splitter result.

Suppose Σ⊆Σ′, and for every type τ at which Σ′ adds new constants, Σ already contains infinitely many constants of type τ. Then:

1. Max(C(Σ′)) is conservative over Max(C(Σ)) for old-language sentences and preserves consistency of old-language conditions.
2. SP_Σ′ entails SP_Σ, and is conservative over SP_Σ for old-language sentences and conditions.

These claims concern comparison of two specified nonempty reference languages. They do not say that a given model of the smaller theory has a generic expansion on its same domain.

For the Max assertion, inclusion on old instances follows from the conservativity of C under extra constant symbols. For consistency preservation, suppose a contradiction from Max(C(Σ′))+Γ has a finite proof, where Γ uses only old-language sentences. The whole finite proof, including any certificates for logical-equivalence instances, mentions only finitely many new constants d_1,…,d_r and finitely many old symbols. Choose distinct old names c_i of the same types, outside that finite support. Replace each d_i by c_i, fixing the old support.

Every C(Σ′) proof step becomes a C(Σ) step. Every Max inequality A≠B remains licensed after this replacement: if C(Σ) proved the renamed identity, injectively renaming the fresh c_i back to d_i would give a C(Σ′) proof of A=B, contradicting its original side condition. Thus the transformed proof is a contradiction from Max(C(Σ))+Γ. This proves preservation without choosing interpretations for infinitely many generic names in a pre-existing model.

For SP, Max consistency preservation first ensures that every old SP instance is a new SP instance. To prove the reverse conservativity of consequences, repeat the finite-proof renaming. A used new SP axiom is Diamond_ne P, where Con(Max(C(Σ′))+P). Let ρ replace its new symbols by the selected fresh old names. Then

    Con(Max(C(Σ))+ρP).

Indeed, otherwise a finite contradiction proof from that latter theory could be injectively renamed back, sending the selected c_i to d_i. Injective renaming maps its old Max axioms to valid Max(C(Σ′)) axioms, producing a contradiction with P. Therefore Diamond_ne ρP is an SP_Σ axiom. All non-C axioms in the renamed proof are licensed old SP instances, and the old Γ sentences used in the proof are fixed. An alleged new proof of an old consequence consequently gives an old proof.

The infinite-reservoir hypothesis is used only to find fresh old names outside a finite proof. A finite old signature does not supply that argument, and the finite complete-diagram splitters show why a replacement argument there can fail. In the original target comparison the old language is pure and has no name reservoir at all; §3's explicit counterexample still applies to every admitted new signature.

## 9. Exact Max-preservation boundary for finite signature extensions

Let Σ⊊Σ′ be finite signatures of constants in the original type system. Write CP(Σ,Σ′) for preservation, by Max(C(Σ′)), of all Max(C(Σ))-consistent old-language conditions. Then

    CP(Σ,Σ′)
      iff Σ′ adds exactly one individual constant,
          adds no relational constants,
          and Σ contains no individual constants.

For the equal-signature case preservation is trivial. For a proper finite extension the displayed exceptional case is the only one. This is a classification of Max consistency preservation, not an unconditional classification of implications whose antecedents might be inconsistent.

### The positive case

Suppose Σ contains only relational constants and Σ′=Σ∪{a:e}. The unary Possibility+ argument in §6 relativizes to this fixed old signature:

    if C(Σ)+P(x) is consistent, then
    Max(C(Σ))⊢∀x Diamond P(x).

For precision, the singleton Σ-profile construction, whose component arrows range over every pointed C(Σ) structure, satisfies E_1∧∀x Diamond P(x) whenever P has a component witness. Thus that closed Σ-sentence is C(Σ)-consistent. Signature Max makes it possible. At a witnessing singleton point every transported current individual is the same individual, and base4 gives Diamond P(x) for every original current x. All old constants are relational, so their component interpretations impose no conflicting demands on a singleton root individual map.

Every C(Σ′)-consistent sentence has the form P(a) for an old-language P(x). Therefore any Max(C(Σ)) model, expanded by any current individual as a, satisfies every Σ′ possibility-Max instance. Old sentences keep their truth. This proves CP and hence SP_Σ′⇒SP_Σ. No reverse SP implication is asserted.

### A new relational constant

Suppose Σ′ adds c:τ with τ relational. In the full singleton extensional hierarchy choose any interpretation d of the finitely many old relational constants. Every value has a pure finite-table representative. Let

    Δ_d:=A_1 ∧ AND_(old relational b)(b=t_b^d).

Old individual constants, if any, all have the unique individual value at an A_1-point, so no extra old-name diagram is needed. This is a complete closed old-signature finite diagram. The appropriate old profile root (singleton-marker when there are no individual names, closed-profile when there are) proves

    Con(Max(C(Σ))+Atom(Δ_d)).

The atomhood assertion transfers to SP_Σ by universal-identity reflection. With all old interpretations fixed by Δ_d, the new c can still be top or bottom. Hence Δ_d∧R(c) and Δ_d∧¬R(c) are both C(Σ′)-consistent, with R as in §3. Two Max(C(Σ′)) instances split Δ_d. Therefore CP fails and SP_Σ is incompatible even with Max(C(Σ′)), hence with SP_Σ′.

Only finiteness of the **old** signature is needed for this construction. The new signature may in fact be infinite; the one selected new relational symbol supplies the split, and no infinite diagram is written. When both signatures are finite, each new relational constant multiplies the exact number of A_1 atoms by the size of its full singleton extensional type domain. Each such factor is at least2.

### A new individual constant when an old name already exists

Suppose Σ has a:e and Σ′ adds b:e. Let Δ be A_2, the assertion that all old individual names equal a, and the assertion that every old relational constant is its top relation. There are finitely many conjuncts. In the full two-individual extensional hierarchy, this specifies one complete unpointed old-signature structure: all old names designate one individual, the other is unnamed, and all old relations have their fixed top values.

The old closed-profile construction makes Atom(Δ) consistent with old Max, and old SP forces it. The new name b may be interpreted as a or as the other individual. Therefore Δ∧b=a and Δ∧b≠a are both C(Σ′)-consistent and two new-Max instances split Δ. Again CP fails and old SP is incompatible with new Max and new SP. Root distinctness of old name symbols is not contradicted: their transport may coalesce at the Δ component.

### Two new individual names when there were none

Finally suppose old Σ is relational-only and Σ′ adds distinct a,b:e. Let Δ:=A_2 together with the finitely many assertions that every old relational constant is top. The two individuals of this old finite structure are automorphic, so Δ is pointed-complete. The old singleton-marker profile construction makes Atom(Δ) Max-consistent and old SP forces it. The two consistent new-language conditions Δ∧a=b and Δ∧a≠b split Δ under new Max. This covers every remaining proper finite extension not in the positive case.

In all three negative cases the same consequences as in §4 hold:

    SP_Σ′ entails SP_Σ  iff SP_Σ′ is inconsistent,
    SP_Σ entails SP_Σ′  iff SP_Σ is inconsistent.

In particular every proper finite relational-only signature extension makes the corresponding SP theories incompatible. The exact positive one-individual-name case shows why that statement must not be broadened to every proper finite signature extension without a type qualification.

## 10. Actual individual-domain size under signature SP

There is also a simpler structural explanation of the individual-name obstructions. Suppose Σ has exactly u<∞ individual constant symbols c_1,…,c_u. Its relational-constant part need not be finite. Then

    SP_Σ⊢E_(max(1,u))^e.

For u=0, the singleton-marker Σ-profile root is a Max(C(Σ)) model of E_1. Express E_1 as the universal identity sentence ∀x∀y(x=y), using standing nonemptiness. Identity reflection transfers it to SP_Σ.

For u≥1, the closed-Σ-profile root has precisely those u individual-name symbols as its actual individuals. Hence it witnesses Max(C(Σ))-consistency of

    U_Σ:=∀x(x=c_1∨…∨x=c_u).

This is a finite universal Boolean combination of identities, so SP_Σ forces it. Signature Max also entails c_i≠c_j for every pair of distinct symbols, since C(Σ) does not prove their equality. Thus the names enumerate the actual e-domain bijectively and E_u follows.

Consequently, adding an individual name when there is already at least one, or adding at least two names when there are none, makes the two SP theories incompatible simply by their forced actual finite cardinalities. The old-theory sentence U_Σ (or E_1 in the zero-name case) is also a direct Max nonconservativity witness: the old profile model satisfies it, while the new Max theory makes a fresh named individual distinct from all the listed old ones.

This concerns the actual domain. It does not assert boxed E_u, does not require future transports to be injective for ordinary Box-accessibility, and does not prohibit the finite-cell components with fewer individuals used above. Infinitely many individual names require a different statement: Max already makes them pairwise distinct, but no infinitary enumeration sentence U_Σ has been introduced.
