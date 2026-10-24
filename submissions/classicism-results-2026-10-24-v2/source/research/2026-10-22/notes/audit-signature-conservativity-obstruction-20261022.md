# Signature maximalization is not pure-conservative: independent audit

OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematical audit, not human checking or formal verification. No main records edited. This checks `profile-root-construction-20261022.md` §§1–4,6,9 against the exact signature records and the conjectured arrow `strong-possibility-signature-r-implies-strong-possibility-r.yaml`.

## 1. Verdict

**PASS:** for every signature Σ admitted by the bundle, meaning that it contains at least one constant of relational type, signature Maximalism is not conservative over pure Maximalism for pure sentences. A witness is

    A := Fregean ∧ ExactlyOneIndividual,
    P := Atom_t(A).

Pure Max+P is consistent by the audited pure-profile root. Signature Max proves ¬P by two explicitly licensed possibility instances. Pure SP proves P, and consequently pure SP is incompatible with signature Max and with signature SP.

**Necessary logical qualification:** this does not prove signature SP inconsistent by itself. It makes the conjectured implication

    SP_Σ ⊢ SP_pure

equivalent to inconsistency of SP_Σ. In particular, if SP_Σ is consistent, the implication is false. Without that consistency hypothesis no countermodel to the implication is supplied, because an inconsistent premise theory entails every schema.

The record's unqualified “the arrow holds iff … conservative” formulation therefore needs correction. Conservativity would suffice; its necessity requires consistency of SP_Σ. The nonconservativity witness settles the proposed conservativity route negatively, while the implication itself becomes a consistency question.

## 2. Fixed language and the independently valid implication SP_Σ⇒Max_Σ

The background convention fixes a signature of uninterpreted constants at admitted types and assumes a relational constant. There are no standing inequalities between distinct constant symbols and no nonlogical axioms about their values. The definitions are

    Max_Σ = C(Σ) + {¬E : E closed identity and C(Σ)⊬E},
    SP_Σ  = C(Σ) + {D Q : Q closed in L(Σ), Con(Max_Σ+Q)},
    Bq=∃r(r∧□(◇r→q)),    Dq=¬B¬q.

The record `strong-possibility-signature-r-implies-possibility-signature-r.yaml` has a sound proof. For C(Σ)-consistent Q, signature Max proves ◇Q. Its source construction establishes Con(Max_Σ), so Max_Σ+◇Q is consistent. SP_Σ therefore has the instance D◇Q. C proves D≤◇ and ordinary modal 4, giving ◇◇Q and then ◇Q. These are precisely the signature Possibility-Max instances, equivalent in C to Max_Σ.

This proof never passes through SP_pure and never assumes conservativity of Max_Σ over pure Max. Ordinary fresh-constant conservativity of C suffices for the separate implication Max_Σ⇒Max_pure, as the existing record states.

## 3. Why pure Max+Atom(A) has the required witness

The pure-profile root uses one actual individual and profiles T(z) of pure terms with just one possible free individual variable. Each relational object consists of an arbitrary actual extension and such a component-denotation profile. Outgoing arrows include every pointed component object (V,a) in a complete family of genuine C action models, and all their descendants. The components' quantifiers retain their target domains.

The model closure proof in the profile audit passes: finitely many root parameters are replaced by their pure z-profiles; abstraction keeps its bound variables bound; arbitrary actual extensions supply the root coordinate. H is validated by the ordinary local clauses, and H-theorem Logical Equivalence identifies both actual extensions and component profiles. Profile equality must be equality of denotations, not merely equality of truth at the initial component points. The all-descendant intension argument in `audit-profile-20261022.md` §4 and the finite-table argument in `parent-profile-atomicity-audit.md` supply that necessary detail.

At an A-point, Fregean extensionality and the unique individual make every finite type the unique full finite extensional hierarchy. For any fixed pure proposition T(z), finite truth-table elimination consequently yields one of the closed C-theorems

    ∀z(A→T(z)),       ∀z(A→¬T(z)).

Every table uses only admitted relational output types. Exhaustiveness comes from finite lambda-defined truth tables and extensionality under the discharged Fregean premise; it is not an optional extensionality assumption at the new root. After discharging the premises, theorem necessitation and CBF give the component identities A∧T(z)=A or A∧T(z)=⊥ at every pointed component, including points at which A is currently false.

At the new root A has false actual coordinate, since the root has more than two proposition entities. Thus for every root proposition p, the actual coordinate of p∧A is false and its profile is either bottom or A's profile. Hence p∧A is literally bottom or A. A is nonbottom because the complete family includes a full singleton extensional component satisfying A. This proves Atom(A) at the root.

Every C-consistent pure sentence has an outgoing witness, so the root satisfies pure Max. It is therefore a model of pure Max+P. This is a consistency witness for the selected strengthening, not a model of pure SP: its isolated-root collapse remains present.

## 4. The two signature witnesses split A

Choose any constant c of relational type τ=σ₁…σ_kt. Put

    R(c):=∀x₁…x_k c[x₁,…,x_k],

with R(c)=c when k=0. In the full singleton-individual extensional model, interpret c as top_τ or bottom_τ. All type domains are nonempty, so R(c) is respectively true or false. Every other constant can be assigned an arbitrary permitted value; no assumed distinctness of symbols interferes. Thus both

    A∧R(c),       A∧¬R(c)

are C(Σ)-consistent closed signature sentences. This check needs neither a signature-SP model nor a signature-Max expansion of the pure-profile root.

Signature Max therefore gives their ordinary possibilities, equivalently their nonbottomness. Write u=A∧R(c) and v=A∧¬R(c). C's Boolean laws give u∧v=⊥ and u∨v=A. If Atom(A), then u≤A and u≠⊥ force u=A, whence v=⊥, a contradiction. Consequently

    Max_Σ ⊢ ¬Atom(A).

The alternative splitter R(c):=(c=top_τ) works as well, using top_τ and bottom_τ in the same two extensional witnesses. The universally closed application version above is well typed even when some arguments have type e.

This proves nonconservativity outright: the displayed pure consequence ¬P of Max_Σ is not a pure-Max consequence, because §3 supplies a pure-Max model of P. The witness works for any admitted Σ, including a single propositional constant and signatures with no individual constants.

## 5. Pure SP forces P without Barcan or illicit necessitation

The universal identity co-persistence lemma used in the profile note is sound. If a universal finite Boolean combination U of typed term identities is false, choose an actual countertuple and a true DNF clause for its failure. Let q be the conjunction of that clause's disequality literals, or top if there are none. Its equality literals persist by NI. For each disequality a≠b, NI gives the C theorem ◇(a≠b)→a≠b, and necessitation of the corresponding closed C-theorem supplies the boxed conditional. These finite facts imply □(◇q→¬U), so the true q witnesses B¬U. Contraposition yields D U→U.

No interchange of a universal quantifier with □ is used. The actual countertuple supplies a single finite witness; existential introduction at later points is part of the fixed C logic. Terms inside the identities may contain quantifiers without invalidating NI.

The sentence P=Atom(A) is in this fragment after expanding Boolean order as an identity, for example

    A≠⊥ ∧ ∀p(p≤A→(p=⊥∨p=A)).

Section 3 makes P pure-Max-consistent, so D P is a licensed pure-SP instance. Co-persistence gives P. Combining this with §4 proves the incompatibility of pure SP with Max_Σ. Section 2 then yields incompatibility with SP_Σ.

## 6. A shorter incompatibility proof and the exact status of the conjecture

There is an independent route to the incompatibility which does not need the special co-persistence of P. The finite-support reflection lemma from `strong-possibility-degree.md` §2 works in any fixed signature:

    Max_Σ⊢Q ⇒ Max_Σ⊢B Q.

Its proof uses only finitely many signature inequality axioms, NI, and necessitation of a C(Σ)-theorem. Since Max_Σ⊢¬P, it follows that Max_Σ⊢B¬P, i.e. Max_Σ⊢¬D P. Pure SP contains D P by §3. Hence any pure failure of maximalist conservativity already yields this compatibility obstruction.

In particular SP_Σ proves ¬D P, while D P is a specific axiom of SP_pure. Therefore

    [SP_Σ entails every SP_pure instance]
        iff SP_Σ is inconsistent.                       (6.1)

The forward direction uses that one conflicting instance; the reverse is explosion. Similarly the reverse lift SP_pure⇒SP_Σ holds iff SP_pure is inconsistent, because SP_Σ entails Max_Σ and pure SP is incompatible with it.

What is established unconditionally is the existence of a pure-Max model of P, the theorem Max_Σ⊢¬P, and the finite incompatibility certificates above. What remains open here is the separate consistency of pure SP and of SP_Σ. The already proved consistency of Max_Σ does not establish either Strong Possibility consistency statement.

## 7. Record implication without editing it

The named record is currently `status: conjectured` with an empty proof. That status must not be silently replaced by a countermodel claim: no SP_Σ model has been constructed. Its proposed maximalist-conservativity premise is, however, refuted by the explicit pure sentence P. A mathematical correction should distinguish this from the original implication's remaining equivalence (6.1) to inconsistency.

Ordinary C(Σ) remains conservative over C. The obstruction arises from the additional maximalist inequality/possibility instances, not from adjoining bare uninterpreted constants. This distinction is essential because the Henkin constructions elsewhere use only the conservative fresh-constant extension of C and retain optional pure Max/SP schemata in their original language.

Validation: no main records were edited. The required bundle validator is run after saving this report and reported in the parent update.
