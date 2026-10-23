# Non-extensional realizability choice: close analogy, no verified C transfer

OpenAI Codex source and mathematical audit, 22 October 2026. This note does not establish a countermodel to Relational Choice ⇒ Transversal Choice over Classicism. It identifies a genuine primary-source analogue and a concrete failure of the most direct attempted interpretation.

## 1. The precise source theorem

Fontanella and Geoffroy, *Preserving Cardinals and Weak Forms of Zorn's Lemma in Realizability Models*, §4.2, printed pp.16–17, define

    Func(f) := ∀x y y′(pair(x,y) ε f ∧ pair(x,y′) ε f → y=y′),

and NEAC by

    ∀z ∃f [f⊆ε z ∧ Func(f)
            ∧ ∀x y ∃y′(pair(x,y) ε z → pair(x,y′) ε f)].

Corollary 4.7 proves NEAC in their specified model M(κ). The paragraph preceding Proposition 4.6 explicitly distinguishes strong equality from weak extensional equality and notes existing realizability models of NEAC+¬AC. Corollary 4.8 gives formula-wise functional uniformization for classes as well. [Primary PDF](https://geoffroy.re/docs/fontanella-geoffroy-2020-preserving-cardinals-and-weak-zorn-in-classical-realizability.pdf).

This is a close structural analogue of RC: a represented binary relation has a functional subrelation, but its selector need not respect an extensional equivalence on inputs. It is not yet an interpretation of the map's types, proposition identities, lambda terms, or TC formula.

## 2. What strong equality means in the set-theoretic version

Krivine, *Realizability Algebras II: New Models of ZF+DC*, Proposition 13, printed pp.12–13, identifies Leibniz equality with the equality controlled by ground-model names. The proof separates distinct names using the ε-set {t}×Π. Proposition 14 verifies the equality laws. [Primary PDF](https://www.irif.fr/~krivine/articles/R_ZF.pdf).

Krivine, *Realizability Algebras III: Some Examples*, §1.5, printed p.7, Lemma 8, makes the same point through a conditional whose falsity value is empty if the ground terms differ, and is the consequent's falsity value if they agree. This is stronger than the weak equality used by the extensional ZF collapse. Sections 1.1 and 1.4, printed pp.2 and 6, give the forcing-algebra special case and raw realizability truth clauses used below. [Primary PDF](https://www.irif.fr/~krivine/articles/RA-examples.pdf).

Accordingly, one cannot silently reinterpret strong identity as coextension. Conversely, literal identity of raw names does not by itself validate C's Logical Equivalence schema.

## 3. Concrete failure of the raw-value interpretation of C

The following calculation is an independent audit of the naïve proposal to use raw realizability falsity values as proposition entities, literal equality as proposition identity, and the usual realizability clauses as the logical operations.

Use the degenerate forcing-style realizability algebra with underlying meet-semilattice

    P={0,1}, 0<1,
    Λ=Π=P,
    push, application, and process composition = meet,
    pole={0}, proof-like elements={1}.

This is coherent: the proof-like element 1 fails against stack 1. For a raw falsity value A⊆Π its realizers are

    A⊥={u∈P : ∀π∈A, u∧π=0},

and the implication falsity value is A⊥·B={u∧π:u∈A⊥,π∈B}.

Choose proposition parameters with raw values

    ⟦p⟧={1},  ⟦q⟧=∅.

Then

    {1}⊥={0},
    ⟦p→p⟧={0},
    ⟦q→q⟧=∅.

But H proves (p→p)↔(q→q), so C identifies the corresponding abstractions and hence their instances. The displayed raw values are distinct. Therefore this direct raw-value interpretation fails C's Logical Equivalence even before modal principles or choice are considered.

Using two tautologies avoids any dependence on which tautology the target language abbreviates by top. If top is assigned the customary empty falsity value, the same calculation also contradicts C's required identity (p→p)=top.

This is a counterexample to the general raw-value TRANSFER CLAIM, not a proof that every conceivable interpretation into realizability fails. It also does not claim that this particular two-condition algebra is an NEAC+¬AC separator; that is unnecessary for exposing the invalid transfer step.

## 4. Why the typed HOL paper is not already the missing interpretation

Raffalli and Ruyer, *Realizability of the Axiom of Choice in HOL (An Analysis of Krivine's Work)*, author preprint dated 2 February 2007, published in *Fundamenta Informaticae* 84(2), 2008, pp.241–258, uses two formula sorts: o={0,1} and τ=P(Π). See preprint §§3–4, pp.3–6. Section 7.2, pp.17–18, proves NAC with functionality expressed using algorithmic equality, explicitly not propositional equality. Section 5.1, pp.10–11, distinguishes these equalities. [Author's PDF](https://raffalli.eu/pdfs/ac.pdf); [publisher record](https://journals.sagepub.com/doi/abs/10.3233/FUN-2008-84206?download=true).

The author PDF fetch timed out. The exact preprint text was inspected in the author-uploaded full text, labeled as uploaded by coauthor Frédéric Ruyer, at [this mirror](https://www.researchgate.net/publication/29603263_Realizability_of_the_axiom_of_choice_in_HOL_An_analysis_of_Krivine%27s_work). No ResearchGate commentary, abstract-generated inference, or third-party theorem claim is used.

For our proposed transfer, interpreting C's t by their o would put the task in the ordinary two-valued extensional setting. Interpreting it by their raw τ instead retains the identity problem in §3. The NAC theorem itself does not supply another choice of C proposition entities with the required identity law.

## 5. What a quotient repair would still have to prove

One natural response is to identify raw values related by a uniform realizability equivalence, rather than retaining literal raw identity. This can repair Boolean identities at the level of a logical algebra. Miquel's *Implicative Algebras: A New Foundation for Realizability and Forcing*, §4, constructs Set-based triposes from implicative algebras; its framework includes classical realizability. [Primary paper](https://arxiv.org/abs/1802.00528).

That source theorem alone does not provide the required C interpretation. The outstanding points are concrete:

1. **Lambda identity and application.** Choosing one raw representative of each logical-equivalence class externally does not show that abstraction, substitution, application, and quantification are well-defined on those classes. In particular, pointwise equivalence of a varying family is weaker than a single uniform realizer for its universal closure. An arbitrary representative choice cannot be treated as a logical operation.
2. **Selector descent.** A raw NEAC graph can distinguish two input names that the proposed C quotient identifies. Strong functionality on raw inputs does not show that the graph becomes a well-defined functional relation on the quotient. Saturating it may introduce several output classes for one input class. This is precisely an additional compatibility obligation, not an automatic consequence of the source theorem.
3. **Identity and modality.** The interpretation must validate C's derived Intensionality and the definition Box(p):=(p=top). A rule preserving realizability of a biconditional is insufficient if it does not give the required identity of the proposition or relation entities.
4. **Actual quantifiers and failure transfer.** Raw realizability validity is not itself a two-valued Tarski satisfaction relation. A classical model obtained through completeness may add individuals. A claimed TC counterexample must be shown to survive that passage and the chosen type domains. Failure of extensional set-theoretic AC is not by itself failure of a specific admitted C-TC instance.

These are original transfer checks, not claims that the cited sources address or settle Classicism. No complete strictification or quotient construction meeting them was found here.

## Verdict

NEAC+¬AC is a real and relevant literature lead. The direct raw-name/raw-truth-value reading is demonstrably not a C model. The available typed HOL treatment does not remove that defect. A new interpretation proving C's Logical Equivalence and preserving all-type relational selection would be needed before this literature could settle RC⇒TC. No such interpretation or separation is established in this audit.
