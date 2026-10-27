# Generic-point audit: C5 and qualified left-inverse observers

Ordinary mathematical research and independent audit by OpenAI Codex, 25 October 2026. Direct source for the generic-point observer theorem and its qualified-left-inverse strengthening: `misc`, this note, §§1–5, unpaginated. No database or formal-verification status is changed.

**Audit verdict.** The full Boolean-valued construction can be evaluated at a generic ultrafilter on its atomless component while retaining the ordinary quantifier truth clauses and C5. Homogeneity then supplies ordinary logical separation. If a proper nonzero forcing interval is internally isomorphic to the whole Boolean algebra, the same construction supplies **SplitMono**, separation by observers with admitted qualified left inverses. The isolated-atom reader alone would not establish this strengthening; explicit injective replacement observers are constructed in §4.

## 1. Metatheory, admitted domains and generic truth

Let M be a countable model of ZFC and let A be a nontrivial atomless complete Boolean algebra according to M. M need not be externally well founded. External references to an M-set mean its members in the membership structure of M. No external completeness of the resulting countable Boolean algebra is assumed.

Internally in M put

```math
B=2\times A,
```

choose a nonempty individual domain, and form the full relational hierarchy with proposition domain B and all M-functions at admitted arrow types. Externalize the standard finite types and their M-function domains. Boolean operations and quantifiers are interpreted by the M-Boolean operations and M-coded meets and joins. Equality at every type is crisp: its value is 1_B for identical objects and 0_B otherwise. This is the full Boolean-valued hierarchy used in the earlier [analysis countermodel](../dependencies/c5-functional-choice-analysis.md), §§2–3, now with a different designated truth evaluation.

Choose an M-generic ultrafilter G on A and declare

```math
(\epsilon,b)\text{ true}\quad\Longleftrightarrow\quad b\in G
\tag{1}
```

Such a G exists externally by enumerating the countably many M-coded dense subsets and constructing a descending filter. An M-maximal antichain is externally maximal with respect to the externalized algebra: the relevant assertion quantifies over exactly its M-elements. Thus genericity has its ordinary intended meaning even when M is not well founded.

### The precise generic quantifier lemma

If $`(b_i)_{i\in I}`$ is a family coded in M and its M-join is b, then

```math
b\in G\quad\Longleftrightarrow\quad
\exists i\in I^M\;(b_i\in G)
\tag{2}
```

Inside M, take a maximal antichain below b refining the family: every member a of that antichain lies below some b_i. Add ¬b when nonzero. This is an M-maximal antichain in A, so G meets it. If b∈G, the member selected by G is below b and therefore below one of the b_i; upward closure puts that b_i in G. The reverse implication is immediate from b_i≤b. Boolean complementation gives the dual equivalence

```math
\bigwedge_{i\in I}^{M}b_i\in G
\quad\Longleftrightarrow\quad
\forall i\in I^M\;(b_i\in G)
\tag{3}
```

Only M-coded families are covered. G is not asserted to preserve arbitrary external meets or joins; such a claim would generally be false.

Every admitted predicate F is an actual M-function, so its range family over an admitted type domain is M-coded. Consequently (2)–(3) give the exact ordinary external existential and universal truth clauses for every admitted F. This includes higher-type domains, not just individuals. Formula denotations with finitely many admitted parameters remain M-coded: logical interpretation is performed internally over M-sets.

## 2. Lambda admission, identity and C5

Every standard finite lambda term, with finitely many admitted parameters, defines an M-function by the corresponding internal finite interpretation. The full M-function domain includes it. Externalization preserves its evaluation equation on every admitted argument. Thus the hierarchy is closed under the actual language's lambda abstraction; no function depending on the external generic G is added to a domain.

Crisp equality agrees with the native Leibniz equality. Equal inputs give identical predicate values. If x≠y, the M-admitted crisp haecceity $`z\mapsto\delta(z,x)`$ has values 1_B and 0_B at x and y, so the Boolean meet defining Leibniz identity is 0_B. This argument works at every admitted type. Extensional equality of M-functions is actual equality of their interpreted function objects.

The usual Boolean-valued soundness proof gives every fixed H theorem Boolean value 1_B. It is a standard finite proof interpreted in M, so external well-foundedness of M is unnecessary. If H proves a biconditional, its two Boolean denotations are identical for every assignment. Function extensionality in M therefore identifies their lambda abstractions. Hence C's Logical Equivalence is satisfied with its theoremhood restriction. Together with (2)–(3), this is an ordinary pointed C interpretation, not merely an algebra lacking classical quantifier truth.

Native Box remains

```math
\Box p=\delta_t(p,1_B)=
\begin{cases}1_B,&p=1_B,\\0_B,&p\ne1_B\end{cases}
\tag{4}
```

Every identity and every distinctness assertion is crisp. All ND instances and their separate boxes therefore have value 1_B. Thus C5 holds at the generic evaluation. Generic truth (1) does not change the native modality or identify it with truth in G.

## 3. Complete homomorphisms give whole logical observers

Any M-coded complete Boolean homomorphism E:B→B is an admitted tt object. Its Boolean preservation is literal. If F is an admitted σ-predicate, its M-coded family satisfies

```math
E\!\left(\bigwedge_{x\in D_\sigma}^{M}Fx\right)
=\bigwedge_{x\in D_\sigma}^{M}E(Fx),
\tag{5}
```

and likewise for joins. Since this holds internally for every admitted F, it identifies the whole quantifier-composite operations. Their identity propositions have value 1_B. The same applies to the whole Boolean-composite identities. The translated equality clauses follow from crisp equality and endpoint fixing.

Thus E is Good_Δ for **every finite requested list Δ**, with the exact whole-operation qualification. This uses M-completeness for M-coded families, precisely the families appearing in the admitted quantifiers. It does not rely on current material preservation being promoted to whole identity.

Assume the following internal homogeneity condition:

```math
\bigvee_{\alpha\in\mathrm{Aut}^{M}(A)}^{M}\alpha(b)=1_A
\qquad(0<b\in A)
\tag{6}
```

Weak homogeneity implies (6): otherwise a nonzero complement of that orbit join would have zero intersection with every translate of b, contradicting weak homogeneity. Aut^M(A) and the orbit are M-sets.

For each internal automorphism α, the observer

```math
T_\alpha(\epsilon,b)=(\epsilon,\alpha(b))
\tag{7}
```

is a complete Boolean automorphism of B. Its internal inverse is also Good at every type. For each nonzero b, (2) applied to (6) gives some internal α with α(b)∈G. Thus reversible observers (7) detect every nonzero proposition whose atomless coordinate is nonzero.

The remaining difference is the isolated atom a=(1,0). A simple atom reader $`(\epsilon,b)\mapsto(\epsilon,\epsilon1_A)`$ would detect it and establish OS, but is not injective. The next section replaces it with a qualified split injection.

## 4. An admitted split injection detects the isolated atom

Suppose there are a nonzero proper c∈A and an M-coded complete Boolean isomorphism

```math
h:A\longrightarrow A\mathbin{\upharpoonright}c,
\qquad\neg c\in G
\tag{8}
```

Here the interval has top c. Define internal B-operations

```math
\begin{aligned}
J(\epsilon,b)&=(\epsilon,\;\epsilon\neg c\lor h(b)),\\
K(\epsilon,d)&=(\epsilon,\;h^{-1}(d\land c))
\end{aligned}
\tag{9}
```

Both are complete Boolean homomorphisms. In the second coordinate, the decomposition of A into the two intervals below c and ¬c makes this transparent: J uses the first bit on the ¬c interval and h on the c interval, while K discards the ¬c interval and applies h^{-1} on the c interval. They preserve 0 and 1, complementation, and all M-coded joins and meets. Section 3 therefore makes both admitted, fully qualified observers.

Direct calculation gives the identity of whole admitted operations

```math
K\circ J=I_B
\tag{10}
```

Indeed $`(\epsilon\neg c\lor h(b))\land c=h(b)`$. On the other hand

```math
J(a)=(1,\neg c)
\tag{11}
```

is true at G by (8), while J(0)=0 is false. More generally J detects every nonzero difference with first coordinate 1, irrespective of its second coordinate.

The assumptions (6) and (8) hold for the usual Cohen and Levy-collapse Boolean completions used in the proposed mathematical countermodels. Below a basic forcing condition the forcing is isomorphic to the original forcing by reindexing its unused coordinates; the Boolean completion gives h. Choose one of two incompatible nonzero basic conditions outside G. Its complement belongs to G, giving c as in (8). This is an internal M construction. One need not claim that every arbitrary Boolean interval is isomorphic to A.

## 5. Full current SplitMono, and why it need not be necessary

Let p≠q be admitted propositions. Their Boolean symmetric difference is a nonzero pair (ε,b).

* If ε=1, J makes that difference true at G by §4.
* If ε=0, then b≠0. Section 3 supplies α with T_α(0,b) true at G.

Boolean preservation then says that the chosen observer makes p and q have different current truth values. In the first case its qualified left inverse is K; in the second it is T_(α^{-1}). Both witnesses qualify for every requested finite Δ. This proves every propositional SplitMono separation instance.

For relations, distinct M-functions differ at an admitted argument; iterating through the finitely many curried arguments supplies a tuple at which their proposition values differ. Apply the same propositional observer there. Conversely identical relations agree under every observer. Thus the full typed SplitMono schema holds currently.

The construction proves

```math
\boxed{C5+\mathrm{SplitMono},}
\tag{12}
```

at the generic point, and hence current OS. It does not prove □OS or □SplitMono. The isolated atom is nonzero but false at G. Existing C5 + necessary OS + OneAtom⇒Atomicity_t would rule out the atomless remainder, so necessary OS cannot be silently added here. No exact Boolean value of the global separation sentence is needed in this audit.

There is already an immediate closed pure contingency witness: B has exactly one Boolean atom, a. The native Actuality sentence therefore has Boolean value a, so ¬Actuality has value (0,1), is true at G, and has false native box. Thus C5+SplitMono does not force No Pure Contingency, independently of the later real-field application.

A proposed positive real-structure proof that lifts a split injection to a typed image still sees only image predicates. With a left inverse F for E, the reconstructed predicate value involves EF(Yx), which need not equal Yx. A left inverse gives FE=I, not EF=I. This is precisely the image-coverage gap identified in [the earlier CH/analysis audit](ch-analysis-audit.md), §6. Section 6 states the separate value computations needed to turn this into an exact CH or analysis counterexample.

## 6. Use for CH and analytical contingency; scope of this audit

This audit validates the model-theoretic and observer part of the proposed counterexamples. Mathematical truth values must still be computed in the internal full Boolean hierarchy, with their exact real-structure language and carrier capacity checked as in [the earlier forcing transfer proof](../dependencies/c5-functional-choice-analysis.md), §§3–5. Generic evaluation does not change any such Boolean value.

In particular, whenever an exact universal mathematical assertion U has previously verified Boolean value (0,1_A), it is currently true at G but □U has value 0_B. If its universal negation has value (1,0), that opposite assertion is currently false as well. Actual real-structure existence must be verified separately to exclude vacuity. These are the intended ground-versus-forcing value calculations for the main CH/analysis note; this audit does not replace them with external full-power-set assumptions about M.

For a Cohen completion over a constructible M, the analytical sentence asserting the existence of a nonconstructible real supplies the familiar forcing-versus-ground change, in the first-order field language with N via the earlier coding proof. For current CH versus possibly ¬CH, a collapse over a ground satisfying ¬CH is the appropriate orientation. The two orientations must not be swapped by informal references to “CH contingency”.

The core positive-transport proposal is therefore not justified by observer elementarity or by SplitMono alone. Sections 1–5 remove the previously identified obstacle to constructing C5 counterexamples with ordinary separating observers, and strengthen the construction to qualified left-inverse separation. The actual CH and analysis applications retain the explicit ground-model and forcing assumptions of their main construction.

No Lean, compilation, native-record edits, publication, or external-domain completeness assumption was used. This is an ordinary mathematical audit, without a claim of historical novelty.
