# Vicinity and propositional Atomicity imply Actuality

## Original recorded proof

Cian Dorr (the argument and its use of BF for 5-necessity, 28 October 2026), with Claude Opus 5.5 (Anthropic), who completed the step showing that the atoms below the witness are self-atoms. The following proof is reproduced from the native result record with its cross-reference label expanded.

By the 5-necessity form of Vicinity, some truth $v$ entails every 5-necessary truth. We show that every atom $w\le v$ is a self-atom. Let $A:=\operatorname{Atom}_t(w)$. Since $w$ is an atom, $w\le A$ or $w\le\neg A$; suppose $w\le\neg A$. First, $\Diamond_5w$: otherwise $\Box_5\neg w$, so $v\le\neg w$, and with $w\le v$, $w=\bot$. As $\Box\le\Box_5$ and $\Box_5$ is K, $\Diamond_5\neg A$, that is, $\Diamond_5\exists z\, .\,\psi(z)$, where $\psi(z)$ says that $z$ falsifies the clause of $\operatorname{Atom}_t(w)$ for $z$. $\Box_5$ satisfies BF at type $t$: in the form of The Bounds of Possibility, Appendix D, $\Box_5p$ says that $p$ is $X$-necessary for every $X$ that is necessarily NKJF$_{\langle\rangle}$, and F$_{\langle\rangle}$ is BF for $X$; that definition is necessarily equivalent to the map's (Background). So $\Diamond_5\psi(z)$ for some $z$. But $\psi(z)$ is a truth-functional compound of identities among $z$, $w$ and $\bot$ (the order $\le$ is an identity), and such a formula $\varphi$ satisfies $\Diamond_5\varphi\to\varphi$: identities are necessary (NI), hence 5-necessary, so $\varphi\to\Box_5\varphi$ holds for identities and their negations by B for the S5 operator $\Box_5$, and so for their compounds; contraposing for $\neg\varphi$ gives the claim. Hence $\psi(z)$ holds, contradicting that $w$ is an atom. So $w\le A$, and $w$ is a self-atom. Wherever $w$ is true it is then a true atom, and a true atom entails every truth (it lies below $q$ or $\neg q$, and not below a falsehood); so $w\le\mathrm{Act}$, where $\mathrm{Act}$ is Actuality. Finally, were $v\land\neg\mathrm{Act}$ possible, Atomicity (type $t$) would give an atom $w\le v\land\neg\mathrm{Act}$, with $w\le v$ and hence $w\le\mathrm{Act}$, so $w=\bot$. So $v\le\mathrm{Act}$, and since $v$ is true, Actuality holds.

<a id="common-core-proof"></a>

## Alternative common-core proof

This is an alternative proof of the already recorded theorem, over C with current Vicinity and Atomicity_t. The existing Dorr/Claude proof and attribution are retained unchanged. The following argument uses only S4, Necessity of Identity and converse Barcan; it does not invoke the derived 5-necessity operator or its BF theorem.

Choose a true Vicinity witness w and put

    A_w := forall r (r -> w <= Diamond r),      s := w and A_w.

Thus s is true. We first prove, for every admitted predicate F:sigma t,

    forall x (s <= F(x))  ->  s <= forall x F(x).                 (1)

Suppose the antecedent T is true. Vicinity gives w<=Diamond(w and T). At any accessible evaluation where s holds, suppose an available x makes F(x) false. The A_w conjunct there gives w<=Diamond(s and not F(x)). Both bounds are positive identities and persist. The first supplies a further evaluation with w and T. Converse Barcan keeps the parameter x available there, so T gives Box(s->F(x)); the second bound and w give Diamond(s and not F(x)), a contradiction. This proves (1). In particular T itself was not transported; Vicinity supplied a new evaluation where it holds.

Now fix any current atom a. For each current q, either a<=q or a<=not q. Whichever disjunct holds is an identity, hence necessary. Apply (1) to these decisions to obtain

    s <= forall q (a<=q or a<=not q).                            (2)

C unconditionally proves that a true proposition deciding every q is an Actuality witness: when q is true, a<=not q is impossible. Necessitate only this unconditional theorem and combine it with (2). Writing Act for the Actuality proposition gives

    s and a <= Act                                              (3)

for every current atom a. If s and not Act were nonzero, Atomicity would supply an atom below it. Equation (3) would put that atom below both Act and not Act, contradicting nonzeroness. Therefore s<=Act. Since s is true, Actuality follows.

The proof collects atom decisions only beneath the single true core s. It neither infers ordinary BF nor assumes that every current atom remains an atom at future evaluations. Current ND_t implies Vicinity by an existing native arrow, so its Atomicity corollary is already derived and receives no duplicate result.

Source: OpenAI Codex, prompted by Daniel Kodsi, *Atomicity and Vicinity imply Actuality*, 26 October 2026, §§2–3, unpaginated. The common-core calculation was developed on 25 October from the mechanism of Christopher Sun's 19 October Vicinity argument. Independently checked ordinary mathematical proof; no historical priority or Lean certification is claimed.
