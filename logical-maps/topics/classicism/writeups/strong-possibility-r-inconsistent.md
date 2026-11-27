# Strong Possibility (pure) ⇒ ⊥

## A unary diagonal {#unary-proof}

**Theorem.** The same two closed pure sentences witness the inconsistency of Strong Possibility in the pure language and in every admitted signature. Each sentence is separately consistent with ordinary Maximalism in that language. Their distinctness-preserving possibilities are jointly inconsistent in Classicism.

Write $C$ for Classicism, $\Diamond$ for ordinary possibility and $D$ for distinctness-preserving possibility. Thus $DP$ says that for each currently true proposition $q$, one can reach a $P$-world from which $q$ is again possible. Ordinary Maximalism adds to $C$ every closed disequality of the language that is consistent with $C$ in that language. Strong Possibility requires $DP$ for every closed sentence $P$ consistent with this maximalist theory.

### A distinction that can become permanent

Can every distinction between individuals be made permanent? Two ordinary Maximalist worlds suggest opposite answers. In the first, any two distinct individuals have different names, and there is a future where the names stay apart forever. In the second, two individuals are distinct now but are sent to the same individual at every proper exit. Let

$$
 K=\forall x^e y^e\,[x\ne y\ \to\ \Diamond\Box(x\ne y)].
$$

Then $DK\to K$. Given distinct $x,y$ here, use $DK$ to visit a $K$-world from which their distinctness can be restored. They must still differ at the visit, since equality persists. By $K$ they have a further future where their distinctness is permanent. That future was accessible from here all along.

The first world will license $K$, forcing $K$ here under SP. At the second world we seek a law whose strong possibility forces $\neg K$ here. To find such a law, consider two testers that disagree about their common output.

Let $S=e\to t$ be the type of unary predicates, and call an entity of type $S\to t$ a *tester*. Suppose that for each individual $b$ we have an operator $Q_b$ taking testers to unary predicates. Form the Russell tester and its output

$$
 \rho_b(p)=\exists F\,(Q_bF=p\land\neg F(p)),
 \qquad d_b=Q_b\rho_b .
$$

Then $\rho_b(d_b)$ holds. If it failed, $\rho_b$ itself would witness it. Unpacking its truth gives, at every world, a tester $F$ with

$$
 Q_bF=d_b \qquad\text{and}\qquad \neg F(d_b). \tag{R}
$$

The rejection is at the world in question, and the witness may vary from world to world. This use of the Russell–Myhill diagonal adapts the earlier argument for a language with a higher-order relation name. [Earlier signature argument](strong-possibility-signature-r-inconsistent.html)

For any sentence $g$, form the law

$$
 H(g)=\forall b^e F^{S\to t}\,[Q_bF=d_b\ \to\ \Box(g\to F(d_b))].
$$

If both $H(g)$ and $g$ hold here, (R) gives a contradiction. The witness has the diagonal output, so the law makes it accept $d_b$, although it rejects $d_b$.

The outer box in $H(g)$ lets us draw the same conclusion from a *visit* to the law. An implication between identities reflects to the starting world.

$$
 D(x=y\to u=v)\ \longrightarrow\ (x=y\to u=v).
$$

If $x=y$ and $u\ne v$ held here, ask to restore $u\ne v$. The premise persists to the visit, where the implication gives $u=v$. That equality precludes the restoration. Each instance of $H(g)$ has this form because $\Box P$ means $P=\top$. Instantiating at the transported parameters gives $DH(g)\to H(g)$, hence $DH(g)\to\neg g$. Thus $K$ and $H(K)$ are the two sentences we seek, once we have an operator $Q$ for which each has an ordinary Maximalist witness.

### The two Maximalist worlds

Work first in a finite signature whose constants have closed types and which has an individual name $m$. Both licensing worlds use the definable-root construction over a complete family of pointed canonical action models for this language. Add a root with one entrance into each component. Its only outgoing arrows are its identity and these entrances followed by component arrows. At the root, relations may have arbitrary current extension, with one closed expression, their *descriptor*, giving their transported value across **all** entrances. Each public relation name uses itself as descriptor. Each root individual is assigned an individual name as its descriptor and travels to that name's denotation along each entrance. Substitution of descriptors for parameters gives an abstraction a single closed description on every component. We use the action semantics and completeness of Bacon and Dorr, “Classicism,” in *Higher-Order Metaphysics* (2024), §§3.5–3.6 and Appendix E in the draft numbering, and the definable-root construction described in the project notes. [Dorr’s one-name construction](coalesced-definable-root.html) · [Construction with a fixed signature](coalesced-definable-root-signature.html)

At either root every consistent closed sentence of the ordinary language (with no schematic type variables) is true at some entrance by completeness, hence ordinarily possible. In particular every consistent closed disequality holds at the root, since it is possible there and equality persists. Thus both roots satisfy ordinary Maximalism.

**The world for $K$.** Take one individual for each individual name, with that name as its descriptor. Two distinct root individuals therefore have different names $i,j$. A one-world classical model interpreting them differently witnesses the consistency of $\Box(i\ne j)$. Some entrance consequently makes the pair permanently distinct. This proves $K$.

**The world for $H(K)$.** Give each individual name $i$ two root individuals $i_0,i_1$, both with descriptor $i$, and interpret $i$ by $i_0$. In particular $m_0,m_1$ are distinct at the root and coincide at every proper exit. They can never become permanently distinct. At the root there is an exit merging them, and at each proper exit they are already equal. Hence $K$ is false at the root.

Now suppose $Q_bF=d_b$ there. Let $n$ be the name of which $b$ is a copy, and let $f$ be a descriptor of $F$. The identity persists to every entrance, giving $Q_nf=d_n$ uniformly in the canonical family. This is where we need a particular choice of $Q$. Its required property is proved below.

**Separation.** If a closed tester $f$ rejects $d_n$ at some continuation of a canonical component, then $Q_nf=d_n$ fails at some canonical entrance. [Proof of separation](#unary-reading)

Given separation, $f(d_n)$ holds throughout every component. In root parameters this says that $F(d_b)$ holds at every proper exit. Since $K$ is false at the root itself, $\Box(K\to F(d_b))$ holds there. We have obtained $H(K)$. The Russell witness in (R) concerns a tester at one world. The separation claim concerns a *single closed expression across all entrances*, which is why the local diagonal argument alone could not supply this licence.

### Removing names {#unary-signatures}

The two sentences $K,H(K)$ are pure. For the pure theorem one auxiliary individual name suffices. Any pointed pure model can interpret it, and forgetting it in the two licensing models preserves the sentences and pure Maximalism.

Let the public language be any set-sized free signature whose constants have closed types. This includes every signature admitted by the map. The consistency tests must be taken in the whole signature. Suppose ordinary Maximalism with either $K$ or $H(K)$ proved a contradiction there. The derivation uses only finitely many names and finitely many Maximalist disequalities. Keep this finite sublanguage and add a fresh individual name $m$. Every cited disequality is still a Maximalist axiom there. Otherwise its equality would be provable in the finite language with $m$. Reinsert the public names, replace $m$ by a fresh individual variable, and discharge that variable using existence at type $e$. This would prove the equality in the original language, contrary to the cited axiom. The two sentences contain no names to change, so the derivation would contradict the finite named case. This licenses the same two sentences even when the public language has no individual name. SP now gives both $DK$ and $DH(K)$. The first implies $K$ and the second implies $\neg K$.

### Proof of separation {#unary-reading}

Suppose $f$ rejects $d_n$ at an old world. We already know how $f$ and $\rho_n$ differ. The former can reject the old diagonal, and the latter accepts it everywhere. We need their *outputs* to differ. It suffices to find one individual $a$ at which the output of a tester reads “can this tester reject the old diagonal?”

A unary predicate can be recorded by giving each individual one copy where the predicate is true and two where it is false. Current values alone would lose information. A tester can ask whether its input equals a specified predicate, and two predicates agreeing here can differ at an individual that appears later. We therefore record the values at every old continuation. One marked pair tells the language when to read the copies and when to apply the tester. While the markers differ, choose a predicate agreeing with the recorded values. When they coincide, ask the tester about that predicate.

Here is the pure operator implementing this idea. For individual parameters $a,b$, abbreviate $a=b$ by $B$ and put

$$
\begin{aligned}
 L(x)&=\exists y\,[x\ne y\land\Box(B\to x=y)],\\
 \operatorname{Code}(r)&=(r=\lambda x.\Diamond r(x))\\
 &\quad{}\land\Box\bigl(\neg B\to\forall x\,[\neg L(x)\leftrightarrow\Diamond(B\land r(x))]\bigr),\\
 (Q_bF)(a)&=\Diamond\bigl(\neg B\land\exists r^S\,
                [\operatorname{Code}(r)\land\Diamond(B\land\neg F(r))]\bigr).
\end{aligned}
$$

Every output $p=Q_bF$ satisfies $p=\lambda x.\Diamond p(x)$, by reflexivity and transitivity of ordinary possibility and intensionality. Call such a predicate *possibility-fixed*. Every output also fails at $b$, since identical markers can never become distinct.

In an action model the worlds and arrows form a category, and individuals transport along arrows. A relation at $w$ is determined by its truth value for each arrow $h:w\to z$ and each tuple of arguments at $z$. Write $p_h(u)$ for a unary predicate's value at the arrow $h$ and individual $u$.

**Reading lemma.** Fix a pointed action model $(A,w)$ in a signature containing an individual name $b$. There is an action model with a new starting world above $w$ and an individual $a$ there such that, for every closed tester $f$,

$$
 (Q_bf)(a)\text{ holds at the new world}
 \quad\Longleftrightarrow\quad (A,w)\models\Diamond\neg f(d_b). \tag{T}
$$

*Proof.* Let $p$ denote $d_b$ in the old model. It is possibility-fixed and false of $b$ by the definition of $Q$. Keep the old model as a lower layer. Add an upper world for each $h:w\to z$, starting at $1_w$. Each old arrow $k:z\to z'$ gives an upper arrow from $h$ to $kh$ and an exit from $h$ to the lower $z'$. Composition is induced by old composition. Every arrow out of a lower world stays lower.

Over each individual $u$ at $z$ put one copy $u_0$, and a second copy $u_1$ exactly when $p_h(u)$ is false. A second copy, once present, persists along upper arrows. Indeed, truth at any later image of $u$ would already make $p_h(u)$ possibly true, hence true. Upper transport thus preserves the subscript. Exits forget it and apply the old transport. Lift every individual name to its first copy. Choose $a$ to be the second copy of $b$'s old denotation, which exists since $p(b)$ is false. The markers differ throughout the upper layer and coincide throughout the lower layer reached from it.

At each relational type, admit at $h:w\to z$ a pair consisting of an arbitrary set of upper rows and one admitted old entity of that type at $z$. An upper row specifies an upper arrow from $h$ and a tuple of arguments at its target. The old entity supplies all the values on exits. This defines the domains inductively on types, since the arguments of a relation have lower type. Interpret a relational constant by taking empty upper rows and its original denotation below. At a schematic type variable, copy the old carrier, transport, and any named value. Upper transport restricts the rows by composition and transports the old entity. An exit transports just the old entity. Upper arrows recover the first entry of the pair, and the immediate exit to $z$ recovers the second, so the resulting intension determines the pair.

To check closure under terms, first evaluate below. Induction on the term gives its old interpretation, since all domains and all continuations there are old. Term evaluation commutes with transport, so restricting an upper denotation along the immediate exit gives the old term on the projected parameters, an admitted entity. Its upper rows are unrestricted. In particular an abstraction takes its prescribed value on every target tuple, including tuples first appearing later.

At an upper world, $\Box(B\to x=y)$ says exactly that $x,y$ project to the same old individual. The immediate exit tests equality of their images, and that equality persists along every later exit. Thus $\neg L(x)$ holds precisely when the old predicate is true of the image of $x$.

Suppose $r$ passes $\operatorname{Code}$ at $h$. For each $k:z\to z'$ and *every* individual $u$ at $z'$, apply the boxed test upstairs at $kh$ to $u_0$. Its left side reads $p_{kh}(u)$. Its right side reads possible truth of the lower restriction of $r$ at $(k,u)$, since the markers coincide exactly on exits and every old continuation is available. The first conjunct of $\operatorname{Code}$ makes that possible truth equal to the actual row. Consequently the lower restriction of $r$ equals the entire transported $p$. Conversely, the term $d_b$ itself supplies a passing code at any upper world. It is admitted there and possibility-fixed, as every output of $Q_b$ is. Its lower restriction is the transported $p$, by preservation of old term denotations. The same row calculation therefore gives the boxed test.

A successful search by $Q_bf$ therefore chooses its code upstairs and ends downstairs where $f$ rejects the transported $p$. Conversely, given an old rejection, choose the passing code at $1_w$ and cross along the rejecting arrow. This proves (T). $\square$

To prove separation, take a continuation where $f(d_n)$ fails as the old base and use the name $n$ as the marker in (T). The identity arrow witnesses rejection by $f$. No old arrow witnesses rejection by $\rho_n$, since $\rho_n(d_n)$ holds everywhere. The new model therefore distinguishes $Q_nf$ from $Q_n\rho_n=d_n$ at the upper twin. By completeness in the named language this refutation also occurs at a canonical point. If $f$ contains schematic type variables, this use of completeness requires witnesses at those sorts. Canonical models supply them, transport preserves them upon changing base, and the upper model retains their carriers. This proves separation and completes the argument. $\square$

## Earlier proof using atomlessness and a six-place diagonal {#uniform-pair}

**Theorem.** In Classicism there are two closed pure sentences $A_0$ and $\Psi$, each consistent with ordinary pure Maximalism, for which
$$
 C\vdash\neg(\Diamond_{\ne} A_0\land\Diamond_{\ne}\Psi).
$$
Consequently pure Strong Possibility is inconsistent. The same two sentences witness the inconsistency of Strong Possibility for every free signature admitted by the map, with both consistency tests taken in that signature.

Here $A_0$ says that the Boolean algebra of propositions is atomless. Write $D=\Diamond_{\ne}$. At a $DP$-point, each currently true proposition can still be made true after reaching a $P$-point. Applying this to a true strong atom shows that $DA_0$ rules out Strong Actuality. To define $\Psi$, the proof uses the Russell–Myhill diagonal at the type of six-place relations on individuals. An auxiliary world for each old arrow and individual tuple tests the entire interpretation of such a relation. This produces a sentence true at a definable Maximalist root whose distinctness-preserving possibility contradicts the diagonal whenever Strong Actuality fails.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, found the construction and completed the proof on 27 November 2026. Independent GPT-6 researchers checked the native types, full action-model extension, descriptor argument, and the two licences in each signature. The diagonal adapts the earlier [higher-order-signature proof](strong-possibility-signature-r-inconsistent.html) of Cian Dorr and Claude Fable 5.2 (Anthropic), prompted by Cian Dorr. Lean verifies both map statements. The [unary proof](#unary-proof) gives another choice of incompatible possibilities.

## The closed terms

Let \(S=e^6t\) denote the type of six-place relations on individuals. Write a tuple of six individuals as \(\bar a=(a_0,a_1,b_0,b_1,c_0,c_1)\). With this tuple as parameter define

\[
 A=(a_0\ne a_1),\quad B=(b_0=b_1),\quad
 T=\neg A\land\neg B\land c_0\ne c_1,\quad
 U=\neg A\land\neg B\land c_0=c_1.
\]

Put \(x\sim y\) for \(\Box(U\to x=y)\). Let \(C_i(x)\) say that exactly \(i\) current individuals \(y\) satisfy \(x\sim y\), using the usual finite first-order formula, for \(1\le i\le7\). Set \(J=\exists x\,C_7(x)\). These formulas all use the same six transported parameters. For \(p:S\) put

\[
\begin{split}
 \operatorname{Code}(p;\bar a)={}&(p=\lambda\bar v.\Diamond p(\bar v))\\
 &{}\land\Box\bigl(T\to\forall v_1\ldots v_6\,[(\bigwedge_{i=1}^6 C_i(v_i))
              \to(J\leftrightarrow\Diamond(B\land p(\bar v))) ]\bigr).
\end{split}
\]

Define

\[
\begin{split}
  (QF)(\bar a)&=\Diamond\left(A\land\exists p^S\,[\operatorname{Code}(p;\bar a)
                              \land\Diamond(B\land\neg Fp)]\right),\\
  \rho(x)&=\exists F^{St}\,[QF=x\land\neg Fx],\qquad d=Q\rho.
\end{split}
\]

Here \(QF\) abbreviates the six-individual lambda abstraction displayed above. Equivalently its uncurried relation takes one input of type \(St\) followed by six inputs of type \(e\). In particular \(d=Q\rho\) is a relation of type \(S\). All its output rows are fixed by ordinary possibility: \(QF=\lambda\bar v.\Diamond((QF)(\bar v))\) by S4 and intensionality. The Russell–Myhill argument gives \(\rho d=\top\). If \(\rho d\) were false, \(F=\rho\) would make it true. Unfolding the resulting theorem gives

\[
 C\vdash\exists F^{St}\,[QF=d\land Fd\ne\top]. \tag{1}
\]

## Testing a marked term

Let \(f:St\) be any term closed apart from one freely interpreted individual marker. Suppose \(f(d)=\top\) is not provable in marked C. By completeness a countermodel to the identity has an ordinary continuation where the proposition is false. Repointing there, with the transported marker, gives a marked C action model \(w\) with \(\neg f(d)\). Keep its generated cone unchanged. At \(w\) fix the marker's original individual as an anchor.

Adjoin a new root \(o\) and an arrow \(l:o\to w\). For every old arrow \(h:w\to z\), including the identity, and every tuple \(\bar u\in D_e(z)^6\), add a fresh object \(t=t_{h,\bar u}\), with arrows \(i_t:o\to t\) and \(k_t:t\to z\). Impose \(k_t i_t=h l\). Also add one fresh classical terminal \(v_t\) and an arrow \(j_t:t\to v_t\). These generators and the old compositions impose all the identifications. In particular every path from \(o\) into the old cone factors through \(l\), and every path from \(t\) into the old cone factors through \(k_t\).

Choose a root tuple \(\bar a\) with the three pairs distinct at \(o\). All six entries go to the anchor under \(l\). At each \(t\) merge the first pair and keep the other two pairs distinct. At \(v_t\) keep only the \(b\)-pair distinct. Under \(k_t\) all six transported root entries map to \(h\) of the anchor. Thus \(A\) holds only at \(o\), \(B\) holds precisely in the old cone, \(T\) holds at the test objects \(t\), and \(U\) holds at the private terminals \(v_t\), for this choice of \(\bar a\).

At \(t\) the relation \(x\sim y\) is exactly \(j_tx=j_ty\). Implement its fibres as follows. For each \(i=1,\ldots,6\) create one fibre of size \(i\) and send *every* member of that fibre to \(u_i\) under \(k_t\). Add one fibre of size seven precisely when \(d(\bar u)\) is true at the old point \(z\). Its elements can go to the transported anchor. Use two further fibres of size eight for the incoming root controls and any fillers. For example take distinct local control representatives except for the already merged \(a\)-pair. Place the two \(b\)-representatives in opposite size-eight fibres, the two \(c\)-representatives in the same one, and send all control representatives to the transported anchor under \(k_t\). Use the fibres themselves as distinct terminal individuals, and let \(j_t\) send each element to its fibre. This realizes the cardinalities and both required individual compositions. The colour of the optional fibre uses the value of an already defined closed term in the **original** component. Adding predecessors does not enter its interpretation there.

For clarity, the new relations form an action model at every standard type. At a test object \(t\) admit an arbitrary current row, one entire \(z\)-entity, and one entire \(v_t\)-entity. At \(o\) admit an arbitrary current row, an arbitrary current row at each \(i_t\), one whole \(v_t\)-entity per \(t\), and one whole \(w\)-entity. Its value transported to \(t\) has the prescribed test row, prescribed private entity, and old entity transported along \(h\) from \(w\). The terminal hierarchies are full. These descriptions are inductive on types since rows use only lower-type arguments. Distinct entities are separated at their differing row or in a continuation of their differing old or terminal component. Lambda abstraction takes the body row on *all* target arguments at each new row, and takes the native abstraction in the original or terminal cone on transported parameters. Hence every abstract has the prescribed form, including those with new higher-type parameters. The test objects consequently preserve the equation $k_t i_t=h l$ also on higher-type parameters. The marked individual of the new pointed test can be any root individual transported to the original anchor.

## What the code determines

If \(p\) satisfies \(\operatorname{Code}(p;\bar a)\) at \(o\), its old projection equals \(d\) as a **whole** \(S\)-entity at \(w\). To check an arbitrary old row choose \(h:w\to z\) and any six current individuals \(\bar u\) at \(z\). At its test object choose a member of the size-\(i\) fibre as \(v_i\), independently at each coordinate. The antecedent in the code holds. Possibility of \(B\land p(\bar v)\) there is precisely possibility of the projected row of \(p\) on \(\bar u\) at \(z\), since the old continuations are exactly those through \(k_t\). The first code condition makes that row possibility-fixed. Its possibility therefore equals its current truth at \(z\). The colour \(J\) is exactly the previously recorded truth of \(d(\bar u)\) there. Every old row on every old tuple agrees, proving equality by intensionality.

Conversely \(p=d\) passes the code at \(o\). Its rows are possibility-fixed by construction. At a test site *every* member of the size-\(i\) fibre has the stipulated old image, so the comparison holds for every tuple satisfying the antecedent. The transported selected root parameters disable the comparison everywhere else.

It follows that \((Qf)(\bar a)\) is true at \(o\), using \(d\) as code and the old \(w\) itself for \(B\land\neg f(d)\). But \((Q\rho)(\bar a)\) is false. The only possible site satisfying \(A\) is \(o\) itself. Every passing code equals \(d\) throughout the old cone, and \(\rho(d)=\top\) throughout that cone. Thus \(Qf=d\) is not a theorem of marked C.

Consequently no standard marked term solves (1): whenever a marked term satisfies the required identity, it fails the required disequality in the term algebra.

## The contradiction at a proposed Strong Possibility point

Let \(V\) be the standard coalesced definable ordinary pure Maximalist root. Its sole individual supplies the construction's auxiliary marker. Every relational entity there has a closed one-marker term descriptor, evaluated on its marked target at every proper exit. An abstraction with root parameters has as descriptor the same abstraction with their descriptors substituted. Root identities imply provable identities between these descriptors: the components and their possible marker interpretations are complete for marked C. The scalar true only at the identity of the root is a true strong atom. It decides every root proposition there and transports to bottom at each proper exit, so Strong Actuality (\(\mathrm{SA}\)) holds at \(V\). [Descriptor root](coalesced-definable-root.html)

If \(QF=d\) holds at \(V\), the descriptor \(f\) of \(F\) satisfies \(Qf=d\) provably in marked C. The test just proved gives provable \(f(d)=\top\). Consequently \(Fd=\top\) holds at every proper exit of \(V\). The identity of \(V\) satisfies \(\mathrm{SA}\), so the following **one pure sentence** is true at this ordinary Maximalist point:

\[
   \Psi=\mathrm{SA}\land\forall F^{St}\,
       [QF=d\to\Box(\neg\mathrm{SA}\to Fd=\top)].
\]

Pure Strong Possibility excludes Strong Actuality. Indeed there is an ordinary pure Maximalist point with an atomless scalar algebra. If a Strong Possibility point had a true strong atom, use that atom as the true guard in distinctness-preserving possibility of atomlessness. At the intermediate atomless point the transported atom is nonzero since it is true at a continuation. Its necessary decision of every scalar persists, which makes it an atom and gives a contradiction. [Strong-atom obstruction](strong-possibility-and-strong-actuality-incompatible.html)

At a putative pure Strong Possibility point choose \(F\) from (1). The scalar \(\neg\mathrm{SA}\land Fd\ne\top\) is true. Apply \(\Diamond_{\ne}\Psi\) with that scalar as guard. This gives an intermediate site satisfying \(\Psi\) and a subsequent site restoring the guard on the transported parameter. Since identity persists, \(QF=d\) still holds at the intermediate site. Its boxed conditional gives \(Fd=\top\) at the subsequent site, contrary to the restored guard. This proves inconsistency of pure Strong Possibility.

Explicitly, let \(A_0\) be propositional Atomlessness. The strong-atom argument gives \(\Diamond_{\ne} A_0\to\neg\mathrm{SA}\) already in C. Hence (1) and the guard above give the pure failed disjunction
\[
     C\vdash \Box_{\ne}\neg A_0\ \lor\ \Box_{\ne}\neg\Psi.
\]
Neither \(\neg A_0\) nor \(\neg\Psi\) is provable in ordinary pure Maximalism. Only these two Strong Possibility instances are needed.

## Extension to an arbitrary free signature

Let \(\Sigma\) be any set-sized free signature admitted by the map. Use \(\Sigma^+=\Sigma\) when it already has an individual constant, and otherwise add one individual marker. The terms \(Q,\rho,d\) and the sentence \(\Psi\) remain pure.

The test of a closed \(\Sigma^+\)-term \(f\) works with its constants retained. Start with a marked old point where \(\neg f(d)\). Give each relational constant its prescribed old value at \(w\), empty new current rows and bottom values at private terminals. At each test object its old component is the transport along \(h\) of its value at \(w\). For each individual constant add a distinct individual at \(o\) with its specified image at \(w\). At each \(t_{h,\bar u}\) give its image a fresh fibre of size eight, distinct from the control and size-one-through-seven fibres. Send that entire fibre to \(h\) of the constant's old value. The image at the private terminal is its fibre. These choices commute with the imposed square and make no new size-seven classes. The control individuals themselves remain separate from the added individuals. The construction works for arbitrarily many constants since the fibres are disjoint and all eight-element fibres are ignored by the six selectors and the colour. The same proof gives
\[
 C(\Sigma^+)\vdash Qf=d\quad\Longrightarrow\quad
 C(\Sigma^+)\vdash f(d)=\top .
\]

The ordinary signature-Maximalist coalesced descriptor root gives every entity a closed \(\Sigma^+\)-descriptor and is strongly actual. It therefore satisfies the same pure \(\Psi\). The atomless ordinary signature-Maximalist point exists in this same signature, so signature Strong Possibility excludes Strong Actuality and also gives \(\Diamond_{\ne}\Psi\). Applying the same single return guard to (1) gives the contradiction for signature Strong Possibility, including first-order signatures and infinite sets of names. [Signature descriptor root](coalesced-definable-root-signature.html) · [Atomless model in the given signature](#an-atomless-ordinary-maximalist-point)

## An atomless ordinary Maximalist point

Fix a pointed ordinary Maximalist model \(K,w\) for the given signature, for example the [signature descriptor root](coalesced-definable-root-signature.html). Take two copies \(G,X\) of the Cantor space \(2^{\mathbb N}\), with \(G\) acting as a group by coordinatewise addition modulo two. Add a new root with the individuals of \(w\), loops indexed by \(G\) fixing all individuals, and an entrance to an independent copy of \(K,w\) for each \(x\in X\). Each entrance absorbs every loop and acts identically on individuals. Include all old postcomposites.

At each relational type \(\tau\) a root entity consists of a locally constant table on \(G\) of current rows and an independent locally constant function \(X\to D_\tau(w)\) of whole old entities. Both ranges have the discrete topology. Loops right-translate the table and fix the old section. An entrance evaluates the section at its index. Give each relational name a constant table and the constant section of its prescribed old value. Individual names keep their old interpretations. Compactness of Cantor space gives a common finite prefix on which every entry of a finite list of tables depends. Thus the transported parameters of an abstraction are locally constant as whole entities along the loops, and evaluating its body on all current tuples gives another locally constant table. At the entrances the native abstraction on the transported old parameters is likewise locally constant as a whole old entity. This includes quantification over new target arguments. Differences of entities are witnessed on a loop or in a continuation of an old copy. The action therefore validates C, and the entrances retain every ordinary Maximalist possibility in the given signature.

At scalar type every nonzero loop row or old value occurs on a nonempty clopen patch. Split that patch into two nonempty clopen pieces. Restrict the scalar to the appropriate coordinate and one piece, setting it to bottom elsewhere. This gives a nonzero proper part, since the other piece retains a nonzero value witnessed on a loop or an old continuation. Thus the scalar algebra at this ordinary Maximalist root is atomless.

## Lean verification

Both exported proofs apply the same theorem for signatures whose constants have closed types. The first licence realizes $K$ at the ordinary named root. The second realizes $H(K)$ at the root with two copies of each individual name. In (T), the upper term $d_b$ itself supplies the passing code. [Permanence and reflection](../lean/Classicism/StrongPossibility/Permanent.lean) · [First licence](../lean/Classicism/StrongPossibility/UnaryUniformPositive.lean) · [Second licence](../lean/Classicism/StrongPossibility/UnaryUniformNegative.lean) · [Diagonal reading](../lean/Classicism/StrongPossibility/UnarySeparation.lean) · [Uniform signature theorem](../lean/Classicism/StrongPossibility/UnaryArbitrarySignature.lean)

The exports are `Classicism.Map.strong_possibility_r_inconsistent` and `Classicism.Map.strong_possibility_signature_r_inconsistent`. The registry verifies both. The proof-body audit traces each to the two licences, the reflection arguments, the Russell witness, and the unary reading. Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`. From `logical-maps/`, run `python scripts/pmap.py lean-check classicism` to check the generated statements and audit their Lean axioms. From `topics/classicism/lean/`, run `lake env lean scripts/StrongPossibility.lean` to trace both proof bodies to the unary reading theorem. [Proof dependency check](../lean/scripts/StrongPossibility.lean)
