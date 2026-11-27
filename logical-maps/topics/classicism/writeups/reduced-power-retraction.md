# Functional Choice and strong atoms without the Barcan Formula

At the designated point Functional Choice holds and the Barcan Formula fails at every input type. Necessarily every atom is a strong atom, at every relational type, and necessarily there is a true strong atom. The construction uses ZFC.

## Current, entrance and return rows

Let $E_e^r=\{0\}$ and $E_e^s=\{0,1\}$. Let $j$ collapse the latter set to the former, and let each $h_i$, for $i\in\mathbb N$, send $0$ to $0$. For a relational type $\tau=\alpha_1\ldots\alpha_d t$, write $A^b=\prod_k E_{\alpha_k}^b$, also allowing the empty tuple. Inductively set
$$
 E_\tau^r=\mathcal P(A^r)\times
  \big(\mathcal P(A^s)^{\mathbb N}/{=^*}\big),
 \qquad E_\tau^s=\mathcal P(A^s)\times E_\tau^r.
$$
Two sequences agree modulo $=^*$ when their entire rows coincide at all but finitely many indices. The first coordinate gives the current extension. Write $j(S,x)=x$. For each $x=(R,[U])$ at $r$ choose one representative sequence $U^x$ and put
$$
 h_i x=(U^x_i,x).
$$
Thus $jh_i x=x$ at every type. Each individual $h_i$ uses chosen representatives. Only the aggregate along a free ultrafilter defines an arrow. The reduced sequence factor replaces the individually observable entrance rows of the [full retraction](full-two-object-retract.html).

## The action model

At the initial stage the base kind is $r$ and the index ultrafilter is principal on a singleton. The typed domains at a stage of kind $b$ with index ultrafilter $D$ on $I$ are the ultrapowers $(E_\tau^b)^I/D$. Interpret current application pointwise modulo $D$. A stage of kind $r$ has, for every family of free ultrafilters $U_l$ on $\mathbb N$ indexed by $l\in I$, a successor of kind $s$. Its indices are $(l,i)\in I\times\mathbb N$, and a set is large if its fiber at $l$ belongs to $U_l$ for $D$-almost every $l$. The arrow sends $[x_l]$ to $[h_i x_l]_{(l,i)}$. At $s$ a single step to kind $r$ retains $I,D$ and sends $[z_l]$ to $[jz_l]$. Take finite histories as objects and finite paths as arrows, with identities and concatenation. This is a set. All the maps on classes are well-defined. Changing the chosen representatives changes each $i\mapsto h_i x_l$ at only finitely many indices, so it has no effect on any entrance map.

Distinct relational entities have different extensions at some continuation. At an $r$-stage, on a $D$-large set of indices either the current rows differ, or the entrance sequences of rows differ on infinitely many indices. In the first case choose a distinguishing argument tuple at each good index. In the second choose $U_l$ containing the infinite set of disagreements at each good $l$, and choose a distinguishing tuple at the successor. An ultrafilter makes one orientation of the disagreement large, so the family of tuples separates the two extensions there. At an $s$-stage a difference is in either the current rows or the return coordinates on a large set of indices. In the latter case take the deterministic return and apply the $r$ argument. Equal entities remain coextensive by well-definedness. This proves the required intensional identity criterion, including for propositions.

Here are the details of term closure. Evaluate a variable by its value; local truth uses current application, entity equality, ordinary Boolean operations and quantifiers over the current base carrier. For $L=\lambda\bar y.\phi(\bar y,\bar a)$ on $r$-parameters, set its current row to $\{\bar y:\phi_r(\bar y,\bar a)\}$ and its $i$th entrance row to
$$
 \{\bar z:\phi_s(\bar z,h_i\bar a)\}.
$$
On $s$-parameters $\bar b$, give $L$ its local $s$-row and give it as return coordinate the $r$-value of this abstract on $j\bar b$. At each term form the $r$-case first. It requires just the current evaluations of proper subterms; hence the $s$-case can use that $r$-case without circularity. A compound proposition uses the same construction with the empty tuple, performing its local connective, equality, application or quantifier. Partial application reads the relevant rows on the transported supplied arguments, leaving the remaining argument places free.

The $j$-coordinate of each term at $s$ is its $r$-denotation on the returned parameters. At $r$, the current row of $h_i L$ and the current row of the abstract on $h_i\bar a$ coincide for cofinitely many $i$ as entire rows, uniformly in the newly bound arguments. The return coordinates coincide because $jh_i\bar a=\bar a$. For partial application the same calculation uses a finite intersection of the cofinite sets for the operator and supplied arguments. Thus denotations commute with the deterministic return and with every genuine ultrafilter entrance. Interpret a term at each iterated stage by the family of its base denotations. The ordinary Łoś induction gives the current truth computation for every formula; existential witnesses at the good indices form an admitted ultrapower element. The transport computation makes each abstract's extensions at all continuations those required by the action semantics. Together with extensional separation this yields a C model. In particular the defined ordinary box agrees with truth at all continuations. Compare the [varying-ultrafilter separation argument](iterated-ultrafilter-fronts.html).

## Functional Choice

Given a serial current relation at the initial $r$-stage, choose an allowed $Y_a\in E_\tau^r$ for each input $a\in E_\sigma^r$, where $\tau=\beta_1\ldots\beta_d t$. To define the selecting operation $X$ at type $\sigma\beta_1\ldots\beta_d t$, give $X$ the root row prescribed on $(a,\bar z)$ by the current row of $Y_a$ at $\bar z$. Prescribe its $i$th entrance row at $(h_i a,\bar w)$ by the current row of $h_iY_a$ at $\bar w$, and give value false on other inputs. Each $h_i$ is injective by $jh_i=1$, so this determines a row. Every sequence of such rows is admitted. For each fixed $a$ the current and entrance data of $X(a)$ agree with those of $Y_a$ up to eventual equality of entire rows. Thus $X(a)=Y_a$ as an entity, giving Functional Choice at every admitted output type.

## Strong atoms

The Boolean orders of relational entities at the two base kinds are the coordinate orders in the displayed products, with eventual inclusion in the sequence component. This follows from componentwise Boolean operations, or from the separation calculation. The sequence algebra has no atoms. For any nonzero sequence, partition the infinite set of its nonempty rows into two infinite parts and restrict the sequence to each. Consequently an $r$-atom has the form $(\{\bar b\},[\varnothing])$. At an entrance it is represented almost everywhere by an $s$-atom with empty current row and that singleton as its return coordinate. A return sends it back to the $r$-atom. The other $s$-atoms are singletons in the current $s$-row with bottom return component. These go to bottom on a return and remain there.

At every stage an atom is represented by base atoms almost everywhere by Łoś. The preceding calculations show that it transports through any finite path to a family consisting almost everywhere of atoms or bottom. Each decides every tester available there, which gives strong atomhood. This proves the boxed atom principle. Both base kinds have a true current singleton at $t$, also giving necessary Strong Actuality. The root proposition algebra is $\mathbf 2\times(\mathcal P(\mathbb N)/\mathrm{Fin})$ and has one atom.

## Failure of Barcan at every type

At input type $\sigma$, let the tester have full current $r$-row and let its $i$th entrance row be $h_i[E_\sigma^r]$. It holds necessarily of each current input. At an entrance the input is in the indicated image, up to representative changes at finitely many indices; at a return it recovers the original input by $jh_i=1$. The same calculation applies at every subsequent stage. But the first entrance has a family of inputs outside those images. At $e$ take the new individual $1$ at every index. At a relational type fix $a\in E_\sigma^r$ and give $z_i\in E_\sigma^s$ return coordinate $a$ but a current row different from that of $h_i a$. The common left inverse implies $z_i$ is outside the entire image of $h_i$. The input $[z_i]$ fails the tester. This gives $\forall x\,\Box Xx$ and $\neg\Box\forall x\,Xx$.

## Finite weakly rigid bounds at the root

Suppose a weakly rigid $F$ at $r$ has infinitely many current tuples. Choose distinct tuples $x_n$ from its extension. By weak persistence, the set of $i$ such that $h_i x_n$ lies in $F$'s $i$th entrance row must be cofinite for each fixed $n$: any infinite complement would be contained in a free ultrafilter at the first entrance. Denote these cofinite sets by $A_n$. For $i\in A_0$, take the largest $k(i)\le i$ with $i\in\bigcap_{n\le k(i)}A_n$. This index tends to infinity modulo the cofinite filter. On these $i$ give a tester full entrance row except for the single tuple $h_i x_{k(i)}$; give it full rows at the other indices and at the root. For a fixed current tuple $x$, injectivity of $h_i$ implies that any exclusion of $h_i x$ requires $x=x_{k(i)}$. This can happen at only finitely many indices, so the tester necessarily holds of each current tuple through any number of rounds. At the first free-ultrafilter entrance the family $h_i x_{k(i)}$ (filled arbitrarily off $A_0$) is in $F$ and fails the tester. This contradicts weak inextensibility.

Every root weakly rigid bound therefore has a finite current extension. It equals the corresponding finite union of tuple haecceities by weak persistence and weak inextensibility. In particular it is rigid. The finite-bound theorem gives rigidity of both canonical power predicates for such bounds, proving Tame Rigidity, Weakly Rigid Power and Rigid Power at the designated root. [Finite weakly rigid bounds and their canonical powers](https://github.com/dkodsi/Logical-Maps/blob/b92c3eb1029588b4634fce94ec0c39e73e06de7a/logical-maps/topics/classicism/background/rigidity.md#internally-finite-bounds)

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, developed this construction on 26 November 2026. Two additional GPT-6 research agents independently checked the ordinary mathematical proofs.
