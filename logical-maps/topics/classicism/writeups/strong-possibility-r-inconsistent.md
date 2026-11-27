# Strong Possibility (pure) ⇒ ⊥

**Theorem.** In Classicism there are two closed pure sentences $A_0$ and $\Psi$, each consistent with ordinary pure Maximalism, for which
$$
 C\vdash\neg(\Diamond_{\ne} A_0\land\Diamond_{\ne}\Psi).
$$
Consequently pure Strong Possibility is inconsistent. The same two sentences witness the inconsistency of Strong Possibility for every free signature admitted by the map, with both consistency tests taken in that signature.

Here $A_0$ says that the Boolean algebra of propositions is atomless. Write $D=\Diamond_{\ne}$. At a $DP$-point, each currently true proposition can still be made true after reaching a $P$-point. Applying this to a true strong atom shows that $DA_0$ rules out Strong Actuality. To define $\Psi$, the proof uses the Russell–Myhill diagonal at the type of six-place relations on individuals. An auxiliary world for each old arrow and individual tuple tests the entire interpretation of such a relation. This produces a sentence true at a definable Maximalist root whose distinctness-preserving possibility contradicts the diagonal whenever Strong Actuality fails.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, found the construction and completed the proof on 27 November 2026. Independent GPT-6 researchers checked the native types, full action-model extension, descriptor argument, and the two licences in each signature. The diagonal adapts the earlier [higher-order-signature proof](strong-possibility-signature-r-inconsistent.html) of Cian Dorr and Claude Fable 5.2 (Anthropic), prompted by Cian Dorr. Lean verifies both map statements. The [formalization](#lean-verification) gives a second choice of incompatible possibilities.

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

The formalization constructs the same closed six-place operator, proves the Russell inference in the native calculus, and tests every tuple at every accessible old object. The source of each test uses one descriptor for each entity. The direct old projection and the projection through a test object therefore agree at every type and every subsequent old arrow.

For the pure result, two definable Maximalist roots disagree on whether there are at least two individuals. The boxed return conditions using this sentence and its negation cannot both be possible in the distinctness-preserving sense. For the signature result the two roots disagree about whether one public relational name has empty current extension. The finite set of names used in any proposed derivation suffices to transfer the two consistency witnesses to an arbitrary admitted signature. The written proof above gives the additional uniform choice of the same two pure sentences in every signature.

The exported theorems are `Classicism.Map.strong_possibility_r_inconsistent` and `Classicism.Map.strong_possibility_signature_r_inconsistent`. From `logical-maps/`, using the Python environment described in the repository README, run `python scripts/pmap.py lean-check classicism` to rebuild the certificates, compare their types with the generated map statements, and audit their axiom dependencies.
