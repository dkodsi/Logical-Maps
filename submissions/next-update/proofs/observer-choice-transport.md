# Logical observers and Choice

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi. Direct source for the new transport arguments: `misc`, this note, unpaginated. Earlier results and constructions retain the attributions below.

## 1. Results and their exact scope

The two choice principles behave differently under ordinary logical observer separation.

1. **Positive, instancewise:** over C, ordinary propositional separation by observers qualified at the finitely many types in the displayed Functional Choice instance gives

```math
\mathrm{FC}_{\sigma,\tau}\longrightarrow
\Box\mathrm{FC}_{\sigma,\tau},\qquad \tau\ne e
\tag{1}
```

   C5 is unnecessary. Section 2 gives the proof.

2. **Negative, even with C5:** ordinary logical separation and current Relational Choice do not imply necessary Relational Choice. The existing qualitative-contrast model, evaluated at its unrestricted object $`W_1`$, satisfies

```math
\mathrm{C5}+\mathrm{OS}
+\mathrm{RelChoice}_{\rm all}
+\neg\Box\mathrm{RelChoice}_{et,e}
\tag{2}
```

   The same model fails $`\Box\mathrm{RelChoice}_{et,et}`$, so individual outputs are not responsible for the failure. It even has the stronger, already verified separation by observers with qualified left inverses, called **SplitMono** in the linked observer notes. Thus replacing OS in (2) by SplitMono does not repair the implication.

3. **An additional sufficient premise:** C5 + OS + Weak Rigid Comprehension + Relational Choice implies necessary Functional Choice and therefore necessary Relational Choice. The route uses existing Plenitude implications and (1); it does not rescue the implication with Relational Choice alone.

Here $`et=e\to t`$. OS is the full ordinary separation schema of [Logical observer separation and its hierarchy](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1. Its Good conditions are identities between whole Boolean and quantifier operations. All optional premises in these statements are current premises unless explicitly boxed.

## 2. Why Functional Choice reflects

Fix admitted $`\sigma,\tau`$, with $`\tau\ne e`$. Put $`\rho=\sigma\tau t`$ and

```math
\begin{aligned}
\mathrm{FC}_{\sigma,\tau}:={}&
\forall U^\rho\bigl[(\forall x^\sigma\exists y^\tau\,U[x,y])\to
\exists f^{\sigma\tau}\forall x^\sigma\,U[x,fx]\bigr],\\
U^E:={}&\lambda x^\sigma y^\tau.\,E(U[x,y])
\end{aligned}
```

Let $`\Delta`$ contain $`\rho,\sigma,\tau,\sigma\tau`$. The whole-operation Boolean and quantifier identities of a Good$`_\Delta`$ observer give

```math
E(\mathrm{FC}_{\sigma,\tau})=
\forall U^\rho\bigl[(\forall x^\sigma\exists y^\tau\,U^E[x,y])\to
\exists f^{\sigma\tau}\forall x^\sigma\,U^E[x,fx]\bigr]
\tag{3}
```

This calculation uses no equality atoms. In particular it requires no C5 identity-fixing lemma and no preservation of native Box.

Every $`U^E`$ is admitted by lambda formation. Current $`\mathrm{FC}_{\sigma,\tau}`$, instantiated at that admitted relation, makes the right side of (3) true for every $`U`$. Therefore every eligible observer accepts the proposition $`\mathrm{FC}_{\sigma,\tau}`$, and it accepts Top. The separation instance $`S_{t,\Delta}`$ identifies the two propositions. By the definition of native Box, that is $`\Box\mathrm{FC}_{\sigma,\tau}`$.

The crucial syntactic fact is that the witness $`f`$ occurs only in the argument term $`fx`$. The observer acts on the entire proposition $`U[x,fx]`$; it need not act on or invert $`f`$. No observer surjectivity, external reindexing of witnesses, or necessitation of an optional premise occurs.

The same proof covers a finite input tuple $`\bar\sigma`$, including the empty tuple, by replacing $`f^{\sigma\tau}`$ with $`f^{\bar\sigma\tau}`$ and listing all types quantified in the instance. The input variables may have type $`e`$; the output remains relational, exactly as the fixed language requires.


## 3. Extensional fullness at a trivial-symmetry object

The counterexample uses the symmetric ideally-full action construction already recorded in [Symmetric ideally-full models](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/groups/symmetric-ideally-full.yaml). Its domains contain precisely the symmetric relational intensions pinned by a finite set of base individuals. An intension at a flattened relational type $`\bar\sigma t`$ specifies an extension

```math
R(h)\subseteq\prod_jD_{\sigma_j}(\mathrm{target}(h))
```

for every outgoing arrow $`h`$. This is the standard relational presentation of the curried function hierarchy, not an enlargement of its type system.

**Trivial-symmetry fullness lemma.** In this construction, let the symmetry group at an object $`X`$ be trivial. Then every external relation on any finite tuple of admitted domains at $`X`$ is the current extension of an admitted relational entity at $`X`$.

**Proof.** Fix

```math
R\subseteq\prod_jD_{\sigma_j}(X)
```

Define the whole intension $`\widehat R`$, at source $`X`$, by

```math
\widehat R(h)=
\begin{cases}
R,&\mathrm{target}(h)=X,\\
\varnothing,&\mathrm{target}(h)\ne X
\end{cases}
\tag{4}
```

There are two separate admission obligations.

- **Pinning:** parallel arrows have the same target and hence exactly the same extension in (4). The intension is consequently pinned by the empty set. The arbitrary relation $`R`$ need not itself have finite support under permutations of its tuples: pinning here compares the extension rows at parallel arrows, while leaving their target-domain arguments fixed.
- **Target symmetry:** at $`X`$, the only required symmetry is identity, so there is no restriction on $`R`$. At every other target the extension is empty and is invariant under all its symmetries, at every argument type.

Thus $`\widehat R`$ is in the symmetric ideally-full domain and its extension at $`1_X`$ is $`R`$.

This also explains explicitly why higher types and currying cause no gap. A section obtained by inserting a current argument $`a`$ is evaluated at $`h`$ using the transported argument $`h\cdot a`$. A finite pin for $`a`$ makes that argument identical along parallel arrows agreeing on the pin, and (4) then gives identical rows for the section. Finitely many inserted arguments require only the union of their finite pins. Target symmetry of sections follows from the same symmetry condition already checked for the whole relation. Recursing through the finite argument tuple yields admitted curried sections and values. No operation selecting arbitrary intensions has been asserted. $`\square`$

The distinction in the final sentence matters: extensional fullness supplies every actual **relation graph**, not an operation representing each functional graph by identical intensional outputs. Thus it gives Relational Choice in a choice metatheory, but it does not give Plenitude or Functional Choice.

**Corollary (ZFC metatheory).** At a trivial-symmetry object, the full current Relational Choice schema holds, including all higher argument types and individual outputs. For an admitted serial $`U^{\sigma\tau t}`$, its current extension is an ordinary serial relation between sets. Choose one output in each nonempty fibre externally, and apply (4) to the resulting graph. Its representing relation is currently functional and included in $`U`$, precisely the unboxed formula. The same argument treats finite input tuples.

## 4. Apply the lemma to the existing qualitative contrast

Retain [the qualitative-contrast model](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/models/symmetric-qualitative-contrast.yaml) in its base-individual version. It has two objects $`W_0,W_1`$, each a copy of $`\mathbb N`$, with every bijection between every pair as an arrow. Each object uses finite pinning. Its symmetry groups are

```math
G_{W_0}=\mathrm{Sym}(\mathbb N),\qquad G_{W_1}=\{1\}
```

Evaluate it at $`W_1`$.

**C5.** Every arrow has an inverse, whose action supplies the inverse transport at every type. Thus identity and distinctness persist in every possibility, giving all-type boxed ND, exactly C5. The same bijective type transports give necessary BF and Functionality.

**Full ordinary logical separation.** This was proved for this exact evaluation in [Local and necessary observer separation](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/local-observers.md), §§2–4. There are two explicit classes of admitted observers: finite-permutation observers distinguish the unrestricted $`W_1`$-target components of propositions, and the principal observer of the atom consisting of all arrows into $`W_0`$ distinguishes their $`W_0`$-target components. Their Boolean and quantifier laws are whole-operation identities at every finite requested type list. Functionality then lifts propositional separation to every relational output type.

An independent general proof, and the stronger qualified-left-inverse verdict, are in [Fixed-point symmetry and left-inverse separation](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/fixed-point-symmetry-left-inverse-separation.md), §§5–6. In particular, this exact evaluation has full SplitMono; surjectivity and two-sided inverses are not assumed.

**Current Relational Choice.** The symmetry group at $`W_1`$ is trivial, so §3 gives extensional fullness and then Relational Choice at every input/output pair. In the specialized construction (4), the arbitrary selector row is used on all arrows ending at $`W_1`$, and the empty row on all arrows ending at $`W_0`$. The two domains at the different target objects need not be identified; the empty row at $`W_0`$ is well typed in its own domains.

**Failure after transport to $`W_0`$.** Every bijection $`W_1\to W_0`$ is an accessible arrow. The recorded finite-support transposition argument refutes Relational Choice at $`W_0`$, specifically the instance with input $`et`$ and output $`e`$. It is restated next to make the failed instance and admission conditions explicit.

Let

```math
U[X,y]:=Xy\lor\neg\exists z^e\,Xz
\tag{5}
```

This is an admitted closed term of type $`(et)et`$ and is serial. Suppose an admitted selector relation $`S`$ for (5) were currently functional at $`W_0`$, and let $`F`$ be a finite pin for $`S`$. Let $`A`$ be the admitted property of being outside $`F`$, written as a finite conjunction of inequalities. Its extension is nonempty. The selected output $`y`$ at input $`A`$ lies outside $`F`$. Choose $`z\notin F\cup\{y\}`$ and let $`g`$ transpose $`y,z`$.

The permutation $`g`$ lies in $`G_{W_0}`$, fixes the pin $`F`$, and fixes $`A`$. Hence it fixes the entity $`S`$. Target symmetry preserves truth while transporting all parameters by $`g`$. It carries the true proposition $`S[A,y]`$ to the true proposition

```math
(gS)[gA,gy]=S[A,z]
```

These are two different outputs at the same input, contradicting functionality. Thus $`\mathrm{RelChoice}_{et,e}`$ fails at $`W_0`$, and its boxed form fails at $`W_1`$.

**Relational-output failure too.** Put $`H_y:=\lambda z^e.\,z=y`$, an admitted object of type $`et`$, and define

```math
V[X,Y]:=\exists y^e\bigl[(Xy\lor\neg\exists z^eXz)\land Y=H_y\bigr]
\tag{6}
```

This is an admitted closed serial relation with input and output both $`et`$. If $`S`$ were a functional subrelation, repeat the preceding argument with a finite pin $`F`$ for $`S`$ and input $`A`$, the property of being outside $`F`$. Its chosen output must equal $`H_y`$ for some $`y\notin F`$. The transposition $`g`$ gives another true output $`gH_y=H_z`$. The two haecceities are distinct, since evaluation at $`y`$ distinguishes them. This again contradicts functionality. Consequently $`\Box\mathrm{RelChoice}_{et,et}`$ also fails at $`W_1`$.

The underlying model and the $`W_0`$ individual-output choice failure are existing work. The additional current all-type Relational Choice verdict at $`W_1`$, its use with the existing OS/SplitMono verdicts, and the explicit relational-output variation (6) are the new contributions here.

## 5. The counterexample realizes the exact witness-image obstruction

For a Good observer $`E`$, postcompose relations by $`E`$: $`U^E[x,y]=E(U[x,y])`$. Under C5 an observer fixes every identity proposition, so translating a Relational Choice instance yields

```math
\forall U\bigl[\mathrm{Serial}(U^E)\to
\exists S\,[\mathrm{Functional}(S^E)\land S^E\subseteq U^E]\bigr]
\tag{7}
```

Current Relational Choice applied to $`U^E`$ yields some selector relation $`R`$. It does not put $`R`$, or even its current extension, in the image of the postcomposition map $`S\mapsto S^E`$. Formula (7) requires precisely this additional witness availability.

The countermodel makes the failure visible using an admitted observer, rather than only an abstract lack of surjectivity. At $`W_1`$, let $`A`$ be the atom consisting of all arrows into $`W_0`$, and let

```math
E_A(p):=\Box(A\to p)
```

The linked local-observer proof verifies that $`E_A`$ is Good at every finite type list and reads truth at $`W_0`$. For either failed choice instance of §4, its universally closed proposition $`C_{\rm ch}`$ is true on all $`W_1`$-target arrows and false on all $`W_0`$-target arrows. Hence

```math
C_{\rm ch}\text{ is currently true},\qquad E_A(C_{\rm ch})=\bot
\tag{8}
```

In particular, current extensional fullness at $`W_1`$ provides selectors that $`E_A`$ cannot see as selectors at $`W_0`$. The qualified-left-inverse strengthening does not repair this: a left inverse for an observer gives injectivity, while the missing relational witness concerns its image.

This is the reusable boundary. Witnesses occurring only as opaque argument terms, as in Functional Choice, survive the translation without reindexing. Existential witnesses used as asserted relation heads, as in Relational Choice, need a separate witness-image theorem. Ordinary separation, even with C5 and qualified left inverses, does not supply one.

## 6. A stronger positive package

The native records already establish

```math
\mathrm{WeakRigidComp}+\mathrm{ND}\Rightarrow\mathrm{Plenitude},
\qquad
\mathrm{RelChoice}+\mathrm{Plenitude}\Rightarrow\mathrm{FC}
```

See [Weak Rigid Comprehension and ND imply Plenitude](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/results/weak-rigid-comprehension-and-nd-imply-plenitude.yaml), and [Relational Choice and Plenitude imply Functional Choice](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/results/relational-choice-and-plenitude-imply-functional-choice-r.yaml). Their source is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.16, p. 33 and n. 49, and §2.3, pp. 31–32; the weakening to weak rigidity is attributed in the first record to Cian Dorr.

Combining those proved implications with §2 gives

```math
\mathrm{C5}+\mathrm{OS}+\mathrm{WeakRigidComp}+\mathrm{RelChoice}
\Rightarrow\Box\mathrm{FC}\Rightarrow\Box\mathrm{RelChoice}
\tag{9}
```

The last implication is the existing [boxed Functional-to-Relational Choice theorem](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/results/necessary-functional-choice-r-implies-necessary-relational-choice-r.yaml). Its full-schema form includes individual outputs through the usual haecceity coding; no forbidden individual-valued function type is added. Formula (9) states all-type schema premises. It does not assert that any one arbitrarily chosen weak-rigidity type instance alone supplies all those conclusions.

The model construction is Bacon and Dorr, *Classicism*, 16 May 2023 draft, Appendix D, p. 79; the symmetric ideally-full formulation is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8; §3.1, p. 9; Lemma 21, p. 10, as indexed in the group record. The ordinary Relational Choice formulation is *Classicism*, §2.3, pp. 31–33. Existing observer verdicts retain the attribution in their linked research notes. The new witness transport and current-choice combination are not attributed to those human sources.


## 7. Further consequences

**Native-Box separation still does not reflect Relational Choice.** Over C5, a Good observer commutes with native Box exactly when it is injective, by [Native-Box logical observers](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/native-box-logical-observers.md), §3. Briefly, C5 makes every Box judgment an endpoint, so $`E(\Box p)=\Box p`$. Injectivity and $`E\top=\top`$ give $`Ep=\top\leftrightarrow p=\top`$, and therefore $`\Box Ep=\Box p`$. Functionality collects these pointwise identities into the required whole-operation identity. A qualified left inverse makes its observer injective. Consequently C5 + full SplitMono implies full BoxSep, and our same evaluation proves

```math
\mathrm{C5}+\mathrm{BoxSep}+\mathrm{RelChoice}_{\rm all}
\not\Rightarrow\Box\mathrm{RelChoice}_{et,e},
\qquad
\mathrm{C5}+\mathrm{BoxSep}+\mathrm{RelChoice}_{\rm all}
\not\Rightarrow\Box\mathrm{RelChoice}_{et,et}
\tag{10}
```

This follows from the existing observer comparison and the choice verdict above; it assumes neither surjectivity nor reversibility.

**Functional Choice has an exact full-schema characterization.** Combining §2 with the established converse gives

```math
\boxed{\mathrm C+\mathrm{OS}+\mathrm{FC}_{\rm all}
\quad\equiv\quad
\mathrm C+\Box\mathrm{FC}_{\rm all}}
\tag{11}
```

For the reverse implication, the proved native records give $`\Box\mathrm{FC}\Rightarrow\Box\mathrm{Plenitude}\Rightarrow\mathrm{C5}+\mathrm{Atomicity}_t`$. [Logical observer separation and its hierarchy](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §3, then supplies full endpoint separation, hence full OS; T supplies current FC. The passage from C5 + Atomicity to OS is the linked ordinary observer proof, not a native database record. Equation (11) concerns full schemas; it does not claim that a single boxed FC type instance supplies every OS instance.
