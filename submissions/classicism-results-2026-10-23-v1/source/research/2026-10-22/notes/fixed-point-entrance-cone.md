# A fixed-point entrance cone: local rigidity without necessary tameness

Research proof, 22 October 2026. New construction and argument from this session; no database record has been edited and no formal verification is claimed.

## Statement and source boundary

In the fixed Classicism framework, relative to the standard set-theoretic construction of symmetric ideally-full models, there is a model with one individual at every point satisfying

- Atomicity, Boolean Completeness, Rigid Comprehension and Relational Choice at every relational type;
- Tame Rigidity, Rigid Power and Weakly Rigid Power at every relational type;
- boxed Strong Actuality and BF at the individual type e;

while failing boxed Tame Rigidity, BF at every relational argument type, ND at t, and Strong Leibniz at every relational type. In particular WRP does not imply boxed TR, even together with the other listed local principles. This does **not** refute TR+RP=>WRP.

The construction uses the symmetric ideally-full semantics of Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8, and Proposition 20. The tail is exactly the database's `symmetric-qualitative-links-individuals-singleton` variant. Its qualitative base is described in the draft's section 8, pp. 23–26. The specific TR failure used here is the later `tame-rigidity` argument in `topics/classicism/models/symmetric-qualitative-links.yaml`, dated 11 October 2026; it is not attributed to the draft. The present cone argument has source category `misc`.

## 1. The category and domains

Let B_0 be the qualitative-link pinning base, with endomorphism monoid M and symmetry group G from that record. Adjoin one isolated base point d. Every m in M and g in G fixes d, and no old point maps to d. Interpret the individual type e by a singleton, independently of this pinning base. Adding d changes no tail domain: agreement on d is automatic, so finite pinning and symmetry are exactly as before at every type. Thus the interpreted tail B is precisely the recorded singleton-individual model.

Adjoin an object A with singleton pinning base {*}, trivial symmetry group and finite-set ideal. Its only endomorphism is its identity. There is exactly one arrow i:A->B, the function sending * to d, and no arrows B->A. Composition is m i=i for all m in M. Interpret e by a singleton at A as well. These data form a category of functions with the required symmetry groups and ideals. Form its symmetric ideally-full model and interpret any optional relational signature constants by top.

At A, a relation of tuple type tau is precisely a pair (E,S): E is an arbitrary subset of the product of A-argument domains, and S is an arbitrary G-invariant subset of the product of B-argument domains. E is the extension at 1_A and S the extension at i. There is only one outgoing arrow to each possible target, so the empty set pins every pair. The only symmetry condition is G-invariance of S. Conversely every such pair is admitted.

Transport along i gives the constant B-profile S, since every composite m i equals i. Every transported A-entity is fixed by every B-arrow, at every type. This also follows directly from functoriality.

## 2. Exact-image relations and Rigid Comprehension

For any set E of A-tuples define T_A(E)=(E,iE). Each tuple in iE is fixed by every B-arrow, so iE is G-invariant and T_A(E) is admitted. Its extension at every accessible arrow is exactly the image of its actual extension.

This relation is rigid. Persistence follows from the exact-image description. For weak inextensibility at A, suppose a test Z is necessarily true of every tuple in E. Every future member of T_A(E) is the transported image of a tuple in E, so it satisfies Z there. At B the extension iE is constant and consists of arrow-fixed tuples. A test necessarily true of every current member is therefore true of every future member there too. This proves necessary weak inextensibility.

Every actual extension therefore has a rigid representative T_A(E), proving RC. Coextensive weakly rigid relations are identical in C. Consequently every weakly rigid relation at A equals the corresponding T_A(E) and is rigid: TR holds. The same observation identifies every rigid relation at A as an exact-image relation.

## 3. Atomicity, Boolean Completeness and Relational Choice

At each relational type the root Boolean algebra is

    P(A-tuples) x P((B-tuples)/G).

The second factor means arbitrary unions of G-orbits. This is a complete atomic Boolean algebra. Any nonzero pair contains either an actual singleton tuple, with empty future component, or one future orbit, with empty actual component; these are admitted atoms. Arbitrary joins and meets are componentwise unions and intersections. Thus Atomicity and Boolean Completeness hold at every relational type.

For an actually serial relation at A, choose one actual witness for each actual input in the metatheory and use its graph as the first component E, with empty second component. The pair-domain description admits this relation and it is actually functional and serial. Thus Relational Choice holds, including choices of individual outputs. This argument uses ordinary metatheoretic choice; it does not supply an operation-valued or necessarily functional selector.

## 4. Rigid and weakly rigid powers

Fix a rigid F=T_A(E). At B its image is the constant relation on K=iE, all of whose tuples are fixed by every arrow. Let Y be weakly rigid at B with Y<=iF, and let D be its current extension. Then D is a subset of K. The constant relation T_B(D) is admitted, pinned by the empty set and rigid by the same fixed-tuple argument. It is coextensive with Y, so Y=T_B(D).

Set E_D={x in E:ix in D}. Then iT_A(E_D)=T_B(D)=Y. Therefore every future weakly rigid subrelation of iF is the image of a current rigid subrelation of F. Conversely every such current subrelation stays rigid and remains below F.

The weakly rigid power property of F consequently has the exact-image profile of its actual extension. By section 2 it is rigid. This proves WRP directly. The same argument, or its restriction to rigid future subrelations, proves RP. It agrees with the independent Atomicity+RC=>WRP theorem, but this model verification does not depend on that new theorem.

## 5. Failure of necessary Tame Rigidity

The tail's recorded `tame-rigidity` argument gives a weakly rigid nonrigid relation U at type (tt)t. Briefly, it encodes each qualitative nonpoint z by a rigid predicate C_z of propositions, and puts U_h={C_z:z in R(ha,hb)}. At a collapse the fibre consists of two companion codes; a later collapse merges those two while the future U-fibre still contains both companion codes, violating weak inextensibility. Weak rigidity at the initial tail point is proved by the finite-pinning B_N criterion in that record.

The tail domains and arrows are unchanged by the incoming root arrow, and adding the fixed base point d is conservative as explained in section 1. Hence this exact recorded witness still refutes TR at B. Since B is accessible from A, boxed TR fails at A.

## 6. Strong Actuality and the failures of BF, ND and Strong Leibniz

The root-only proposition r=(true,false) is the actual atom at A. It is a strong atom: it is an atom at A and becomes bottom at B, where it entails every proposition and its negation. At B the true atom G (the symmetry group) remains G under symmetries and becomes bottom under a collapse. Thus Strong Actuality holds at both objects and boxed Strong Actuality holds at A. BF_e holds trivially because e is a singleton everywhere.

The root has exactly four propositions, and all their images at B are bottom or top. Define

    Q(p)=r or p=top or p=bottom.

Every root proposition necessarily satisfies Q. But the tail contains contingent propositions, for example G, which do not satisfy Q. Thus forall p box Qp is true at A and box forall p Qp is false: BF_t fails. The same argument refutes BF at any relational argument type tau. Use the constant-predicate embedding p↦C_tau(p) and universal-quantification retraction D_tau, with D_tau(C_tau(p))=p. The image at B of a root tau-entity has constant profile, so D_tau of that image is bottom or top; the tail entity C_tau(G) supplies the omitted instance. Equivalently BF_tau implies BF_t by this embedding/retraction.

ND_t fails because r differs from bottom at A while their images at B are equal.

The future-only root proposition not r is an atom, and its only nonzero part is itself. Its image is top at B, which G splits, so it is not a strong atom. Therefore no strong world lies below not r, and SL_t fails. SL at any relational type tau would imply SL_t: apply SL_tau to the constant relation C_tau(p) for a nonbottom p, and existentially join a resulting strong world W over its tuple arguments. The join is nonbottom, lies below p, and necessarily decides every proposition because W necessarily decides every corresponding constant relation. Hence SL fails at every relational type.

## 7. General entrance-cone lemma

The exact-image and pair-algebra arguments used no special property of the qualitative tail. Any one-object symmetric ideally-full tail with an arrow-fixed pinning-base point admits this singleton entrance. Its root satisfies Atomicity, BC, RC, Relational Choice, Strong Actuality, TR, RP and WRP. Every closed principle that fails in the tail fails necessarily at the root. Adjoining an isolated fixed pinning-base point is conservative whenever the interpreted individuals of the tail are a singleton.

This gives a general method for separating a rich package of local principles from their necessitations. The qualitative-link tail is chosen here because it supplies a recorded failure of TR, while the root's powers are still fully controlled.
