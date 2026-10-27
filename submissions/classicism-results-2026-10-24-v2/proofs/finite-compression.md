# Tame Rigidity and Rigid Power without Weakly Rigid Power

Original mathematical argument, direct source misc; unpaginated.

## 1. Statement and semantic conventions

Work in the fixed relational type system: `e` and `t` are types, and `sigma -> tau` is allowed when `tau != e`. Write a relation type as `rho = sigma_1 ... sigma_n t`, including `n = 0`. All arguments below apply to arbitrary finite tuples of admitted types, including the empty tuple.

The claim is the existence of a pointed model satisfying

```math
 C+\mathrm{TR}+\mathrm{RP}+\neg\mathrm{WRP}_{et}
```

TR and RP here are the full schemas at the distinguished root. No boxed RP or Barcan assumption is added. In fact Barcan at individual type fails in this construction.

Use the symmetric ideally-full category semantics recorded in [symmetric ideally-full models](../source/topics/classicism/groups/symmetric-ideally-full.yaml). The general semantics is due to Dorr, *Boolean Completeness does not imply Rigid Comprehension*, Definitions 15–18, p. 8, §3.1, p. 9, and Lemma 21, p. 10, as located in that record. Individuals are the bases, arrows act as their underlying functions, and the domains contain all symmetric intensions pinned by finite sets of base points. The category specified below is new here; its direct source category is `misc`, not the paper supplying the semantic framework.

For an arrow `h`, write `h*a` for transport of an entity or tuple. For a relation `X` at its source, write `X_h` for its extension at `h`; thus `(h*X)_k = X_(kh)`. A finite pin `P` of an entity means that arrows with the same target agreeing on `P` transport it identically. One can check admission of a relational profile by showing that its extensions agree on arrows agreeing on a fixed finite pin and that it respects postcomposition by target symmetries. Agreement after further postcomposition then gives equality of transported entities, not just current coextension. Transport carries a pin `P` to its finite image `hP`.

We use two elementary facts about rigidity in C. First, coextensive weakly rigid relations are identical: apply each relation's weak inextensibility to the other, using weak persistence, and then use mutual entailment. Second, an admitted relation with the exact-image profile
$`X_h=h[D]`$
for its actual tuple set `D` is rigid. At any future arrow `h`, every subsequent extension is the direct image of `h[D]`. This gives persistence. Any test necessarily true of every member of `h[D]` is true of its image at every further arrow, giving weak inextensibility there. The argument works for tuples of any types.

The definitions of weak persistence, weak inextensibility and rigidity are those in [Background](../source/topics/classicism/background.md): rigidity is necessary weak rigidity. The power properties are

```math
 R_F(X):=\mathrm{Rigid}(X)\land X\le F,
 \qquad
 W_F(X):=\mathrm{WeaklyRigid}(X)\land X\le F
```

Here entailment `<=` is necessary pointwise implication. The property `R_F` is persistent in C, since rigidity and entailment are themselves necessary conditions.

## 2. The two object category

Let `N` be countably infinite, partitioned into infinitely many infinite blocks `B_i`. Let `Q` be a disjoint set of labels consisting of:

- a label `q_i` for every block `B_i`;
- a label `q_D` for every finite subset `D` of `N`, including the empty set;
- a distinguished label `q_top`.

All these labels are distinct. Define their fibres by

```math
 R(q_i)=B_i,\qquad R(q_D)=D,\qquad R(q_{\mathrm{top}})=N
```

The two objects have bases `A = N` and `B = N disjoint-union Q`.

The endomorphisms of `A` are all surjections `N -> N`. Arrows from `A` to `B` are all surjections onto the `N` summand of `B`. There are no arrows from `B` to `A`.

An endomorphism of `B` is a pair `(f,g)` acting separately on its two summands, where `f:N -> N` is surjective, `g:Q -> Q` fixes `q_top`, and

```math
 f[R(q)]\subseteq R(g(q))\quad\text{for every }q\in Q
\tag{1}
```

The label map need not be surjective. In particular, for every surjective `f`, the pair consisting of `f` and the constant label map with value `q_top` is allowed.

These arrows form a category under ordinary composition. For tail arrows, (1) is preserved because `f'f[R(q)]` is contained in `f'[R(g(q))]`, hence in `R(g'g(q))`. A composite from the root still has a surjective `N` component. Identities satisfy (1).

At `A` use the full permutation group of `N`. At `B` use the permutations of `N` which permute the blocks, extended to labels by sending `q_D` to `q_(pi D)`, sending block labels accordingly, and fixing `q_top`. These are invertible allowed arrows and preserve the fibre relation exactly. Give both objects the ideal of finite subsets of their bases.

This is a base for the standard symmetric ideally-full construction, hence gives a model of C. Interpret individuals by the full bases `N` and `N disjoint-union Q`. If a signature is required, take its relational constants to denote top.

Let `i:A -> B` be the entrance which is the identity on `N`. Call a tail entity **old** if it is `i*a` for a root entity `a`. More generally every transport `h*a` along an entrance is old, because `h = i f` for a root surjection `f`. An old entity has a finite pin contained in `N`. On such an entity, tail transport depends only on the `N` component: `(f,g)i = if`. Old tuples remain old under every tail arrow.

## 3. Stable root sets and full Tame Rigidity

**Stable-set lemma.** Let `D` be any set of root argument tuples, closed under all root surjections fixing a finite `S subset N` pointwise. Then the exact-image profile `E_h = h[D]` is admitted, pinned by `S`, and rigid.

To prove pinning, take arrows `h,h':A -> V` with the same target, agreeing on `S`, and `a in D`. Choose a finite root pin `M` for `a`. Both arrows are surjective onto the target's `N` part. Prescribe a root map `u` to fix `S`, and for `x in M minus S` choose `u(x)` with `h(u(x)) = h'(x)`. These are compatible finite prescriptions. Extend them to a surjection `u:N -> N`, using the infinitely many unprescribed points. Then `ua in D` and

```math
 h'a=h(ua)\in h[D]
```

Interchanging `h,h'` proves equality of the two image sets. The profile respects target symmetries since `s(h[D])=(sh)[D]`; hence it is admitted. Exact images imply rigidity by §1.

Now let `F` be weakly rigid at the root, pinned by `S`, with actual extension `D`. If a root surjection `u` fixes `S`, then `uF=F`; weak persistence therefore gives `u[D] subset D`. The stable-set lemma supplies a rigid exact-image relation coextensive with `F`. Coextensive weak-rigidity uniqueness gives equality. Consequently

```math
 F_h=h[F_{1_A}]
\tag{2}
```

for every root weakly rigid relation and every root outgoing arrow. In particular every such relation is rigid. This proves TR at **every relational type** at `A`.

One special case will be our bound. Take `D=N` at individual argument type. Its exact-image unary relation `F` has extension `N` at every root arrow, including entrances. It is rigid and has empty pin. It is actually universal at `A`, but is not the universal intension: after an entrance the actual universal property also contains the new `Q` individuals, whereas `iF` contains only `N`. This distinction is essential.

## 4. A weakly rigid tail fibre that is not rigid

For a label `q`, define the unary tail relation `U_q` by

```math
 (U_q)_{(f,g)}=R(g(q))
\tag{3}
```

It is pinned by `{q}` and respects tail symmetries, so it is admitted. Transport satisfies `(f,g)*U_q = U_(g(q))`. Every one of its extensions is contained in `N`; in particular `U_q <= iF` for the rigid root bound of §3.

Fix an infinite block label `q_i`. Condition (1) gives weak persistence of `U_(q_i)`. We prove weak inextensibility directly.

Let `Z` be an admitted unary test which is necessarily true of each current member of `B_i`. Let `P` be a finite pin of `Z`, enlarged to contain `q_i` and all points in every finite fibre whose label is in `P`. Fix an arbitrary tail arrow `h=(f,g)` and `y in R(g(q_i))`. Choose
$`n\in B_i`$
outside the finitely many pinned individual points. In particular `n` lies in no finite fibre whose label is pinned. There is a tail arrow `j` agreeing with `h` on `P` and sending `n` to `y`, as follows.

Retain `g` on the pinned labels and send every unpinned label to `q_top`. On each pinned block retain `f`, except that `n` is sent to `y` in block `B_i`. Retain `f` on all pinned individual points. This preserves (1) on each pinned block and each pinned finite fibre. Since only finitely many blocks have pinned labels, choose a different infinite block; on its unpinned points supply all missing `N` targets to make the individual map surjective. Elsewhere choose arbitrary values in `N`. Every unpinned label has target fibre `N`, so its condition imposes no further restriction.

The hypothesis on `Z` gives `j*n=y in Z_j`. As `j` and `h` agree on the pin of `Z`, this gives `y in Z_h`. Since `h,y` were arbitrary, `U_(q_i) <= Z`. Thus `U_(q_i)` is weakly rigid.

It is not rigid. Choose distinct `a,b in N`. There is a tail arrow sending `q_i` to `q_{ {a,b} }` and sending `B_i` into `{a,b}`; another infinite block supplies global surjectivity, and all other labels can go to `q_top`. The transported relation is `U_{q_{ {a,b} }}`, currently coextensive with the finite haecceity union

```math
 H=\delta_a\lor\delta_b
```

This union is rigid and necessarily true of both current members. There is a further tail arrow `m` fixing the label `q_{ {a,b} }` while mapping both `a` and `b` to `a`. Its `N` component can still be surjective because other points supply the missing targets; send all remaining labels to `q_top`. At this arrow the fibre relation still contains both `a,b`, while the transported haecceity union contains only `a`. Thus the fibre relation does not entail `H`, and fails weak inextensibility. The original infinite-block relation is therefore weakly rigid but not rigid.

## 5. Exactness when the label pins have finite fibres

We next show why the preceding weak witness cannot create a failure of higher Rigid Power.

**Finite-fibre lemma.** Suppose a weakly rigid tail relation `T` has a finite pin `P` whose label members are finite-fibre labels or `q_top`. Suppose every actual member of `T` has a finite pin contained in `N`. Then `T` has an exact-image profile and a finite pin contained in `N`.

Let `D=T_(1_B)`. Let `S subset N` include the individual part of `P` and every point of the finitely many finite fibres named in `P`. We show that `E_h=h[D]` is an admitted exact-image relation pinned by `S`.

Take arbitrary tail arrows `h=(f,g)` and `h'=(f',g')` agreeing on `S`. Their label maps may differ. For `a in D`, choose a finite `N` pin `M` of `a`. Choose a surjection `u_N:N -> N` fixing `S` such that `f u_N` agrees with `f'` on `M`; this is possible by the same finite prescription argument as in §3. Let `u_Q` fix the finite labels in `P` and `q_top`, and send all other labels to `q_top`. This defines an allowed arrow `u`: its individual map fixes every point of each pinned finite fibre, and other labels have target fibre `N`.

The arrow `u` fixes `P`, so `uT=T` and weak persistence gives `ua in D`. The arrows `hu` and `h'` agree on the `N` pin of `a`, hence `h'a=h(ua)`. This proves `h'[D] subset h[D]`. Interchange the arrows for the reverse inclusion. The profile `E` is therefore `S`-pinned, and its exact-image form respects target symmetries. It is admitted and rigid. Since it is coextensive with weak `T`, uniqueness gives `T=E`. This proves both conclusions at once.

## 6. Rigid subrelations of old bounds lose their label parameters

**Descent lemma.** Let `F` be any root rigid relation, `h:A -> B` an entrance, and `Y <= hF` any rigid tail relation. Then `Y` has an exact-image profile and a finite pin contained in `N`.

By (2), every member of `hF`, and of any further transport of `hF`, is an old tuple. The same holds for `Y` and its transports. Hence their members have finite pins contained in `N`.

Choose a finite pin `P` of `Y`. Let `N_0 subset N` contain its individual part and every point of each finite fibre whose label lies in `P`. List the finitely many block labels in `P`. For each such `q_i`, choose a fresh point

```math
 z_i\in B_i\setminus N_0,
 \qquad
 D_i=(B_i\cap N_0)\cup\{z_i\}
```

The sets `D_i` are nonempty and pairwise distinct. None equals a pinned finite fibre, since those are contained in `N_0` whereas `D_i` contains `z_i`.

Construct a compression arrow `c` as follows. Its individual component fixes `N_0` and sends `B_i minus N_0` to `z_i` for each pinned block. An unpinned infinite block supplies global surjectivity, while still fixing its finitely many points in `N_0`. The label component sends each pinned `q_i` to `q_(D_i)`, fixes each pinned finite label and `q_top`, and sends other labels to `q_top`. It satisfies (1).

Construct a return arrow `r` whose individual component is the identity on all of `N`, whose label component sends each `q_(D_i)` back to `q_i`, fixes all originally pinned finite labels and `q_top`, and sends remaining labels to `q_top`. This satisfies (1) because `D_i subset B_i`. The distinctness observations above ensure that no label is given conflicting prescriptions.

The composite `rc` agrees with the identity on `P`, so

```math
 r(cY)=Y
\tag{4}
```

The relation `T=cY` is rigid and is pinned by `cP`. All label members of `cP` now name finite fibres or `N`. Its actual members are old, since it is below `chF`. The finite-fibre lemma gives an exact-image profile and a finite `N` pin for `T`. As `r` fixes all of `N`, it fixes `T`; (4) therefore gives `Y=T`. The same two conclusions hold for `Y`, proving descent.

The use of rigidity is precise: it ensures that `cY` is weakly rigid, allowing the finite-fibre lemma. The weak infinite-block witness of §4 loses weak rigidity under a finite compression, so this argument does not remove its block-label parameter.

## 7. Approximate lifting and full Rigid Power

Fix an arbitrary root rigid relation `F`, with actual tuple set `E`. Let `S` be a finite root pin of `F`.

**Approximate lifting lemma.** Given an arrow `h:A -> V`, a finite `N_1 superset S`, and a rigid relation `Y <= hF` at `V`, there exist an arrow `j:A -> V` agreeing with `h` on `N_1` and a root rigid `X <= F` such that `jX=Y`.

If `V=A`, choose an ordinary finite pin `T subset N` of `Y`. If `V=B`, choose a finite `N` pin `T` using the descent lemma.

Extend the finite prescription `h|N_1` to a surjection `j:N -> N` whose nonsingleton fibres are finitely many and finite: send `N minus N_1` bijectively onto `N minus h[N_1]`. Regard it as an arrow to `V`. It agrees with `h` on `S`, so `jF=hF`. Choose a finite `P subset N` containing `N_1`, every nonsingleton fibre of `j`, and a `j`-preimage of each member of `T`. Put

```math
 D=\{a\in E:j*a\in Y_{1_V}\}
\tag{5}
```

Equation (2) gives `(jF)_(1_V)=j[E]`, and `Y <= jF`; consequently

```math
 j[D]=Y_{1_V}
\tag{6}
```

We show that `D` is closed under root surjections fixing `P`. For such a surjection `u`, the map `ju` is constant on every fibre of `j`: a nonsingleton fibre is pointwise fixed by `u`, and a singleton fibre imposes no condition. Thus

```math
 ju=vj
\tag{7}
```

for a well-defined surjection `v:N -> N`. It is surjective because `ju` is surjective. It fixes `T`: for each `t in T`, use its chosen preimage in `P` in (7).

For `V=A`, use `v` as a root endomorphism. For `V=B`, extend it to a tail endomorphism by sending all labels to `q_top`. It fixes the `N` pin `T` of `Y`, so in either case `vY=Y`. Persistence gives `v[Y_(1_V)] subset Y_(1_V)`. Also `uF=F` and persistence give `u[E] subset E`. If `a in D`, equation (7) therefore shows `j(ua)=v(ja) in Y_(1_V)`, whence `ua in D`.

Apply the stable-set lemma to obtain a rigid root exact-image relation `X` with actual extension `D`. Since `D subset E` and both relations have exact-image profiles, `X <= F`. By (6), `jX` and `Y` are actually coextensive. Both are rigid, so uniqueness gives `jX=Y`. This proves approximate lifting. It does not assert a lift along the original arbitrary arrow `h`.

Now consider `R_F`. It is persistent in C. To prove weak inextensibility at the root, let `Z` be any admitted test necessarily true of every current member of `R_F`. Choose a finite `N_1` containing pins of `F` and `Z`. At an arbitrary root outgoing arrow `h`, take any member `Y` of `(R_F)_h`; thus `Y` is rigid and entails `hF`.

Approximate lifting gives a root rigid `X <= F` and an arrow `j` agreeing with `h` on `N_1`, with `jX=Y`. The hypothesis on `Z` gives `Y in Z_j`. Pinning gives `jZ=hZ`, so `Y in Z_h`. As `h,Y` were arbitrary, `R_F <= Z`.

Thus `R_F` is weakly rigid at the root. Full TR from §3 makes it rigid. The argument applies to any relation type and any rigid `F` at that type. This proves **full-schema RP at the root**, including its higher-type instances.

The approximate lifting step adapts parts (c)–(d) of [the recorded surjection argument](../source/topics/classicism/arguments/rigid-power-surjections.yaml). The new ingredient needed for the present category is §6: target rigid subrelations under old bounds have pins on the surjective `N` part even though the full tail base contains new labels.

## 8. Weakly Rigid Power fails

Use the rigid unary root bound `F` from §3 and its weak power `W_F`. Root TR says that every current member of `W_F` is rigid. Since rigidity is necessary, the admitted test
$`Z(X):=\mathrm{Rigid}(X)`$
is necessarily true of every current member of `W_F`.

At the identity entrance `i`, however, §4 supplies `U_(q_i)`, which is weakly rigid, entails `iF`, and is not rigid. It belongs to `(W_F)_i` and fails `Z` there. Hence `W_F` does not entail `Z`, violating weak inextensibility. The bound `F` is itself rigid, and therefore weakly rigid. This refutes WRP at relation type `et`.

Together with §§3 and 7, this gives the stated countermodel to the full-schema implication.

## 9. Why higher power does not remove the witness

The tail witness is new as a relation entity even though all its individual members lie inside the old rigid bound. If it were an old relation entity, it would have a finite `N` pin. The finite-fibre lemma with no label pins would then make it rigid, contrary to §4.

Every root rigid relation has an exact-image profile by §3. Therefore the future members of any root rigid family of relation entities are old. No such family can acquire the weak nonrigid labelled witness as a member. This is what allows all higher RP instances to hold while WRP fails: rigid subrelations admit the descent argument; weak subrelations need not.

The construction also identifies an important boundary. Individual Barcan fails because entrance maps omit the `Q` individuals. One can witness this directly with the old bound `F`: every current individual necessarily satisfies `F`, but not every future individual satisfies it. No boxed TR claim is possible either, since §4 explicitly refutes TR at the tail.

## 10. Relation to the proof direction

The proof search isolated a misleading possible step: direct images preserve rigidity, but inverse images of rigid label families need not even be weakly rigid. A finite example already shows why that step cannot justify the conjecture.

Take the full two-world category model `A -> B` with only identity endomorphisms and two constant individuals `a,b`. Each relational domain at `B` is the full powerset of its argument tuples. Each relational domain at `A` consists of pairs of arbitrary extensions, one on root tuples and one on tail tuples; transport takes the tail component. Inductively every domain at every fixed finite type is finite. Every weak relation consequently equals a finite haecceity union and is rigid, at either object.

For a rigid bound `G`, every future rigid subrelation has a finite extension inside the exact image of `G`. Choose preimages of its finitely many tuples in the current extension of `G`. Their finite haecceity union is a rigid subrelation of `G` transporting to the chosen future relation, by coextensive-rigid uniqueness. Thus rigid power has an exact-image profile. Weak and rigid relations coincide at both objects, so weak power has the same profile. This proves full TR, RP and WRP in the finite example; it is the finite-bound argument also discussed in [maximalism-modal, §15](../source/research/2026-10-22/notes/maximalism-modal.md).

Let `p` be false at `A` and true at `B`, and let `F` be the rigid universal individual relation. For `x=a,b`, define `d_x=delta_x or (p and F)`. The entities `d_a,d_b` are distinct at `A` and both become `F` at `B`. Let `Z=delta_(d_a)`, a rigid singleton property of relations. Its inverse image under `x |-> d_x`, restricted to `F`, has current extension `{a}` and future extension `{a,b}`. It is not weakly rigid: the test `delta_a` is necessarily true of its sole current member but fails on `b` later.

Thus the failure of the attempted inverse-image step is independent of the countermodel's label construction. The successful negative direction is instead the descent and approximate lifting argument above, which checks full RP directly while retaining a weak nonrigid subrelation.

## Sources and verification scope

- The fixed framework and definitions are [topic.yaml](../source/topics/classicism/topic.yaml), [Background](../source/topics/classicism/background.md), and the records for [TR](../source/topics/classicism/principles/tame-rigidity-r.yaml), [RP](../source/topics/classicism/principles/rigid-power-r.yaml) and [WRP](../source/topics/classicism/principles/weakly-rigid-power-r.yaml).
- The general semantic construction is the one sourced in [symmetric ideally-full models](../source/topics/classicism/groups/symmetric-ideally-full.yaml), with the locators given in §1. That source is not credited with the new countermodel or its descent lemma.
- The finite approximation argument is adapted explicitly in §7 from [rigid-power-surjections](../source/topics/classicism/arguments/rigid-power-surjections.yaml), parts (c)–(d). Root stable sets are proved directly in §3.
- The earlier [colour-collapse entrance](../source/research/2026-10-22/notes/colour-collapse-entrance.md) proves a unary separation. Its higher-power failure is treated in [colour-collapse higher power](colour-collapse.md). The present construction is different and proves the full-schema separation.
- Direct source for the new construction and proof: Codex, 23 October 2026, this note, §§2–8; source category `misc`. This Markdown note has no fixed pagination. Lean source and its completed verification are described in §11.
