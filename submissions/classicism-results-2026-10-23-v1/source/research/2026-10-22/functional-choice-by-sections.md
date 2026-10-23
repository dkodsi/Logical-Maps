# Functional Choice is Actuality plus sections of surjections

Final scratch proof note, 22 October 2026. This records new ordinary mathematical arguments over the database's fixed C, without changing source records or claiming Lean verification. The two substantive reverse-direction lemmas were independently audited by the parent and rigidity lanes. Expanded proofs and model constructions are in `/tmp/classicism-research/choice-uniformization.md`, §§11–20. This note supersedes the earlier, weaker decompositions there.

## 1. Statements, types, and modal scope

All splitting schemata below range over admitted **relational** types A,B (types other than e). Set

    Surj(f) := ∀b^B ∃a^A(fa=b),
    RInv := ∀f^(AB)(Surj(f)→∃g^(BA)∀b^B f(gb)=b),
    SRInv := ∀f^(AB)(Surj(f)→∃g^(BA)□∀b^B f(gb)=b).

The first conclusion is a pointwise right inverse. The second is a strong right inverse, equivalently the literal operation equation `f∘g=id_B`. The antecedent is ordinary actual surjectivity in both schemata. Replacing it by categorical epimorphism would change the question: over C categorical epimorphism is **necessary** surjectivity.

**Main theorem.** Over C,

    Functional Choice ⇔ Actuality ∧ RInv,
    □Functional Choice ⇔ □Actuality ∧ SRInv.

Consequently also

    □Functional Choice ⇔ □(Actuality ∧ RInv).

These are schema equivalences with the indicated modal scopes. Functional Choice retains every permitted input type, including e, and every relational output type. No e-valued operation is introduced in the proof.

The full splitting schemata may be replaced in these two equivalences by only the mirrored family `f:tA→A`, for relational A. This is a verified type-fragment reduction, not a claim that the fragments and full splitting schemata are equivalent by themselves over bare C.

## 2. First lemma: one section instance stabilizes the actual world

Assume Actuality and the RInv instance for tt→t. Choose w satisfying

    w ∧ ∀p(p→w≤p).

We prove □◇w. If not, let R:=¬◇w and assume ◇R. Define

    T(H) := (w∧◇(R∧H⊤)) ∨ (¬w∧H⊥),     H:tt.

T is actually onto t. Given q, reason by its current truth value. If q is true, choose H⊤=⊤, H⊥=q. Actuality gives w≤q and, from the assumed ◇R, w≤◇R, so T(H)=q. If q is false, choose H⊤=⊥, H⊥=q; then w≤¬q and again T(H)=q. Each chosen H is a two-slot lambda term. This argument uses an existential truth-case choice separately for each q; it does not presume an operation evaluating actual truth.

A right inverse g:t→tt gives T(gw)=w and T(g⊥)=⊥. Since w is actually true, the first yields `◇(R∧(gw)⊤)` and the second its counterpart `¬◇(R∧(g⊥)⊤)`. But C proves necessarily `R→w=⊥`; identity substitution therefore makes the two displayed R-conjunctions necessarily equivalent. Contradiction.

Thus □◇w. The actual-world property of w together with this necessary possibility gives a bivalent evaluator E:t→t:

    ∀p[(p→Ep=⊤) ∧ (¬p→Ep=⊥)].

This last equivalence is proved independently in `/tmp/classicism-research/bivalent-evaluation-root.md`: it is Persistent Actuality ⇔ BE ⇔ ND+Actuality. In particular our assumptions give ND. The argument has used only the tt→t splitting instance.

## 3. Second lemma: a bivalent evaluator turns sections into arbitrary choices

Assume BE and RInv, and let U:στt be serial, with τ relational. Choose x₀,y₀ with Ux₀y₀. Let w be the actual-world proposition supplied by BE. Put A=στt and D=tA. Write

    H_(x,y)(u,v) := (u=x ∧ v=y),
    D_x(u,v) := w ∧ u=x,
    Valid(k) := ∃x,y(Uxy ∧ k=H_(x,y)),
    RangeD(b) := ∃x(b=D_x),
    V(k)(u,v) := w ∧ ∃x,y(Uxy ∧ k=H_(x,y) ∧ u=x).

Pair haecceities are necessarily injective in their components. For every actual Uxy, Actuality gives w≤Uxy, and hence the literal identity `V(H_(x,y))=D_x`. The D_x are actually distinct for distinct x and none is bottom. Bottom is not a valid pair code.

Use E to turn the tests Valid and RangeD into literal Boolean endpoint coefficients. This defines a single lambda operation π:D→A with these actual identities:

    π(H)=V(H⊤), if Valid(H⊤);
    π(H)=H⊥,    if ¬Valid(H⊤) and ¬RangeD(H⊥);
    π(H)=D_x₀,  otherwise.

No general conditional with output e is used: A is relational, so the expression is formed pointwise by Boolean multiplication and joins. The endpoint coefficients make these branch identities literal identities of A-entities.

π is onto. To hit D_x choose y with Uxy and put H⊤=H_(x,y). To hit b outside RangeD put H⊤=bottom and H⊥=b. RInv gives s:A→D with π(sb)=b.

For x≠x₀, set k_x=(sD_x)⊤. If k_x were invalid, the escape branch would yield a value outside RangeD or the default D_x₀, neither equal to D_x. Thus k_x=H_(a,y) with Uay. Its projected value is D_a=D_x, so a=x. Hence k_x codes some y satisfying Uxy.

Decode this y into the permitted relational output τ by

    d(x)[z̄] := ∃y(k_x(x,y)∧y[z̄]).

The literal code identity makes d(x)=y, by necessary evaluation and Intensionality. Use the bivalent test E(x=x₀) to substitute y₀ at the one default input. The resulting operation h:σ→τ satisfies ∀x U(x,hx). This proves FC even when σ=e. The only right-inverse instance used in this lemma has the form tA→A.

FC supplies Actuality through Plenitude and supplies RInv by selecting preimages, so the first main equivalence follows.

## 4. Strong sections and the necessary benchmark

For reference, a useful exact identity is

    SRInv ⇔ RInv ∧ BF_rel,

where BF_rel is Barcan for relational quantified types. In one direction NI makes each pointwise inverse equation necessary and BF boxes their universal quantifier. In the other, strong sections make every actual surjection necessarily surjective, and persistence of surjectivity is equivalent to BF_rel.

Here is the crucial reverse mask argument at type t. Given `∀q□Pq`, define F:tt→tt by

    (FH)(r) := Hr ∧ (r=⊤ → P(H⊥)).

For every current H its image is literally H, so F is actually onto. Persistence of surjectivity makes it onto at every future point. At such a point, a preimage K of the two-slot target with bottom q and top ⊤ must have K⊥=q; its top equation then forces Pq. Thus □∀q Pq, proving BF_t. The same construction with relational outputs gives BF_rel.

Now assume □Actuality+SRInv. The first main equivalence gives FC and hence ND. Strong sections give BF_t, so the recorded ND_t+BF_t characterization gives C5. C5 supplies strong left inverses for injections; the explicit bare-C retraction formula is

    g(b)[ū] := ∀a(b=fa→a[ū]),

which retracts any necessarily injective f. Combining this with □Actuality and the independently proved `Plenitude⇔Actuality+pointwise left inverses` gives □Plenitude. The existing theorem C5+Atomicity_t→No Pure Contingency is therefore available. Since each FC instance is a closed pure formula, ordinary FC now gives □FC.

Conversely □FC supplies □Actuality, C5/BF, and ordinary preimage choices; NI and BF make their inverse equations strong. This proves the second equivalence. Necessitating the first theorem gives the completely boxed formulation.

Only the tA→A fragment is needed: it supplies the two lemmas above. For the BF step any actual surjective endomorphism F:A→A is covered by the surjection `H↦F(H⊤)` from tA; its strong section yields one for F by top evaluation.

## 5. Why neither conjunct nor the strong scope can be omitted

The following are concrete consistency/separation claims, not claims of absolute validity or invalidity of a mathematical philosophy.

* **Actuality does not supply sections.** The recorded singleton-individual full two-object chain has □Actuality and BF but fails RInv. At the root a proposition is (x,y)∈2² and a tt-entity is (A,B), with A⊆2² and B⊆2. Transport forgets A and sends (x,y) to y. The operation

      f₀(A,B)=(1_(1∈B),1_(0∈B)),    f₁(B)=1_(0∈B)

  is onto at the root. A coherent section would require B to encode both x,y while depending only on y, impossible. Details: supplementary note §14. Thus the splitting conjunct is essential in both equivalences.

* **Sections do not supply Actuality.** A full typed Boolean-valued hierarchy over a nontrivial complete atomless Boolean algebra, with crisp identity and all set-functions, validates C+C5 and both strong inverse schemata (indeed necessarily), while Actuality has value 0. Set-theoretic sections exist by ZFC choice. This is first an algebraic value-1 soundness witness; supplementary §16 also gives a countable elementary-substructure/generic-ultrafilter Henkin realization whose quantifiers have ordinary Tarskian truth. No arbitrary complete ultrafilter is assumed. Thus RInv does not imply Actuality or FC.

* **Actuality cannot replace necessary Actuality in the benchmark.** The recorded full Boolean-valued model on `2×RO(R)`, evaluated at its isolated atom, has C5, FC, Actuality and necessarily all strong splitting instances, but fails □Actuality and □FC because its second component is atomless. This is an ordinary designated pointed model. Details: `topics/classicism/writeups/full-boolean-valued-atom-and-atomless.md` and supplementary §13.

* **Ordinary sections cannot replace strong sections beside □Actuality.** The recorded full two-object retract has □Actuality and FC, hence RInv, but fails C5 and □FC. Its ordinary sections need not satisfy the necessary universal inverse equation.

All source-model verdicts used above are recorded or given explicit additional proofs in the supplementary note. The general atomless algebraic construction and the section obstructions are research produced in this session; they must receive source `misc` if later recorded. No source proof has been modified.

## 6. Related clean formulations

The parallel retraction result is

    Plenitude ⇔ Actuality ∧ LInv,
    every actual injection has a strong retraction ⇔ C5.

These explain the sharp distinction between ordinary unique choice and operation identities. For category terminology, `Epi(f)⇔□Surj(f)` over bare C, so with BF_rel explicitly included the necessary benchmark can also be written

    □FC ⇔ □Actuality ∧ BF_rel ∧ every categorical epimorphism splits.

No proof that categorical epimorphism splitting alone supplies BF_rel is claimed. In particular one must not silently use “epi” as a synonym for actual surjection.
