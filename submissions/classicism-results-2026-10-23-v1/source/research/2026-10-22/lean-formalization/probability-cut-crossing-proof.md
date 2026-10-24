# Internal cut crossing and additive inverses

23 October 2026. New mathematical argument and author source; compilation, the C gate, type checking and translated derivations remain separate verification obligations. No database verdict is changed.

Fix an admitted counting type, a current actual-world code w, and quantified Infinity at that type. The earlier constructions supply the supported natural domain, nonnegative fractions, signed rational codes and their current ordered additive group. All operations below are the explicit relational terms in those constructions. Naturals are internal number codes, not external Lean Nat. A real code P is a supported, nonempty, proper, downward-closed, rounded predicate on the constructed rational domain.

## Positive-step crossing

For a nonzero nonnegative fraction X and any nonnegative fraction Y, apply the internal rational natural-bound theorem to Y/X. Strict order preservation under multiplication by X gives an internal number n with Y < nX. This uses the concrete reciprocal and its proved-in-source cancellation laws. It introduces no cofinality hypothesis.

Choose a cut member a and a rational nonmember b. Linear order and downward closure imply a < b. Represent the positive difference b-a by a nonzero nonnegative fraction Y. For a positive step X, the preceding argument gives nX > Y, so t(n)=a+nX exceeds b. If P(t(n)), downward closure would give P(b), a contradiction. Meanwhile t(0)=a lies in P.

Internal induction proves the following general lemma for every represented predicate V on the number codes: if V(0) and not V(n), there is a number k with V(k) and not V(k+1). At zero the premises contradict one another. At a successor, excluded middle for V(k) gives the boundary immediately when true, and the induction hypothesis supplies it when false. No least-number selection or external finite sequence is required.

Apply this lemma to V(k)=P(t(k)). The explicit successor equation gives q=t(k+1)=t(k)+X=p+X, where P(p) and not P(q). Taking X to be half a given positive rational epsilon gives q-p=epsilon/2 < epsilon. Thus the small-gap property is derived from the actual internal arithmetic and induction, rather than added to the real-code interface.

Exact source declarations: ProbabilityCutCrossing.represented_adjacent_exit, natural_multiple_exceeds_fraction, cut_step_eventually_outside, cut_has_adjacent_step and cut_has_small_gap, under Classicism.Research.

## The reflected-complement inverse

Define -P to contain a rational r exactly when some rational nonmember s of P satisfies r < -s. Prefixing the actual-world and rational-domain conditions makes this an explicit supported code. Nonemptiness follows by going below the negative of any nonmember. The negative of a member witnesses properness: otherwise order reversal and downward closure contradict that membership. Downward closure is immediate, and density supplies roundedness.

For the involution, if r is in -(-P), choose a witness s outside -P and a rational t strictly between r and -s. If t were outside P, order reversal would put s in -P. Hence t is in P and so is r. Conversely, if r is in P, round it upward to a member t. Then -t is outside -P and r < -(-t), giving membership in -(-P). Supported coextension gives literal code identity.

For P+(-P) contained in the principal zero cut, write r=p+v with p in P and v < -q for a nonmember q. The member/nonmember comparison gives p < q, hence r < q-q=0.

For the reverse inclusion, take r<0 and apply the small-gap theorem with epsilon=-r. Obtain p in P and q outside P with q-p < -r. Negation reverses this to r < p-q. Set v=r-p. Translation gives v < -q, so v belongs to -P; and p+v=r. This proves the reverse inclusion with no remaining small-gap premise. Localization upgrades the two inclusions to literal equality of the cut codes.

The resulting concrete inverse identity yields additive cancellation and the guarded equivalence P+Q <= U iff P <= U-Q for real codes. Exact main source declarations are ProbabilityConcreteReals.realAdd_neg, realNeg_involution, realAdd_cancel_right and realAdd_le_iff_le_sub, under Classicism.Research.

## Remaining boundary

This argument supplies additive inverses, not real multiplication, positive division, represented finite-family measure equivalences or the type-ceiling rank reduction. Its formal source still depends on the unverified portions of the internal arithmetic/cut certificate chain. Current evidence and source hashes belong in the lane's verification update, not in an assertion that the full probability theorem is complete.
