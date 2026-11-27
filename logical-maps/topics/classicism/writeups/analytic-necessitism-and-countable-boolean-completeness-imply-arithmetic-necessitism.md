# Analytic Necessitism and Countable Boolean Completeness imply Arithmetic Necessitism

Fix a type $\sigma$ and assume $\Box I^*_\sigma$. Write $N$ for the Frege
numbers of type $\nu=(\sigma t)t$. We construct a real number structure at
the current point on the carrier $\tau=\nu t$. Only the current instance of
Countable Boolean Completeness with counting type $\sigma$ and output type
$\tau$ is needed.

For each $n$ in $N$ put $h_n=\lambda x^\nu.\,x=n$. If $m,n$ are distinct
current numbers then they remain distinct throughout the cone. Indeed,
in the current Peano system one is a positive increment of the other,
say $n=m+Sk$ for some $k\in N$. This equation and the numberhood of its
arguments persist, and the Peano condition at each successor rules out
$m=m+Sk$. This uses the
[persistence of true addition equations](arithmetic-necessitism-and-pure-b-imply-necessity-of-arithmetic.html).
Consequently $h_m\leq\neg h_n$ for distinct current numbers. Application
at $n$ also shows that $n\mapsto h_n$ is injective at the current point.

Given an admitted property $A$ of $\nu$, form the property of $\tau$-entities
$$
 H_A(w)\ \longleftrightarrow\ \exists n\,(Nn\land An\land w=h_n).
$$
The graph $Nn\land An\land w=h_n$ injects its current instances into the
Frege numbers counted at $\sigma$. Countable Boolean Completeness therefore
gives $H_A$ a least upper bound $J_A$ in the Boolean order on $\tau$.
For every current $m\in N$ we have $J_A(m)\leftrightarrow A(m)$.
If $A(m)$, then $h_m\leq J_A$. If $\neg A(m)$, every member of $H_A$
lies below $\neg h_m$, so $J_A\leq\neg h_m$. Moreover, if $A$ and $B$
agree on current $N$, then $H_A$ and $H_B$ have exactly the same current
members, hence exactly the same upper bounds. Antisymmetry gives
$J_A=J_B$ as whole entities.

Use the $h_n$ as numbers with zero $h_0$ and successor $h_n\mapsto h_{Sn}$.
Each property of these labels pulls back by $\lambda n.\,Y(h_n)$, so Peano
induction transfers. The reals are the $x$ satisfying
$\exists A\,\operatorname{LUB}_\tau(x,H_A)$. A number $h_n$ belongs to
such an $x$ just when $x(n)$. Equal membership gives identical reals by
the preceding paragraph. For any property $Y$ of the labels, take
$A=\lambda n.\,Y(h_n)$; the resulting real has exactly the requested
members. All predicates and relations of the structure are thus given by
formulas, including the real predicate itself. The map's definition of
a real number structure permits the two sorts to overlap.

The current structure witnesses the antecedent of Analytic Necessitism at
$\tau$. Take its rigid, necessarily real witness. The
[hereditary Peano match](analytic-necessitism-and-transversal-imply-arithmetic-necessitism.html)
identifies its number system with $N$ throughout the cone. Induction gives
persistence of each matched pair, so weak inextensibility of the rigid
numbers transfers to $N$ at every accessible point. Together with
persistence and the necessary distinctness proved above, this gives the
Arithmetic Necessitism conclusion at $\sigma$.
