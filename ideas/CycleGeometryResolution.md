# Resolving the geometry of equilibrium cycles

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `MIXED` |
| Objective priority | `P1` |
| Last audited | 2026-08-03, through `fa4621d` and experiments E42--E50 |
| Central live claim | Couple the landed forward exact-D seam chart to E50's reverse anchored terminal-packet chart through the common finite minimizers, then decode a seam or certified buffered exit as repair or uniform root-debt descent. |
| Next discriminant | Prove a finite-chain bridge/holonomy interface that transports E50's reverse depth-one packet across a forward close seam, or prove that failure of such transport gives a uniform optimized-debt exit. |
| Production destination | Quitting relative-boundary producer and one-seam reinsertion consumer |
| Supersedes / superseded by | Supersedes the invariant-circle/Sturmian reading locally; no successor yet. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| CG1 | Every code in a compact graph-directed pullback system has a lift; common strict contraction makes it unique, periodic codes lift periodically, and common prefixes give exponential value control. | `PROVED` | `M+L` | Verification inside a supplied certified contracting component. |
| CG2 | Periodic lifts are exponentially dense in a supplied contracting full-shift component. | `PROVED` | `M+X` | Symbolic cover only; injective payoff coding is not claimed. |
| CG3 | Finite-prefix best-response summaries compose max-affinely and their acceptance sets are explicit polyhedra. | `PROVED` | `M+L` | Supplied quitting prefixes; producer of attainable tails remains open. |
| CG4 | First scale/direction blow-up gives exact coordinates away from zero and stationary payoffs approach the singleton-reward direction barycenter. | `PROVED` | `M+X` | Stationary zero-hazard chart; no Nash-limit or nonstationary claim. |
| CG5 | Finite iterated blow-up plus terminal data yields a compact, closed, predecessor-serial, strategically exhaustive repair relation. | `OPEN` | `I` | `quittingDebtBox` and the exact-D edge graph already supply a compact closed unanchored core; packet/scale augmentation, plateau seriality, and strategic exhaustiveness remain open. |
| CG6 | Ordinary chain recurrence supplies an exact internal path with all approximation concentrated in one closing seam. | `WRONG` | `M` | Refuted by standard pseudo-orbit versus exact-orbit separation; §8 is corrected below. |
| CG7 | A globally serial relation with a compact buffered set has, within its covering number, either a downstream exact path with one small closing seam or an exit from the buffer. | `PROVED` | `M+X` | Pure compactness theorem; no strategic decoder or initial-debt conclusion. Lean probes: `BufferedOneSeamReturnOrExit.lean` (arbitrary serial orbit) and `GreedyBufferedExitDecoder.lean` (E46; greedy `K`-relative path, first-exit prefix anchoring, drop `> a − b`, and certified failure of buffered seriality at the pre-exit state — the seriality-failure half of CG8 interface 4). |
| CG8 | Plateau-generated, anchor-preserving exact paths decode the CG7 seam as a repair and every CG7 exit as a bounded-length uniform reduction of root optimized debt. | `OPEN` | `I` | Current central geometry question and replacement for CG6. |
| CG9 | The production positive-debt split can retain its supplied exact-D tail and select a downstream finite-cover one-seam pair without changing any internal edge. | `PROVED` | `M+X` | E47 actual-data adapter; the selected states omit terminal packet, terminal distance/scale, and calibrated-prefix provenance, so no repair is claimed. |
| CG10 | Selected finite min-max chains admit a common-subsequence two-ended exact-D limit: a forward positive/summable-clock ray and a reverse ray ending on the zero-payoff/singleton-cap face, with positive debt and a quantitative full-action packet at reverse depth one. | `PROVED` | `M+X` | E50 checks the unscaled two-end core of PB5. The reverse action is selected from the limiting terminal edge; bridge survival and convergence of a preselected finite marked atom are not packaged. The middle escapes, so there is no bi-infinite orbit or proved transport to the forward seam. |
| CG11 | Without any seriality hypothesis, the greedy buffered path yields an exhaustive trichotomy within the covering number of steps: a fully buffered one-seam return, a certified first exit, or a typed dead end — an exact buffered prefix ending at a state of `K` with no admissible successor. | `PROVED` | `M+X` | E46 extension (`greedyBufferedPath_return_or_certified_exit_or_deadEnd`). Keeps the compactness layer consumable while CG5's plateau seriality is only partial: a dead end becomes structured producer output rather than a failed hypothesis. No decoding or debt conclusion is claimed. |

### Falsifiers and wrong turns

- A heteroclinic-cycle homeomorphism can be chain recurrent through multiple
  small pseudo-orbit jumps while a nonfixed exact orbit never returns. This
  kills CG6.
- Total boundedness gives close downstream states on a long exact path, but
  not recurrence of the initial marked packet. Any useful theorem must retain
  owner, full terminal action, scale, and calibrated-prefix anchoring.
- The map (f(x)=x/(1+x)), with ranking (D(x)=1+x), has strictly decreasing
  reachable ranks converging to the positive plateau (1), but no fixed
  bounded horizon gives a uniform decrement over late reachable states. This
  kills any inference from pointwise Lyapunov decrease to CG8.
- K11 overlap, FTV neutral behavior, the period-ten atlas escape, Q125's
  off-chain payoff, Q129 owner nontransfer, and the separation between E50's
  forward and reverse ends remain mandatory regressions for CG5--CG8.

### Production map

```text
contracting graph data -> pullback/periodicity/prefix estimates       [L]
finite quitting prefix -> max-affine acceptance geometry             [L]
hazard vector -> first direction chart and stationary barycenter     [X]
iterated scales + terminal anchor -> compact exhaustive relation      [?]
serial buffer -> greedy one-seam return or certified-exit dichotomy   [X]
positive projective exact-D tail -> downstream exact-D seam           [X]
finite min-max chains -> forward ray + reverse anchored packet ray    [X]
anchored exact return or buffered exit -> one-seam reinsertion        [? -> L consumer exists]
```

The missing bridge/decoder arrows, rather than the already landed symbolic
algebra, finite-cover pigeonhole step, or terminal-end compactness, own the
claim that this geometry could solve the quitting producer.

### Exit conditions

- Mark `MINED` if CG5 and CG8 are proved or rigorously reduced to a different
  named producer, after all short production kernels are routed.
- Mark `PARKED` if the full-rate stationary repair/search lane remains open
  and no game-generated compact relation is available to test.
- Mark CG5 `WRONG` if a plateau-compatible chattering family defeats every
  finite resolved atlas or closedness after retaining the required terminal
  data.
- Mark `SUPERSEDED` only when another idea group supplies both the relative
  boundary object and its repair-or-descent theorem.

## 1. Objective

The object visible in continuation-payoff coordinates is expected to be
singular, folded, piecewise analytic, nonconvex, and possibly nonclosed before
the correct boundary data are added. The realistic objective is therefore not
to find one global change of coordinates making it a smooth manifold.

The proposed resolution is a nicer space **above** the payoff set:

\[
\boxed{
\text{finite symbolic base}
\times
\text{certified continuation fiber}
\times
\text{scale/direction boundary data}.}
\]

The original geometry is recovered by a projection which is allowed to glue
different sheets. Upstairs, cycles become fixed points or chain returns of
explicit fiber maps. Downstairs, their images may form a Cantor set, a glued
branched continuum, or a more singular quotient.

This note makes that proposal precise enough to generate theorem statements.
It separates:

- statements already landed in production;
- generic statements checked under `experiments`; and
- global statements which remain conjectural.

## 2. The unresolved object

At a live phase, a candidate quitting certificate contains at least:

\[
z=(x,w,\beta,a,\mu),
\]

where:

- \(x\) is the product hazard/action profile;
- \(w\) is the prescribed continuation payoff;
- \(\beta\) is a playerwise cap or terminal relative-debt allowance;
- \(a\) is the complete simultaneous terminal action/quitter set; and
- \(\mu\) is the transported survival or terminal-cylinder scale.

The equations and inequalities include:

1. prescribed Bellman recurrences;
2. active-player indifference equations;
3. inactive-player Nash inequalities;
4. Snell/best-response cap inequalities;
5. product-simplex constraints on \(x\); and
6. terminal-packet compatibility.

Projecting immediately to \(w\) forgets the active branch, relative hazard
scale, terminal distance, and possibly the support history. This is where
folds and apparent self-intersections enter.

The full set should be treated as a semialgebraic/analytic **stratified
correspondence**, not as the graph of one globally smooth map.

## 3. Symbolic resolution of the hyperbolic part

### 3.1 Resolved atlas

Let \(G=(V,E,s,t)\) be a finite directed multigraph. A vertex records a
certified support/active-branch chart. Attach to each vertex a nonempty compact
metric box \(B_v\). An edge \(e\) carries:

- a predecessor map \(T_e:B_{t(e)}\to B_{s(e)}\);
- decoded finite hazards/actions along the block;
- active equalities and inactive inequalities valid on the entire domain;
- a complete terminal-packet label; and
- playerwise opponent-survival bounds.

An admissible infinite code is

\[
\omega=(e_0,e_1,\ldots),\qquad t(e_k)=s(e_{k+1}).
\]

A compatible geometric lift is a path \(v_k\in B_{s(e_k)}\) satisfying

\[
v_k=T_{e_k}(v_{k+1}).
\tag{3.1}
\]

The code space \(\Sigma_G\) carries the prefix topology. For
\(0<\alpha<1\), one convenient metric is

\[
d_\alpha(\omega,\omega')=\alpha^{N(\omega,\omega')},
\]

where \(N\) is the first differing edge.

### 3.2 Existing inverse-limit theorem

**LANDED.** `GraphDirectedCompactPullback` proves:

- every admissible code has at least one compatible lift, using compact
  inverse limits;
- a common strict contraction \(q<1\) makes that lift unique.

This gives a coding map

\[
\pi:\Sigma_G\longrightarrow \bigsqcup_v B_v,\qquad
\pi(\omega)=v_0.
\tag{3.2}
\]

### 3.3 Quantitative coding theorem

**LANDED.** `GraphDirectedPeriodicLift` proves that if two codes share
\(n\) edges and their depth-\(n\) vertices agree, then

\[
d(\pi(\omega),\pi(\omega'))\le q^nD,
\tag{3.3}
\]

where \(D\) is the finite-box diameter budget.

Consequently \(\pi\) is continuous in the prefix topology. Choosing
\(\alpha=q\) makes (3.3) a Lipschitz estimate; a different \(\alpha\) gives a
Hölder exponent \(\log q/\log\alpha\).

Also **LANDED**: if the code is periodic, uniqueness forces its lift to have
the same period.

### 3.4 Periodic closing/density

For a one-vertex full shift, define the period-\(n\) approximation

\[
\omega^{(n)}_k=\omega_{k\bmod n}.
\]

**CHECKED IN LEAN (E42).**
`GraphDirectedFullShiftDensity.lean` proves that the unique lift of
\(\omega^{(n)}\) is exactly periodic and

\[
d(\pi(\omega^{(n)}),\pi(\omega))\le q^nD.
\tag{3.4}
\]

Thus exact periodic lifts are exponentially dense in every contracting
full-shift component.

For a finite strongly connected graph rather than a literal full shift, the
same argument needs a bounded connector from the terminal vertex of a long
prefix back to its initial vertex. If the connector length is at most \(L\),
one obtains a periodic code agreeing through the original prefix and the same
\(q^nD\) initial-value bound. Formalizing this graph-closing extension is a
small next theorem.

### 3.5 The quotient and its overlap geometry

The actual payoff attractor is

\[
K=\pi(\Sigma_G).
\]

Its ugliness is controlled by the equivalence relation

\[
\omega\sim\omega'\quad\Longleftrightarrow\quad
\pi(\omega)=\pi(\omega').
\tag{3.5}
\]

There are three regimes:

1. **Separated injective coding.** If branch images are separated and the
   branches have a suitable inverse lower bound, \(\pi\) is an embedding.
   For a full shift, \(K\) is then Cantor-like.
2. **Finite controlled overlap.** The quotient is a branched or graph-like
   continuum. A finite overlap groupoid or nerve may describe it.
3. **Wild overlap.** Infinitely nested identifications may occur. One should
   retain the symbolic cover rather than work directly with \(K\).

The K11 certificate proves a full symbolic shift in support-labelled strategy
space, but current box overlaps do not decide whether the actual value images
intersect. The concrete geometric computation should therefore be:

1. interval-enclose the **reachable branch images**, not merely their boxes;
2. certify pairwise and higher intersections or separations;
3. construct the Čech nerve of those images; and
4. repeat under refinement to see whether the nerve stabilizes.

This is the correct place for computational topology or persistent homology:
as a diagnostic for a certified cover, not as a substitute for the strategic
inequalities.

## 4. Tropical/max-affine resolution of incentive fibers

### 4.1 One-player block action

A finite prefix acts on a certified terminal value by

\[
F(w)=\max\{A,T+\chi w\},
\qquad
G(w)=B+Pw,
\tag{4.1}
\]

where \(F\) is the best-response value and \(G\) is prescribed delivery.
Here \(0\le P\le\chi\le1\) in the quitting application.

The exact cap/gap condition with terminal cap \(\beta\) is

\[
\max\{A,T+\chi(w+\beta)\}\le B+Pw+\varepsilon.
\tag{4.2}
\]

**LANDED.** `QuittingCertifiedBoundaryPolyhedron` proves that (4.2) is the
intersection of two affine halfspaces. In the interior case \(0<P<\chi\), its
acceptable \(w\)-set is one explicit interval and its exact gap has a unique
balance-point minimizer.

### 4.2 Holonomy semigroup

Represent the best-response map by a triple

\[
h=(A,T,\chi),\qquad \chi\ge0.
\]

Chronological composition is

\[
(A_1,T_1,\chi_1)\star(A_2,T_2,\chi_2)
=
\left(
\max\{A_1,T_1+\chi_1A_2\},
T_1+\chi_1T_2,
\chi_1\chi_2
\right).
\tag{4.3}
\]

The prescribed affine summaries compose as

\[
(B_1,P_1)\star(B_2,P_2)
=(B_1+P_1B_2,P_1P_2).
\tag{4.4}
\]

**CHECKED IN LEAN (E43).**
`MaxAffineHolonomySemigroup.lean` bundles (4.3) into an associative
`Semigroup` and proves

\[
\operatorname{eval}(h_1\star h_2,w)
=\operatorname{eval}(h_1,\operatorname{eval}(h_2,w)).
\tag{4.5}
\]

There is no real-valued identity element: an exact identity needs the early
floor \(A=-\infty\). If a monoid is useful, the correct enlargement is to
\(\overline{\mathbb R}=\mathbb R\cup\{-\infty\}\), not an artificial finite
sentinel.

For all players, one block carries the product of these playerwise semigroup
elements plus its full terminal action and mass label. A cycle word
\(\gamma=e_0\cdots e_{m-1}\) has a finite holonomy

\[
H_\gamma=H_{e_0}\star\cdots\star H_{e_{m-1}}.
\tag{4.6}
\]

The prescribed part has a unique fixed point

\[
w_\gamma=\frac{B_\gamma}{1-P_\gamma}
\quad\text{when }P_\gamma<1.
\tag{4.7}
\]

The cycle is strategically valid exactly when this fixed point lies in every
transported chamber and satisfies every playerwise max-affine cap inequality.
Thus fixed-word validation is finite algebra.

### 4.3 Tropical cell complex

The switching wall

\[
A=T+\chi(w+\beta)
\tag{4.8}
\]

separates “stop early” from “continue to the certified boundary.” Combining
these walls over players and support charts gives a finite polyhedral/tropical
cell complex in \((w,\beta)\)-space.

The refined symbolic vertex should therefore contain:

\[
v=(\text{support mask},\text{active Nash set},
   \text{active max-affine branches}).
\]

On each such cell, all formulas are affine or analytic. Word surgery occurs
when a lift crosses a cell wall. This turns a nonsmooth global map into a
finite graph of smooth/polyhedral pieces.

## 5. Blow-up of the zero-hazard apex

### 5.1 First real-oriented blow-up

For a nonzero vector \(x\in\mathbb R_{\ge0}^{\,I}\), define

\[
\lambda(x)=\sum_i x_i,\qquad
\theta_i(x)=\frac{x_i}{\lambda(x)}.
\tag{5.1}
\]

Then

\[
\theta(x)\in\Delta_I,\qquad x=\lambda(x)\theta(x).
\tag{5.2}
\]

Radial rescaling changes only \(\lambda\):

\[
\lambda(cx)=c\lambda(x),\qquad \theta(cx)=\theta(x)
\quad(c>0).
\tag{5.3}
\]

Replacing the apex \(x=0\) by the simplex of directions gives the blown-up
cone

\[
\widehat C=[0,\infty)\times\Delta_I,
\tag{5.4}
\]

with blow-down map \((\lambda,\theta)\mapsto\lambda\theta\).

**CHECKED IN LEAN (E44).**
`HazardScaleDirectionBlowup.lean` proves direction nonnegativity,
simplex normalization, exact reconstruction, radial invariance, reconstruction
from supplied scale/direction, and injectivity away from \(\lambda=0\).

### 5.2 Why one blow-up is insufficient

For

\[
x(\varepsilon)=(\varepsilon,\varepsilon^2),
\]

the first direction converges to \((1,0)\). The second-order coordinate has
not disappeared mathematically; it has moved into the tangent geometry of the
simplex face \(\theta_2=0\).

The existing path-closure experiment proves quantitatively that the normalized
second share is at most \(\varepsilon\). To retain it one needs an iterated
blow-up:

1. blow up the zero-hazard apex;
2. detect the face on which \(\theta\) lands;
3. blow up the vanishing coordinates normal to that face; and
4. repeat until the finite set of asymptotic orders is separated.

For analytic/Puiseux hazard arcs, only finitely many leading orders occur on a
selected branch. The repository's leading-symbol and Puiseux machinery is a
plausible formal source for this finite iterated flag:

\[
I=I_0\supsetneq I_1\supsetneq\cdots\supsetneq I_r,
\tag{5.5}
\]

with one simplex direction at each scale.

This is the hazard analogue of sector decomposition and renormalization.

## 6. The terminal end and relative compactification

Forward scale/direction data are not enough. The terminal-packet results show
that a nonvanishing cylinder can move to arbitrarily large terminal distance.
At every fixed forward time its mark disappears, although its total scale
does not.

Introduce a compactified terminal-distance coordinate, for example

\[
\rho=\frac{d}{1+d}\in[0,1],
\qquad \rho=1\text{ representing }d=\infty.
\tag{6.1}
\]

The boundary \(\partial_\infty=\{\rho=1\}\) must retain:

- terminal cylinder mass;
- the full simultaneous quitter action;
- the debt owner/provenance;
- terminal payoff and cap;
- the hazard-scale flag.

A finite chain is then a relative path whose terminal endpoint lies on
\(\partial_\infty\). A stationary, First, or finite lasso repair is an edge
from this boundary stratum back into the finite certificate region.

The resulting local coefficient cannot be only a player label. Q129 proves
that atomwise regret does not transfer dynamic-debt ownership. At minimum the
coefficient is

\[
\mathcal L=(i,a,w,\beta,\mu,\text{scale flag}).
\tag{6.2}
\]

## 7. The proposed resolved certificate space

For each refined symbolic cell \(v\), let:

- \(B_v\) be its compact continuation/cap box;
- \(\widehat C_v\) its finite iterated hazard blow-up;
- \(K_v\) its finite action/provenance label space; and
- \([0,1]_\rho\) its compactified terminal-distance coordinate.

Define the disjoint resolved atlas

\[
\widehat X_0
=
\bigsqcup_{v\in V}
B_v\times\widehat C_v\times K_v\times[0,1]_\rho.
\tag{7.1}
\]

Glue only chart faces which have a certified common strategic
interpretation. It may be better to retain these gluing maps as a finite
groupoid rather than form the quotient immediately. This prevents distinct
support histories or provenance labels from being accidentally identified.

Let \(R\subseteq\widehat X_0\times\widehat X_0\) be the **repair
correspondence**:

\[
z\,R\,z'
\]

iff there is one decoded exact block taking future certificate \(z'\) to
current certificate \(z\), preserving all Bellman, Nash, cap, packet, and
scale conditions.

The required construction theorem is:

> **Compact resolved-relation conjecture.**
> After finite iterated blow-up and addition of the terminal boundary,
> the strategically admissible repair relation \(R\) is closed on a compact
> resolved atlas and is predecessor-serial on the positive-plateau region.

### 7.1 A landed partial resolved relation

The construction does not start from zero. Production already contains the
following fixed-dimensional core:

\[
\texttt{QuittingDebtPoint}
=
(\text{payoff},\text{product root},\text{exact dynamic debt}).
\]

The set `quittingDebtBox` is compact. The graph
`quittingDynamicDebtEdgeGraph` of exact Nash--Bellman/dynamic-debt
transitions is closed and compact. Moreover, the production positive-infimum
split supplies either a uniform-equilibrium payoff or an infinite path in
this graph with a positive initial debt coordinate and summable opponent
clock.

E47 applies the supplied-path form of the finite-cover theorem directly to
that production tail. For every finite cell assignment whose cells have
diameter below \(\eta\) on `quittingDebtBox`, the exceptional tail contains
ordered indices

\[
0\le p<q\le \#\mathrm{Cell}
\quad\text{with}\quad
d(z_p,z_q)<\eta,
\tag{7.2}
\]

and every displayed transition remains the original exact-D edge. Thus the
compact exact relation and an actual positive-plateau path through it are
already landed; the downstream seam is now Lean-checked without selecting a
different orbit.

E50 shows that the terminal end should not be forced into the same one-point
state by an unbounded residual-distance coordinate.  For the selected finite
minimizers (z^K_0,ldots,z^K_K), retain simultaneously

\[
  z_t=\lim_j z^{K_j}_t,
  \qquad
  y_r=\lim_j z^{K_j}_{K_j-r}
  \tag{7.3}
\]

along one common subsequence.  The (z)-ray follows exact-D edges forward;
the (y)-ray follows exact-D edges toward (y_0).  The latter lies on the
closed terminal face

\[
  y_0.\mathrm{payoff}=0,
  \qquad
  y_0.\mathrm{debt}_i=\max(0,r_i(\{i\})).
  \tag{7.4}
\]

Moreover, finite-chain monotonicity gives

\[
  D_i(z^K_0)\le D_i(z^K_{K-1}).
  \tag{7.5}
\]

Thus the positive owner on the forward limit has (D_i(y_1)>0).  The exact
edge (y_1\to y_0) then forces a complete simultaneous opponent action with
positive product mass and positive owner advantage; quantitatively its
weighted advantage carries a `1 / card (ι → Bool)` share of the incoming
debt.  This is the residual-depth-one packet, now retained theorem-grade at
the reverse end rather than discarded as an atom at infinity. The action is
reselected from the limiting edge; E50 does not yet package convergence of a
chosen finite marked action or its transported root-cylinder scale. Those
stronger coupled coordinates are PB5 in
`PositivePlateauBoundaryClosure.md` and remain the P0 bridge input.

This is still not the resolved repair relation.  Equation (7.3) produces two
one-sided charts, not a bi-infinite orbit: the middle of the same finite
chains escapes, and no bounded bridge between (z) and (y) is asserted.
Consequently the reverse packet is not yet transported through E47's close
forward seam.  Closeness in the forward `QuittingDebtPoint` quotient can
still identify states whose finite suffixes cannot be spliced with a uniform
modulus. Nor is the exact-D graph proved predecessor-serial on an exhaustive
plateau set. CG5 is therefore narrowed from “add an unbounded terminal field”
to “construct a two-chart bridge/holonomy relation preserving finite-chain
provenance, and prove its strategic decoder.”

The full conjecture is not yet proved. Its mandatory falsifiers are:

1. the K11 full shift and its overlapping boxes;
2. FTV neutral rotation;
3. Q125's stationary payoff outside the zero-boundary chain set;
4. Q129 owner nontransfer;
5. E50's nonvanishing reverse terminal packet with no automatic bridge to
   the forward ray;
6. the pure-externality positive-holonomy equilibrium; and
7. the period-ten branch outside the reduced atlas.

## 8. One-seam compactness, buffered exit, and the strategic decoder

Assume temporarily that \((\widehat X,R)\) has been constructed. The
reinsertion theorem consumes a specific object:

> A **one-seam exact return** at \(z\) is a finite exact \(R\)-path whose final
> endpoint is within \(\varepsilon\) of \(z\). Every internal transition is
> exact; the sole approximation is the closing mismatch.

This is stronger than ordinary chain recurrence. A standard
\(\varepsilon\)-chain or pseudo-orbit may introduce an \(\varepsilon\)-defect
at every transition. In general those many defects cannot be moved into one
closing seam without a shadowing, specification, or closing hypothesis.

The distinction is real. On the circle, take the time-one map of
\(\dot\theta=\sin^2(2\pi\theta)\). It fixes \(0\) and \(1/2\), and its two
open arcs are heteroclinic connections directed toward the next fixed point.
Small pseudo-orbit jumps across both fixed points make every point chain
recurrent, while a nonfixed exact forward orbit converges to the next fixed
point and never returns near its start. Thus the former claim

\[
\text{ordinary chain recurrence}
\Longrightarrow
\text{one-seam exact return}
\tag{8.1}
\]

is **wrong**.

The correct topology-only result is elementary and quantitative. Let
\(K\) be a totally bounded subset of a metric space and let
\(N_\eta(K)\) be the least number of sets of diameter less than \(\eta\)
needed to cover \(K\).

> **Downstream one-seam lemma.** If a relation \(R\) is serial on \(K\), then
> from every \(x_0\in K\) there is an exact path
> \(x_0 R x_1 R\cdots R x_N\), with \(N\le N_\eta(K)\), and indices
> \(0\le p<q\le N\) such that
> \(d(x_p,x_q)<\eta\).

Indeed, choose \(N_\eta(K)\) successors in \(K\). Two of the resulting
\(N_\eta(K)+1\) states lie in the same covering set. The exact segment from
the earlier state to the later one has only the closing seam. Closedness of
\(R\) is not used in this finite argument; it is needed when the repair
relation itself is obtained by limiting or compactification.

There is a useful relative version. Let \(R\) be serial on the whole compact
metric space \(X\), let \(\Phi:X\to\mathbb R\) be continuous, choose \(a>b\),
and put

\[
K_b=\{x:\Phi(x)\ge b\}.
\]

Start from \(x_0\) with \(\Phi(x_0)\ge a\). While possible, choose an
\(R\)-successor inside \(K_b\); if none exists, seriality supplies a successor
outside it. Within \(N_\eta(K_b)\) edges one obtains either

1. an exact downstream one-seam segment lying in \(K_b\); or
2. an exit \(y\notin K_b\), for which
   \(\Phi(x_0)-\Phi(y)>a-b\).

This is the **buffered one-seam return-or-exit theorem**. It is the strongest
finite dichotomy supplied by compactness alone. In particular, once downstream
starts are allowed, absence of an \(\eta\)-return means failure of seriality
inside the buffer, not a Conley theorem.

**LEAN STATUS.** E46 proves the greedy relative form: the exit is the first
exit, its entire prefix is exact and buffered, and the pre-exit state has no
admissible successor remaining in the buffer. E47 proves the complementary
supplied-path form and instantiates it on the production projective exact-D
tail. E50 retains, along the same finite-minimizer subsequence, a reverse
exact-D ray whose depth-one state has positive debt and a quantitative full-
action packet over the anchored terminal face. Consequently the topology,
actual forward-tail adapter, and terminal-end compactness are no longer open.
What remains is exactly CG8: bridge the separately compactified forward seam
and reverse packet through their common finite-chain provenance, and convert
the greedy exit's failure of buffered seriality into the root optimized-debt
splice.

The uniform exit is a state-level statement, not yet optimized-debt descent.
That distinction is forced even by a one-dimensional continuous map. Take

\[
f(x)=\frac{x}{1+x},\qquad D(x)=1+x,\qquad x\in[0,1].
\]

Then

\[
f^n(1)=\frac1{n+1},
\qquad
D(f^n(1))\downarrow1,
\]

and the only chain-recurrent point is \(0\), which is not reached in finite
time. Although \(D(f(x))<D(x)\) for every \(x>0\), for each fixed \(L\),

\[
D(x)-D(f^L(x))
=\frac{Lx^2}{1+Lx}\longrightarrow0
\quad(x\downarrow0).
\tag{8.2}
\]

Thus neither absence of a finitely reachable chain-recurrent point nor
pointwise strict decrease gives a decrement uniform over late reachable
states. A generic complete Lyapunov function has the same limitation. Uniform
decrease follows on a compact bad set only after proving that every admissible
edge there decreases the chosen function strictly; compactness of the
restricted graph then supplies the positive minimum gap.

The downstream one-seam lemma still says nothing by itself about the
designated initial state or the terminal packet that generated the positive
debt. E50 proves that the owner survives and that a simultaneous terminal
action can be re-extracted on the reverse chart, but shifting to a downstream
forward segment does not
transport that reverse chart with it. The missing datum is now the bridge
through the common calibrated finite chain (including the relevant
transported scale), not existence of the terminal packet itself. Without that
bridge the return is a pigeonhole artifact, not a repair certificate.

The corrected target is therefore anchored:

> **Anchored repair-or-exit conjecture.** For every calibrated
> positive-plateau chain, either an exact initial block reaches an accepted
> tail with one closing mismatch tending to zero while preserving the marked
> packet/provenance/scale data, or there are uniform constants
> \(m,\delta>0\) and an explicitly certified exit such that within \(m\)
> further blocks the optimized debt decreases by at least \(\delta\) (or a
> separately valid stationary/First repair is reached).

This is intentionally stronger than a generic complete-Lyapunov theorem.
Pointwise Lyapunov decrease outside a chain-recurrent set may vanish near that
set and need not be decrease of the optimized debt. A uniform bounded-block
decrement requires a buffered compact bad set, continuity of the decoded debt,
and proof that every non-returning continuation stays in that buffer until the
decrement or named exit occurs.

For a finite cell graph, a reachable strongly connected component versus an
acyclic quotient remains a useful prototype. In compact fibers, however, the
actual missing theorem is the preservation of the anchor and the uniform
buffer—not ordinary Conley recurrence alone.

More explicitly, consuming the buffered theorem requires four interfaces not
provided by compact topology:

1. every relation edge decodes to a uniformly bounded number of exact game
   stages;
2. the transient and loop attach chronologically to the supplied minimizing
   chain;
3. closeness in the **full** resolved state has a uniform modulus which turns
   the one seam into a strategically valid approximate repair while preserving
   the nonvanishing packet; and
4. leaving the buffer constructs an actual zero-boundary extension whose
   aggregate debt at the original root drops by a fixed amount.

Without the first item, a bounded number of relation edges is not a bounded
game length. Without the fourth, a lower local ranking value is not the
optimized-debt inequality needed by the plateau contradiction.

## 9. Physics and geometry dictionary

| General technique | Concrete object here | Mathematical payoff |
| --- | --- | --- |
| Covering space / hidden variables | retain support code and phase | unfolds overlapping payoff sheets |
| Markov partition / symbolic dynamics | finite decoded branch graph | replaces orbit geometry by a subshift |
| Poincaré return map | finite block predecessor map | cycles become small fixed-point problems |
| Transfer matrix | max-affine/affine block summary | long words reduce to semigroup products |
| Tropicalization | active max-affine branch cells | nonsmooth geometry becomes polyhedral |
| Real-oriented blow-up | \((\lambda,\theta)\) hazard coordinates | resolves the zero-hazard apex |
| Sector decomposition / renormalization | iterated face blow-ups | retains \(\varepsilon,\varepsilon^2,\ldots\) scales |
| Gauge/groupoid presentation | retain chart labels and certified gluings | avoids destructive quotienting |
| Projective metric | positive survival/continuation maps | may prove contraction beyond Euclidean boxes |
| Morse–Conley theory | diagnostic recurrence/debt order | suggests separators, but needs anchoring plus shadowing/closing before one-seam compilation |
| Transfer/Ruelle operator | operator on symbolic codes | entropy and invariant-measure classification |

Hilbert's projective metric is a particularly interesting untested route.
Positive cone maps can be projective contractions even when their ordinary
operator norm is not below one. A game-facing application would need a
positive homogeneous lift of the continuation recurrence; additive payoff
terms may require one extra homogeneous coordinate.

## 10. Concrete theorem ladder

### Tier A: already proved or checked

1. Compact inverse-limit existence for admissible graph paths — **LANDED**.
2. Uniqueness under common contraction — **LANDED**.
3. Common-prefix exponential continuity — **LANDED**.
4. Periodic code implies periodic lift — **LANDED**.
5. Full-shift periodic closing/density (3.4) — **E42, LEAN-CHECKED**.
6. Max-affine composition and boundary polyhedron — **LANDED**.
7. Bundled associative max-affine holonomy — **E43, LEAN-CHECKED**.
8. First scale/direction blow-up — **E44, LEAN-CHECKED**.
9. Depth-free one-seam mismatch penalty — **E40, LEAN-CHECKED atop the
   landed reinsertion core**.
10. Greedy buffered return or first certified exit — **E46,
    LEAN-CHECKED**.
11. Supplied exact-path fork and production positive exact-D tail adapter —
    **E47, LEAN-CHECKED**.
12. Common-subsequence forward/reverse exact-D compactification, anchored
    reverse terminal face, and quantitative depth-one packet — **E50,
    LEAN-CHECKED**.

### Tier B: short formal extensions

1. Periodic density for finite strongly connected graph shifts using bounded
   connectors.
2. Bundle prescribed affine and best-response semigroups into one
   `BoundaryHolonomy` object.
3. Fixed-point and cap-safety decision theorem for one holonomy word.
4. Extended-real identity, if a literal block monoid has a consumer.
5. Scale-direction homeomorphism between the punctured nonnegative cone and
   \((0,\infty)\times\Delta_I\), upgrading E44's algebraic inverse laws.
6. One-step blow-up continuity and compactness on a bounded hazard cone.

### Tier C: substantive geometry

1. Certified branch-image separation/overlap nerve for K11.
2. Exhaustive refined support/active-branch atlas.
3. Finite iterated blow-up theorem for selected analytic/Puiseux hazard arcs.
4. Closed bridge/holonomy correspondence coupling E50's two landed ends.
5. Full-state anchored one-seam return compiler on that correspondence.
6. Decoder from a buffered exit to a bounded-length root-debt splice. The
   abstract covering-number return-or-exit theorem itself is already proved.

## 11. Conditional capstone

The entire program can be summarized as one conditional theorem.

> **Resolved-geometry uniformity principle.**
> Suppose a finite quitting game admits a compact resolved certificate
> correspondence satisfying:
>
> 1. exhaustive chart coverage;
> 2. exact strategically sound block transitions;
> 3. a finite scale flag and terminal boundary retaining every nonvanishing
>    packet;
> 4. an anchor-preserving exact one-seam return or a buffered uniform debt
>    descent/named repair on every positive-plateau component; and
> 5. a one-seam compiler for those anchored returns.
>
> Then the game has a uniform-equilibrium payoff.

This theorem would not prove that every game has the required resolution.
Its value is architectural: it identifies the exact geometric construction
which would turn the quitting-game conjecture into a compact-dynamics
statement, and it isolates where a counterexample would have to defeat the
resolution.

The probable final “nice geometry” is therefore not a manifold. It is a
compact stratified groupoid or branched correspondence with:

- a finite symbolic base;
- analytic or max-affine fibers;
- hyperbolic and neutral recurrent components;
- iterated scale-direction boundary faces; and
- a relative terminal boundary at infinity.

The horrible payoff geometry is its quotient shadow.
