# Research Synthesis of the Two Manuscript Reviews

## Later correction from Question 84 (2026-08-01)

Question 84 has since been answered negatively. Even an action-independent
game with a trivial uniform equilibrium can fail its proposed absolute
terminal-remainder certificate because public (+1) and (-1) absorbing
branches cancel ex ante but not after taking an absolute value branchwise.

Accordingly, references below to Question 84 as a corrected capstone are
historical. Its branch-and-target quantifiers and no-free-public-coin rule
remain useful design constraints, but its conditions (5)--(7) are not a
universal proof interface. The existing expectation-level adaptive-potential
certificate is a different, still-sound sufficient route. The semantic target
remains the exact uniform deviation-cap constructor.

## Later result from Question 85 (2026-08-02)

Question 85 answers the coupled-scale player-free problem. It gives a
canonical recurrent-quotient hierarchy for \((\lambda(t),P(t))\), with at
most \(|S|-1\) faster-than-killing quotients and one critical generator. It
also gives an exact occupation--flux characterization for fresh-public-
randomized finite modes and an exact augmented-chain test for every specified
finite-mode architecture.

The deterministic boundary is nonclosed: a slower irreversible leakage can
make the Abel target unattainable by any one feedback policy while leaving it
arbitrarily approximable. This is not itself an obstruction to uniform
equilibrium, whose profile may depend on accuracy. It redirects the root
notion from exact target realization to constructive all-accuracy
approximability with the correct horizon and deviation quantifiers. The
remaining lift is strategic and must synthesize any public randomization.

## Purpose

This note extracts consequences for the uniform-equilibrium conjecture from
ManuscriptReviewClaude.md and ManuscriptReviewGPT.md. It is not a plan for
polishing or publishing the manuscript. The reviews are evidence and prompts,
not authorities; every mathematical criticism is checked before it changes
the proof program.

## Changes that materially affect the conjecture program

### 1. Select the analytic arc as well as the payoff target

The endpoint atlas classifies a chosen analytic discounted-equilibrium germ.
But germ existence is existential, and the conjecture only needs one
successful construction. Closing every possible germ is sufficient, not
necessary.

The root architecture should therefore be:

    discounted-equilibrium correspondence
      -> choose an analytic germ/leaf
      -> choose an implementable uniform target
      -> preserve that declared target through legal credible continuations
      -> adaptive certificate

This creates a legitimate **arc-improvement route**: prove that every game has
at least one germ landing in a closable region, rather than close every leaf
of every germ.

Sorin's absorbing game proves that arc improvement cannot replace target
selection. Its analytic discounted payoff \((1/2,2/3)\) is outside the whole
uniform-payoff set. Thus the two root choices—germ and target—are distinct.

Consequences:

- the \(0/13\) leaf score remains a conservative sufficient-program score,
  not a necessary list of thirteen obligations;
- any future root selector must quantify existentially over the chosen germ,
  not universally over an arbitrary input germ;
- the Lean root interface should be a GermTargetSelectionOutput, not an
  endpoint-preserving reconstruction record.

### 2. Do not grant a free public correlation device

The conjecture concerns behavior strategies with private randomization in the
original perfectly monitored stochastic game. A commonly observed random
seed is extra structure unless it is part of the model.

Any proof that uses public random child selection must therefore do one of:

1. synthesize the lottery from publicly observed actions or transitions;
2. prove unilateral robustness of the synthesized lottery;
3. charge its payoff, transition, entry, and stopping costs; or
4. show that the branch closes without public correlation.

Jointly controlled lotteries are therefore a serious candidate primitive, not
a cosmetic addition. The relevant question is not merely whether a public
coin can sample the desired distribution. It is whether the game can produce
that coin at the required history without giving one player profitable control
over the child, changing the entry state, or accumulating linear lottery debt.

The no-free-public-lottery constraint survives Question 84's negative answer:
any replacement construction assumes independent private randomization only,
so a public lottery must be constructed and audited.

### 3. Replace the one-scale Abel bridge by a coupled-scale problem

The analytic germ has the form

\[
t\longmapsto(\lambda(t),P(t),r(t)),
\]

not necessarily an analytic family \(P(\lambda)\). If
\(\lambda(t)\asymp t^d\), a transition of order \(t^a\) is:

- faster than discount when \(a<d\);
- critical when \(a=d\);
- slower than discount when \(a>d\).

The first-order formula involving \(JP'(0)H\) covers only the special
one-scale case where the discount itself is a valid analytic parameter.
Faster transitions can merge endpoint classes before the critical resolvent
is formed; critical transitions create a reduced generator; slower
transitions can remain invisible to the Abel endpoint while still causing
irreversible Cesàro leakage.

[Question 85](../../../questions/old/Question85-CoupledScaleAbelReduction.md) therefore
asks for an invariant multiscale reduction of the
coupled pair \((\lambda(t),P(t))\). Questions82 and 83 remain useful one-scale
feedback and one-controller results, but their positive statements must not
be promoted to general Puiseux arcs without this new bridge.

### 4. Add benchmark validation to the proof search

Two benchmarks are more informative than another abstract wrapper.

#### The Flesch--Thuijsman--Vrieze cyclic game

The 1997 three-player example has equilibria that require cyclic Markov
strategies and has no stationary \(\varepsilon\)-equilibrium. It directly tests
whether the atlas plus target selector can generate endogenous modes rather
than merely perturb a stationary endpoint.

The immediate research task is to transcribe the published game exactly and
compute:

- all analytic discounted-equilibrium branches near zero;
- their endpoint targets and atlas leaves;
- the target selected by the known cyclic equilibrium;
- which public modes, lottery primitives, and target bridges are actually
  needed.

This must be done from the complete published game, not from a remembered
summary. Primary reference: J. Flesch, F. Thuijsman, and K. Vrieze, “Cyclic
Markov Equilibria in Stochastic Games,” *International Journal of Game
Theory* 26 (1997), 303--314, DOI
<https://doi.org/10.1007/BF01263273>.

#### Vieille's two-player theorem

The framework should be tested against arbitrary finite two-player games.
The useful question is not whether the known theorem is true, but whether the
present certificate language can reconstruct it.

- If it can, identify the selected germ/target and close every post-selection
  seam using the known two-player machinery.
- If it cannot, identify the first missing certificate field or operation.

Failure of the current certificate calculus on the two-player theorem would
be a framework diagnosis, not evidence against uniform equilibrium.

## Mathematical criticisms checked and not accepted

### The two-state bicausal calculation is not an independent-innovations error

For

\[
Q=K=
\begin{pmatrix}
0&1\\
2/3&1/3
\end{pmatrix},
\qquad
\alpha=(2/5,3/5),
\]

contemporaneous next-state noises are freely coupled. With
\(\rho_{00}=a\), the initial coupling constraints give

\[
\rho_{01}=\rho_{10}=2/5-a,\qquad
\rho_{11}=1/5+a.
\]

For the cost \(\mathbf 1_{\{X_1=Y_1=1\}}\), the rowwise Fréchet minima at
current pairs \((0,0),(0,1),(1,0),(1,1)\) are

\[
1,\quad\frac13,\quad\frac13,\quad0.
\]

Therefore

\[
\min_{0\le a\le2/5}
\left[a+\frac13\left(\frac45-2a\right)\right]
=\frac4{15}.
\]

An arbitrary complete-path coupling attains the terminal Fréchet bound
\(1/5\). The gap comes from conditioning each transition on the current pair,
not from requiring independent innovations. The review's alternative
calculation silently fixed a different initial coupling and used the wrong
row probability.

The manuscript now displays this calculation explicitly.

### The harmlessness dual does not require a unichain hypothesis

The direct-closure theorem takes the maximum over **all** normalized invariant
state-action occupations in the entire unilateral-reachable arena. The dual
scalar is the global maximum recurrent gain over all classes, not a
state-specific gain asserted to be constant.

Finite LP duality therefore gives

\[
\rho(x,a)+Ph(x,a)-h(x)\le0
\]

on every reachable row whenever every invariant occupation has nonpositive
mean. This is valid in a multichain arena. A gain-plus-bias formulation becomes
necessary when safety is required only from selected reset states or when
transient flows weight differently reachable recurrent classes, as in the
fixed-compiler analysis of
[Question 83](../../../questions/old/Question83-ControlledAbelCesaroUniformCap.md). That
is a different hypothesis.

The manuscript now states why the global theorem is multichain-safe.

## High-value leads, not yet theorems

These review suggestions deserve investigation, but receive no closure credit
until they produce a consumed mathematical output.

1. **Jointly controlled lotteries.** Test whether they remove any actual
   child-selection obstruction without introducing entry or credibility debt.
2. **Nonhomogeneous finite-chain decomposition.** Compare the coupled-scale
   feedback problem with decomposition--separation and simulated-annealing
   hazard criteria.
3. **Equilibrium index and arc selection.** Use index or degree information to
   choose a favorable analytic branch. This can reduce leaf obligations but
   cannot by itself solve the Sorin target mismatch.
4. **Mean-payoff/Streett and switched-Lyapunov tools.** The account calculus
   may admit existing path-complete or quantitative liveness theorems.
5. **Computational leaf census.** Enumerate small rational games, solve their
   algebraic germ branches, classify them, search finite certificate
   templates, and verify exact candidates. Frequencies are heuristic; exact
   generated certificates are genuine progress.

## Important for auditability, but not the conjecture's critical path

The reviews correctly request complete mathematical definitions of the
certificate and all endpoint leaves, pinned formal artifacts, theorem-by-
theorem attribution, a two-axis status taxonomy, and narrower publication
scope. These are important for independent validation and eventual
publication.

They do not, by themselves, construct an implementable target, a credible
response, a strict child, or a discharged account. They should not displace
the mathematical priorities above.

## Revised priority order

1. **Germ-and-target selection:** choose an implementable target under Sorin,
   arc choice, absence of a free public coin, and Q84's cancellation boundary.
2. **Coupled-scale delivery:** solve or sharply refute
   [Question 85](../../../questions/old/Question85-CoupledScaleAbelReduction.md); use the
   answered one-scale Questions82 and 83 as boundaries.
3. **Concrete stress tests:** run the complete FTV cyclic game and arbitrary
   two-player recovery through the certificate calculus.
4. **Public-lottery audit:** determine exactly when child randomization can be
   synthesized in the original game.
5. **Post-selection leaf reconstruction:** only then freeze new Lean
   interfaces for target transport, entry, credibility, and recursive
   progress.
6. **Computational census and cross-field imports:** use them to discover
   closures or falsify proposed invariants, not as substitutes for consumers.

## Progress accounting

The reviews and the resulting corrections improve the map but do not close a
generic game or a nonsemantic atlas leaf. Closure credit remains zero. The
gain is that three invalid shortcuts are now fenced off:

- fixed discounted endpoint as target;
- arbitrary fixed germ as compulsory branch;
- free public randomness.
