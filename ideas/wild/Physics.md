# Wild ideas: uniform equilibrium and physics

## Status

Only a narrow physics-adjacent layer has been mined so far.  Potentials already
behave like stored energy, account inequalities like dissipativity, analytic
transition scales like metastable barriers, and owner holonomy like a discrete
gauge obstruction.  Nonequilibrium statistical mechanics, adiabatic theory,
Markov-chain Hodge decomposition, thermal equilibrium selection, and
renormalization confluence have not been integrated into the proof program.

The useful physics is finite-state and mathematical.  Quantum mechanics, path
integrals, replica methods, and hydrodynamic limits currently add vocabulary
without addressing a known proof seam.

## 1. Hodge decomposition of stationary currents

For a stationary Markov chain with law (pi), let

\[
F(x,y)=\pi(x)P(x,y)
\]

be its stationary edge flow.  It splits into reversible traffic and
irreversible current:

\[
S(x,y)=\frac{F(x,y)+F(y,x)}2,
\qquad
J(x,y)=F(x,y)-F(y,x).
\]

The current is antisymmetric and divergence-free.  On a finite graph, edge
fields decompose into gradient and cycle/harmonic components.  This is a
canonical version of the potential-versus-circulation alternative already used
throughout the endpoint analysis.

With player-valued edge charges, the harmonic component becomes owner typed.
An aggregate current may vanish while its owner components retain opposing
cycle currents.  A useful target is:

> Construct an owner-valued Hodge decomposition in which gradients are payable
> by public potentials and every harmonic current is classified as credible,
> occupation-inert, or strategically obstructive.

Experiment E22 checks exact finite Hodge projections and a nonequilibrium cycle.

## 2. Entropy production and information-payable currents

The stationary entropy-production rate is

\[
\operatorname{EP}(P,\pi)
=\sum_{x,y}F(x,y)
  \log\frac{F(x,y)}{F(y,x)}.
\]

It is nonnegative and vanishes at detailed balance.  It also measures pathwise
time-reversal information.  This creates a possible bridge from circulation to
monitoring: a deviation producing irreversible current may reveal itself.

The scale fence remains essential.  A small current of order (p) generally
produces entropy only of order (p^2).  Therefore evidence cannot pay arbitrary
linear punishment debt.  A viable theorem must pair entropy with a payoff debt
that is also quadratic, complementary, or backed by another potential.

Experiment E26 computes the current, entropy, tilted pressure, and debt scales
in a biased cyclic chain.

## 3. Adiabatic tracking

Let (P_t) be a slowly changing public kernel with instantaneous invariant law
(pi_t).  Adiabatic Markov theory controls whether the actual law tracks
(pi_t).  Schematically, tracking requires

\[
\frac{\|\pi_{t+1}-\pi_t\|}
     {\operatorname{gap}(P_t)}\longrightarrow0,
\]

together with enough accumulated contraction.

This directly addresses the conversion of an analytic discounted germ into a
time-varying schedule on mixing branches.  The hard cases are precisely those
where the spectral gap closes as the germ parameter vanishes.  A useful theorem
would quantify tracking for Puiseux-order gaps and a universal calendar, under
prescribed and unilateral laws.

Experiment E23 demonstrates a good schedule where variation is asymptotically
slower than relaxation and a critical schedule with persistent lag.

## 4. Metastability and effective generators

If transition rates satisfy

\[
P_\lambda(x,y)\asymp c_{xy}\lambda^{q_{xy}},
\]

the orders (q_{xy}) act like energy barriers.  Faster classes equilibrate,
then a reduced generator moves between classes at the next scale.  This is the
physics version of the existing faster/critical/slower reduction.

The possible new invariant is a canonical metastable hierarchy or resistance
tree.  The first algebraic requirement is confluence: eliminating fast states
in different orders must give the same effective generator and reward.
Schur-complement elimination has exactly this associativity when its blocks are
invertible.

Experiment E24 verifies generator and reward confluence exactly over the
rationals.  Extending it to controlled kernels, public observations, and target
inequalities is the substantive problem.

The resolvent calculation now makes the issue sharper.  For a fixed kernel,
the ergodic projection and group inverse give the ordinary gain-plus-bias
packet.  For a moving multichain kernel, transitions of order higher than the
discount scale can still select the first Abel correction, and fractional
orders can destroy an ordinary first-order bias.  Under an explicit convergent
Puiseux presentation, the correct certificate is the full leading-order
hierarchy of every deviation residual.  The missing theorem is therefore not
the existence of formal scales, but confluence of controlled elimination while
preserving rewards, unilateral inequalities, owner labels, and re-entry data.

## 5. Renormalization and rebasing

The analytic reduction already resembles renormalization:

1. integrate out faster transitions;
2. pass to an effective quotient;
3. rescale time;
4. repeat at the next transition order.

If this reduction is functorial under stopped-history rebasing, the metastable
tree depth or barrier profile could provide a canonical progress rank.  If it
depends on elimination choices, it cannot solve global coherence.

Rebasing is essential rather than cosmetic: after a public stopping time, the
same unresolved slow scale must be represented in the child continuation
without reviving a faster scale already discharged by the parent.  A useful
confluence theorem must commute with this change of origin as well as with
different elimination orders.

The relevant question is therefore not whether “renormalization” is a useful
metaphor, but:

> Are polynomial-rate controlled reductions confluent, target preserving, and
> compatible with unilateral continuation inequalities?

## 6. Thermal equilibrium selection

Entropy-regularized or logit responses introduce a temperature
(\tau>0).  Positive temperature gives full-support smooth fixed points.  A
two-parameter family ((\lambda,\tau)) may select different zero-temperature
equilibrium arcs depending on the scaling of (\tau) relative to (\lambda).

This could be an arc-selection mechanism, but it may select an unsustainable
discounted endpoint more canonically rather than repair it.  The decisive test
is whether some temperature scaling selects a target in the all-accuracy
sustainable correspondence.

Experiment E25 solves stationary logit fixed points numerically for Big Match
and Sorin's absorbing example along several temperature/discount scalings.  It
is a branch probe, not an equilibrium-existence theorem.

## 7. Reversible Dirichlet geometry

If (P) is reversible with invariant law (pi), then

\[
\mathcal E_P(f,f)
=\frac12\sum_{x,y}\pi(x)P(x,y)(f(y)-f(x))^2
=\langle f,(I-P)f\rangle_\pi.
\]

A family of controlled kernels sharing one reversible law and a common spectral
gap has a common coercive energy geometry.  This supplies canonical Poisson
bounds, mixing estimates, and moving-potential control without owner-neutral
cycle currents.

Experiment E27 checks exact Dirichlet identities and common-gap coercivity for
two distinct reversible kernels.  A future theorem should determine whether
this closes a natural multiplayer stochastic-game subclass.

## 8. Thermodynamic formalism and tilted kernels

For an edge score (f), the tilted transfer operator

\[
P_\theta(x,y)=P(x,y)e^{\theta f(x,y)}
\]

has a leading eigenvalue whose logarithm is the pressure.  Its derivatives give
long-run score means and variances; its Legendre transform gives deviation
rates.  This may supply optimal monitoring statistics and exact information
budgets for endpoint currents.

It does not construct a punishment.  Pressure separates laws; strategic
credibility remains a recovery-control problem.

The graph-directed predecessor branches suggested by the K11 atlas may form a
contractive symbolic system, but this does not yet promote thermodynamic or
fractal conclusions. A pressure calculation has no proof-program value until
it controls a named strategic quantity, and a Cantor-payoff claim additionally
requires certified branch-image separation. Overlapping images or absence of
such a consumer parks the analogy even if every symbolic code exists.

## 9. Gauge structure

The existing gauge language is mathematically literal:

- potentials are defined modulo constants;
- gauge fixing selects an anchor;
- edge differences are gauge invariant;
- cycle holonomy obstructs a global potential;
- owner labels give vector-valued holonomy.

A stronger formulation would treat child potentials as local charts and
rebasing identities as transition functions.  Global coherence would amount to
flatness plus strict descent in nonflat directions.  This is useful only if it
produces an explicit cocycle or curvature certificate; otherwise it is a
renaming of the current obstruction.

## Highest-value standalone questions

1. **Owner Hodge theorem.** Give a canonical player-valued Hodge decomposition
   of legal endpoint flows and characterize the strategically inert harmonic
   subspace.
2. **Adiabatic germ tracking.** Establish public occupation tracking for an
   analytic family with Puiseux-order spectral-gap closure under a universal
   schedule and every unilateral law.
3. **Metastable confluence.** Prove that iterated Puiseux-scale fast-class
   reduction is independent of elimination order and compatible with rewards,
   unilateral inequalities, owner labels, public observations, and
   stopped-history rebasing.
4. **Thermal target selection.** Characterize temperature/discount scalings
   whose logit stationary-equilibrium limits are sustainable uniform targets.
5. **Entropy/debt inequality.** Identify endpoint branches where strategic
   damage is bounded by entropy production plus account drift.
6. **Common Dirichlet subclass.** Determine whether shared reversibility and a
   common coercive Dirichlet form suffice to construct uniform equilibrium.
7. **Renormalized progress rank.** Test whether the metastable hierarchy is
   preserved by child rebasing and prevents discharged scales from reappearing.

## Priority assessment

The strongest candidate is now Puiseux-filtered metastable confluence with
rebasing; adiabatic tracking is the complementary implementation problem.
They interact directly with analytic transition scales and may yield either a
schedule constructor or a canonical rank.  This promotion is based on exact
fixed-kernel and convergent-Puiseux resolvent calculations, not yet on a
controlled confluence theorem.  Hodge decomposition is the best
language for unifying potentials, circulation, and owner holonomy.  Thermal
selection is high-risk but easily falsified on benchmark games.  Entropy
production and tilted kernels improve monitoring only on branches where their
quadratic information scale can actually pay the strategic debt.
The K11 branch-semigroup proposal does not change that priority assessment.
