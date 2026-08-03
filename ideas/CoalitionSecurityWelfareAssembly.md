# Uniform equilibrium from coalition splits: structural ideas

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `MINED` |
| Verdict | `MIXED` |
| Objective priority | `P2` |
| Last audited | 2026-08-03, commits `81aec6c` and `bf65314` |
| Central live claim | Positive singleton security floors plus one saturated positive weighted all-profile welfare ceiling assemble into a uniform-equilibrium payoff. |
| Next discriminant | None for the assembly theorem; any attempt to produce the ceiling from quitting-boundary separation is a separate idea group. |
| Production destination | Weighted security--welfare assembly and bounded Bellman-bias cap modules. |
| Supersedes / superseded by | Naive split-equilibrium gluing is wrong; the saturation theorem is the replacement. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| CS1 | Independently chosen split witnesses can be glued merely by exchanging `forall` and `exists`. | `WRONG` | `M` | Logical gluing schema only; this does not by itself refute every specially structured game-level split theorem. |
| CS2 | Playerwise one-sided security at `v`, together with one saturated strictly positive weighted all-profile welfare cap at `v`, implies that `v` is a uniform-equilibrium payoff. | `PROVED` | `M+L` | `WeightedSecurityWelfareAssembly.lean`. |
| CS3 | A bounded weighted Bellman bias implies the all-profile welfare cap with endpoint loss `2*C/T`. | `PROVED` | `M+L` | `WeightedWelfareBias.lean`; consumed by CS2. |
| CS4 | Uniform equilibria of all coalition splits, without further compatibility assumptions, produce the security floors and saturated welfare cap required by CS2. | `OPEN` | `I` | This is the remaining content of the user's original possible implication. |
| CS5 | Game automorphisms and cyclic phases can reduce the number of split certificates and align them before CS2 is applied. | `CONDITIONAL` | `I+X` | Separated into `CoalitionSplittingGroupActions.md`; an actual game-automorphism adapter is missing. |

### Falsifiers and wrong turns

- Playerwise feasibility does not imply intersection of the playerwise
  feasible profile sets; the quantifier exchange in CS1 is invalid.
- A coalition action may correlate its members, whereas an original behavior
  profile mixes players independently.  Any quotient that forgets this is not
  a sound source of strategies.
- A common split payoff vector, public time-sharing, or one-stage deviation
  checks do not supply the history-uniform behavioral deviation inequalities.
- CS4 would be refuted by one finite stochastic game in which every specified
  split has a uniform equilibrium but the original game has none.  No such
  game-level counterexample is claimed here.

### Production map

```text
singleton split certificate --game adapter--> one-sided security floors [?]
planner / separator ----------Bellman bias--> weighted welfare cap       [L]
security floors + welfare cap ----------------> uniform payoff            [L]
player/phase symmetry --------transport-----> fewer independent floors   [X -> ?]
```

The production theorem verifies assembly; it does not produce its split-game
hypotheses.  The first and last arrows are the remaining coalition-specific
interfaces.

### Exit conditions

- Remain `MINED` while CS2--CS3 are landed and every live producer question is
  owned by a separate idea group.
- Reopen this group only if a theorem or counterexample settles CS4 at the
  level of actual stochastic games.
- Mark CS4 `WRONG` only after a genuine game-level counterexample, not merely
  the abstract quantifier objection.
- The symmetry/periodic offshoot is mined or parked independently in
  `CoalitionSplittingGroupActions.md`.

The central assembly claim is mined and in production. The naive inference
from separately existing split equilibria is wrong. The dynamic-potential,
Doeblin, lattice, and punishment variants below are retained as parked
offshoots; they do not keep this group active.

## Status and scope

This note records research ideas prompted by the question:

> Can uniform equilibria of coalition-split games be assembled into a
> uniform equilibrium of the original multiplayer stochastic game?

The ambient definitions are those of
`GameTheory/Concepts/Stochastic/Uniform.lean`.  In particular, a uniform
equilibrium payoff permits the behavior profile to depend on the requested
accuracy, but at a fixed accuracy one profile and one horizon threshold must
simultaneously control every player's behavioral deviations at every longer
horizon.

The main conclusion is that mere existence of an equilibrium for every split
does not supply the required compatibility.  The most promising replacement
is a **security-floor / welfare-ceiling assembly principle**.  It turns
separate singleton-versus-complement security strategies into one equilibrium
profile without trying to make the split equilibria themselves coincide.

This file distinguishes:

* statements which should admit short proofs using existing repository APIs;
* structural hypotheses which plausibly produce those statements;
* speculative routes whose missing steps are stated explicitly;
* tempting but invalid inferences already fenced by repository examples.

## 1. Why the naive split statement does not glue

For a finite player set `I`, a singleton split gives data of the form

```text
for every i, there exists a profile sigma_i controlling player i.
```

The original uniform-equilibrium condition needs

```text
there exists one profile sigma which controls every i.
```

Thus the logical gap is

```text
(forall i, exists sigma_i, P i sigma_i)
    does not imply
(exists sigma, forall i, P i sigma).
```

Different horizon thresholds are not the issue: because the player set is
finite, their maximum is a common threshold.  The incompatible profiles are
the issue.  `FinkContinuationCompatibilityCounterexample.lean` gives the
finite-dimensional local model of precisely this failure: player zero can
satisfy its inequalities only toward the high end of a common continuation
segment, player one only toward the low end, and both playerwise systems are
feasible although the coupled system is not.

There are two preliminary modeling issues as well.

1. A coalition has several original payoff coordinates, so a virtual
   coalition player needs a specified scalar objective.
2. A virtual player mixing over joint actions can correlate its members'
   simultaneous moves.  An original `BehaviorProfile` uses independent mixed
   actions at each public history.  An action-level coalition quotient is
   therefore not automatically lossless for behavior profiles.  The
   game-form-level `mergeCoalition` avoids this by bundling already chosen
   whole strategies, but that object does not itself define coalition
   utilities or a finite stochastic-game quotient.

Consequently, any lifting theorem must either require product-decomposable
coalition play, supply an implementable deviation-safe public coin, or work
only with the singleton side of a split, whose strategy needs no internal
correlation.

## 2. Primary idea: security floors plus a weighted welfare ceiling

### 2.1 One-sided uniform security

Fix an initial state `s0`, positive weights `alpha i`, and a target payoff
vector `v`.

For every player `i`, assume a one-sided uniform guarantee at `v i`: for every
`eta > 0`, player `i` has one behavior strategy `secure i` and one threshold
`T_i` such that, against every completion by all other players and at every
horizon `T >= T_i`,

```text
v i - eta <= gamma_i^T (secure i, arbitrary completion).
```

This is exactly the existing predicate
`StochasticGame.IsOneSidedGuaranteeCertificate` in
`AdaptiveCertificate.lean`.

The zero-sum split `{i} | I \ {i}` with payoff `u_i` is the natural source of
this strategy.  Only the singleton's maximizing strategy is transported back
to the original game.  The complementary virtual player may be more powerful
than the original independent opponents; a guarantee against that larger
class remains a guarantee against original completions.

### 2.2 Uniform weighted welfare cap

Assume, in addition, that no behavior profile can asymptotically exceed the
weighted target welfare.  The clean semantic form is:

```text
for every kappa > 0, there is Tcap such that
for every profile pi and every T >= Tcap,
  sum_i alpha_i * gamma_i^T(pi)
    <= sum_i alpha_i * v_i + kappa.
```

Call this a `UniformWeightedWelfareCap` at `(alpha, v)`.

The cap can be obtained from a grand-coalition planner problem which maximizes
the scalar reward `sum_i alpha_i * u_i`.  It can also be certified directly
by a bounded scalar state bias `B` satisfying, for every state and every joint
action,

```text
sum_i alpha_i * stagePayoff(s,a,i)
  + E[B(nextState) | s,a]
  <= sum_i alpha_i * v_i + B(s).
```

The latter inequality telescopes under every history-dependent behavior
profile.  If `|B| <= C`, it gives the quantitative cap

```text
sum_i alpha_i * gamma_i^T(pi)
  <= sum_i alpha_i * v_i + 2*C/T.
```

This bias form is strictly more flexible than a stagewise constant-sum
identity.

### 2.3 Assembly theorem

**Proposed theorem (high confidence).**  Suppose:

* `alpha i > 0` for every player;
* every player has a one-sided guarantee at `v i`;
* `(alpha, v)` has a uniform weighted welfare cap.

Then `v` is a uniform-equilibrium payoff.

This should be formalized as something close to:

```text
isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_weightedWelfareCap
```

#### Proof sketch

At a small common error `eta`, choose each player's securing strategy and form
the product behavior profile

```text
sigma i = secure i.
```

Let `p_i` be player `i`'s on-path `T`-horizon payoff.  Every security floor
holds on path:

```text
p_i >= v_i - eta.
```

The welfare cap gives

```text
alpha_i * (p_i - v_i)
  <= kappa + sum_{j != i} alpha_j * (v_j - p_j)
  <= kappa + eta * sum_{j != i} alpha_j.
```

Hence every on-path coordinate is close to `v_i` from above as well as below.

Now let player `i` replace its whole behavior strategy.  Every `j != i`
continues playing its security strategy, so the same one-sided guarantee gives

```text
deviatingProfilePayoff_j >= v_j - eta.
```

Applying the welfare cap to the deviating profile yields

```text
deviatingProfilePayoff_i
  <= v_i
     + (kappa + eta * sum_{j != i} alpha_j) / alpha_i.
```

Finiteness and strict positivity of the weights allow `eta` and `kappa` to be
chosen uniformly small enough for all players.  These are exactly the on-path
delivery and deviation caps consumed by
`isUniformEquilibriumPayoff_of_deviation_caps`.

### 2.4 Interpretation as value saturation

Let `m_i(s0)` be player `i`'s uniform security value in the singleton split,
and let `W_alpha(s0)` be the grand-coalition planner value for weighted welfare.
The elementary weak inequality is

```text
sum_i alpha_i * m_i(s0) <= W_alpha(s0).
```

The structural hypothesis is equality:

```text
sum_i alpha_i * m_i(s0) = W_alpha(s0).
```

Under equality, the singleton floors saturate the only available aggregate
room, so they cannot be mutually incompatible.  This is a useful replacement
for demanding a common equilibrium selection from the split games.

For a stagewise constant-sum game `sum_i alpha_i*u_i = C`, the welfare cap is
automatic.  The remaining condition is simply

```text
sum_i alpha_i * m_i = C.
```

For two-player zero-sum games this specializes to the existing assembly of the
two one-sided guarantees in `AdaptiveCertificate.lean`.

### 2.5 Quantitative slack

If the cap is instead

```text
sum_i alpha_i * gamma_i^T(pi)
  <= sum_i alpha_i * v_i + Delta + o_T(1),
```

the same proof constructs a profile with asymptotic exploitability bounded by
approximately

```text
Delta / alpha_i
```

for player `i`.  Thus the normalized saturation defect is a quantitative
measure of the failure of this assembly method.  A sequence of weights or
targets whose defect is small relative to every `alpha_i` would still yield a
uniform equilibrium by diagonal selection.

## 3. Partition and coalition-tree variants

Let a partition `P` of the players consist of disjoint teams.  Give each team
`C` a scalar aggregate payoff `U_C` and a uniform security strategy against
the other teams.  If positive team weights and team security levels saturate a
global aggregate cap, the preceding proof produces a uniform equilibrium of
the **team quotient**.

To lift that quotient equilibrium to the original players, one still needs an
internal alignment condition.  A clean sufficient condition is coalition-wise
identical interest:

```text
u_i = c_i * U_C + d_i       for i in C, with c_i > 0,
```

where the equality is at the payoff-process level (or differs only by a
bounded telescoping coboundary).  Then an improving deviation by a member is
an improving deviation for its team objective and is ruled out by team
equilibrium.

The team strategy must also be implementable as original behavior strategies.
Possible sufficient interfaces are:

* the team mixed action factors into the members' mixed actions at every
  history;
* the team equilibrium is pure;
* a deviation-safe public randomization device implements the correlation.

A **laminar coalition tree** could recursively apply this construction.  At
each internal node, the children are disjoint, their security floors saturate
the parent's welfare ceiling, and their strategies compose.  Laminarity avoids
the inconsistent prescriptions created by overlapping coalitions.  This is a
real coalition-splitting theorem, but the compatibility fields must be part of
the certificate rather than inferred from bare equilibrium existence.

## 4. Dynamic potential games modulo coboundaries

A separate structural class can be reduced to a one-player planner problem.
Suppose there is a common scalar stage objective `Phi`, constants `c_i > 0`
and `d_i`, and bounded state functions `h_i` such that

```text
stagePayoff(s,a,i)
  = c_i * Phi(s,a) + d_i
    + h_i(s) - E[h_i(nextState) | s,a].
```

After summing over time, the `h_i` term telescopes.  Uniformly over every
behavior profile,

```text
gamma_i^T(pi)
  = c_i * plannerAveragePhi^T(pi) + d_i + O(1/T).
```

Thus every player's long-average incentives are positively aligned with one
planner objective, even though transitions may depend on actions and the
finite-horizon stage payoffs are not literally identical.

A uniformly optimal pure policy of the finite MDP whose actions are original
joint actions then unbundles coordinatewise into a behavior profile.  Global
planner optimality rules out every unilateral improvement, up to the
telescoping boundary.  The stationary policy's finite Markov chain supplies a
limiting payoff vector.

This should yield a theorem of the form:

```text
exists_uniformEquilibriumPayoff_of_dynamicExactPotentialCoboundary
```

Possible generalization: require only that unilateral payoff differences equal
positive multiples of planner-objective differences modulo a bounded
coboundary, rather than equality of the entire payoff processes.

Ordinary statewise exact-potential structure is not enough by itself: a
deviation can change the future state law and thereby change nominally
"nonstrategic" state-dependent payoff terms.  The coboundary condition is what
makes those changes wash out uniformly in long averages.

## 5. Finite-dimensional compatibility: Helly and lattice mechanisms

These are local tools for a Fink endpoint or a finite public-response
architecture, not standalone global equilibrium theorems.

### 5.1 Helly locality

Let `K` be a convex continuation cell of affine dimension `d`.  For each
player let

```text
F_i = {x in K | every continuation inequality owned by i holds at x}.
```

If the `F_i` are convex, Helly's theorem gives:

```text
if every subfamily of at most d+1 player sets has nonempty intersection,
then the intersection of all player sets is nonempty.
```

This suggests replacing "every singleton split is feasible" with the stronger
but still local hypothesis:

> Every set of at most `d+1` players admits one common continuation witness.

In continuation dimension one, checking players individually is insufficient;
pairwise compatibility is the correct Helly test.  This exactly diagnoses the
two-player, one-coordinate continuation counterexample.

Potential benefit: if the active continuation dimension is much smaller than
the number of players, global compatibility can be certified by bounded-size
coalitions.  The remaining work is to show that the relevant endpoint sets are
actually convex within the chosen cell and to transport the common local
continuation through the history-level recursion.

### 5.2 Common-order or lattice gluing

Suppose `K` is closed under finite joins in a partial order and every `F_i` is
upward closed.  Choose `x_i in F_i` separately and set

```text
x = join_i x_i.
```

Then `x` belongs to every `F_i`.  The dual statement uses meets and downward
closed sets.

This is an exact abstract gluing lemma.  Its game-theoretic content is that all
players' continuation constraints have a common orientation: raising the
continuation in the selected order never breaks another player's constraint.
The local counterexample fails because one player requires the shared
coordinate to rise while the other requires it to fall.

A computational structural test could search for a cone or a signed coordinate
order which contains all active deviation normals, together with a proof that
the endpoint cell is closed under the induced joins.  This is restrictive but
clean and falsifiable.

## 6. Uniform regeneration / Doeblin transitions

Consider the strong action-uniform minorization condition

```text
transition(s,a) >= eta * nu
```

for fixed `eta > 0` and a fixed state law `nu`, for every state and every joint
action.  Every induced kernel then contracts the span seminorm by a common
factor below one.

A plausible vanishing-discount route is:

1. choose discounted stationary Fink equilibria as the discount tends to one;
2. use uniform span contraction to prove that their value spans are
   `O(1-beta)`;
3. normalize relative biases modulo state-constant functions and extract a
   convergent subsequence;
4. pass the discounted Bellman equalities and unilateral inequalities to an
   average-reward gain-bias certificate;
5. apply the existing stationary-average/bias verification theorem.

`FinkLimit.lean` already proves that a strictly positive limiting induced
kernel makes a harmonic limiting payoff state-constant and has a conditional
uniform-equilibrium theorem for that branch.  The missing step is a robust
**bias modulo constants** compactness lemma.  The current relative-bias theorem
asks for convergence before quotienting out state-constant shifts, which can
fail even when the span is uniformly bounded.

This condition is substantially stronger than irreducibility of one selected
equilibrium kernel, but it gives a concrete multiplayer, action-dependent
special class beyond action-independent transitions.  A weaker eventual
common-regeneration or uniformly bounded hitting-time condition may suffice
once the span-contraction proof is isolated.

## 7. Detectable deviations plus singleton punishments

Singleton split values naturally provide punishment strategies.  A possible
history-level theorem would assume:

* state-uniform singleton security levels and punishment strategies;
* a feasible recurrent target payoff strictly above those security levels;
* public statistical identifiability of every profitable unilateral deviation;
* a bounded-cost public reset into the appropriate punishment mode.

One could then maintain player-indexed deviation accounts.  A positive account
drift selects the player whose singleton/complement punishment is activated.
False-alarm and switching costs must be sublinear, and deviations which change
only transition laws must be detected by public transition scores rather than
one-stage payoff comparisons.

The repository's public-response, contextual-monitor, stopping, and adaptive
certificate machinery already provides most of the verification side.  The
missing theorem is the constructor which turns a family of split security
strategies plus the detectability/reset hypotheses into one public response
architecture.  This route is higher risk than the saturation theorem because
state-dependent punishments and invisible deviations are the core difficulty,
not bookkeeping.

## 8. Finite-ranked transient games

Another plausible special class has a rank on states such that every
nonterminal transition strictly lowers rank and rank-zero states are absorbing.
There are then only boundedly many strategically active stages before an
absorbing continuation.

Backward induction can select a finite-horizon Nash action at each rank using
the already constructed child payoff.  Because the active prefix has uniformly
bounded length, its contribution to a `T`-stage average is `O(1/T)`.  This
should extend the existing one-step absorbing-child theorem to arbitrary
finite strict depth.

Self-loops at nonterminal states must be excluded: allowing them immediately
recovers absorbing/quitting-game phenomena and loses bounded-depth induction.
The partial fixed-depth and ranked-child prototypes in the repository indicate
that the main proof obligation is a clean deviation-law transfer through the
terminal stopping depth.

## 9. Things not to infer

### 9.1 Same payoff vector is not enough

Split equilibria may all converge to the same payoff vector while using
incompatible opponent strategies.  Original deviations are evaluated against
the actual common opponent profile, so payoff agreement alone does not glue
the incentive inequalities.

### 9.2 Public time-sharing does not average away regret

Randomly or periodically announce which split equilibrium is being played.
A deviator observes the phase and can obey in phases where deviation is
unprofitable and deviate only in favorable phases.  Maximal deviation gain in
each public phase is nonnegative, so signed gains cannot simply cancel under a
convex combination.  Time-sharing becomes useful only when deviations create
future debt or affect mode selection, which is an adaptive-potential/public-
punishment argument rather than ordinary averaging.

### 9.3 One-stage tests do not control behavioral deviations

Neither a one-shot opponent minmax nor "deviate once and immediately obey"
can replace a cap against arbitrary behavior strategies.  The repository's
`ArchitectureCapSeparators.lean` contains finite counterexamples to both
substitutions.  Any coalition-derived input to the assembly theorem should
therefore target `IsOneSidedGuaranteeCertificate`, not a static surrogate.

### 9.4 Strong coalitional equilibrium is too strong

Requiring one common profile which deters every coalition deviation would
indeed imply ordinary uniform equilibrium, but it is a uniform strong-
equilibrium condition and should not be expected to exist even in simple
finite games.  Coalition splits are useful as security or aggregation tools;
they should not silently change the desired solution concept.

## 10. Experiment plan

The following standalone Lean experiments are the immediate targets.

### Experiment A: semantic weighted assembly

Define a uniform weighted welfare-cap predicate and prove:

```text
all one-sided guarantees
  + positive weights
  + uniform weighted welfare cap
  => IsUniformEquilibriumPayoff.
```

This is the highest-priority result.  It should use only
`AdaptiveCertificate.lean`, finite maxima/sums, and the existing
`isUniformEquilibriumPayoff_of_deviation_caps` waist.

### Experiment B: Bellman welfare cap

Prove that a bounded scalar potential satisfying the universal one-step
weighted welfare inequality produces the semantic uniform cap with explicit
boundary `2*C/T`.  Compose it with Experiment A.

### Experiment C: lattice gluing

Prove the abstract finite join lemma:

```text
finite family of nonempty upward-closed subsets
  + ambient finite joins
  => common point obtained by joining witnesses.
```

Also state a coordinatewise real-vector specialization suitable for finite
continuation boxes.

### Experiment D: dynamic potential telescope

Prove only the safe algebraic core initially: under the common-objective plus
coboundary identity, every finite-average player payoff equals the affine
planner payoff plus an explicit endpoint term.  A later experiment can attach
the finite-MDP uniform-optimal-policy existence theorem.

### Experiment E: quantitative saturation defect

Generalize Experiment A to a cap with fixed slack `Delta` and derive explicit
payoff-delivery and exploitability bounds.  This turns the idea into a usable
diagnostic even when exact saturation fails.

## 11. Priority assessment

1. **Security floors + welfare ceiling:** strongest immediate theorem; short,
   directly connected to coalition splitting, and built on stable APIs.
2. **Bellman/social-bias source of the ceiling:** natural companion and likely
   short.
3. **Dynamic potential modulo coboundary:** promising new structural game
   class; planner optimality is the main external ingredient.
4. **Product-decomposable aligned-team lifting:** direct coalition theorem,
   but correlation implementability must remain explicit.
5. **Doeblin/span-contraction closure:** substantial special case with a clear
   missing quotient-bias lemma.
6. **Helly/lattice continuation gluing:** useful local selection tools; their
   global history-level transport remains separate.
7. **Detectability plus punishments:** conceptually broadest and most closely
   tied to the full open problem; highest construction risk.

## 12. Formalization status

Three standalone experiments now check the main algebraic claims.

- [`experiments/WeightedSecurityWelfareAssembly.lean`](../experiments/WeightedSecurityWelfareAssembly.lean)
  proves Experiments A and B.  It includes the semantic assembly theorem,
  normalization from arbitrary strictly positive weights, the universal
  weighted Bellman-bias certificate, and their composition into a uniform
  equilibrium payoff theorem.
- [`experiments/ContinuationLatticeGluing.lean`](../experiments/ContinuationLatticeGluing.lean)
  proves Experiment C for finite joins and, dually, finite meets.  It also
  gives the coordinatewise continuation-vector specialization and a
  quantitative join lemma for antitone violation measures.
- [`experiments/DynamicPotentialCoboundary.lean`](../experiments/DynamicPotentialCoboundary.lean)
  proves Experiment D.  The result holds for every behavior profile: the
  finite average is exactly the affine common-reward average plus the two
  endpoint potentials divided by `T`.  If the potential is bounded in
  absolute value by `C`, the discrepancy is at most `2*C/T`.
- [`experiments/WeightedSaturationDefect.lean`](../experiments/WeightedSaturationDefect.lean)
  proves the finite-dimensional core of Experiment E.  A welfare-cap slack
  `Delta` and security error `eta` imply the sharp coordinate excess bound
  `(Delta + eta * sum(other weights)) / weight i`; the file also derives the
  corresponding target interval and unilateral exploitability bound.

These results do **not** prove that arbitrary coalition-split uniform
equilibria glue.  They identify three concrete compatibility mechanisms that
do work: a saturated positive aggregate cap, monotone continuation sets, and
common interest modulo a bounded dynamic coboundary.

## 13. Follow-up: symmetry and periodic split alignment

The group-theoretic question raised after this report has its own
coalition-specific note:

- [`CoalitionSplittingGroupActions.md`](CoalitionSplittingGroupActions.md)
  studies player permutations acting on coalitions, rotating-role periodic
  split certificates, stabilizer compatibility, phase holonomy, and the
  equivariant security--welfare assembly theorem schema.

Four independent mathematical ingredients are deliberately kept out of this
coalition report:

- [`CyclicPhaseReynolds.md`](CyclicPhaseReynolds.md) develops periodic
  phase signals as the regular representation of a finite cyclic group;
- [`FiniteGroupOrbitGluing.md`](FiniteGroupOrbitGluing.md) develops
  invariant join/meet constructions for monotone orbit constraints;
- [`EquivariantWordTransport.md`](EquivariantWordTransport.md) develops
  action-groupoid transport of finite block words and periodic fixed points;
- [`FiniteGroupInvariantWeights.md`](FiniteGroupInvariantWeights.md)
  develops Reynolds orbit sums for positive invariant welfare caps.

The coalition note imports these ingredients conceptually and states exactly
which additional game-transport laws would turn them into a theorem about
coalition-split uniform equilibria.
