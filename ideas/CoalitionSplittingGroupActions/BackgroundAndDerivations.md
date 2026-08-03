# Coalition splitting under player and phase group actions

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `MIXED` |
| Objective priority | `P2` |
| Last audited | 2026-08-03, through eight isolated group/phase experiments |
| Central live claim | In a player-transitive game, one transportable singleton-split security certificate plus an invariant positive phase-lifted welfare bias suffices for a uniform-equilibrium payoff. |
| Next discriminant | Build or refute the actual stochastic-game automorphism transport law for one nontrivial coalition-split certificate. |
| Production destination | Possible adapter into `WeightedSecurityWelfareAssembly.lean`; no production API is nominated before actual game data supplies transport. |
| Supersedes / superseded by | Offshoot of `CoalitionSecurityWelfareAssembly.md`; complementary to `CycleGeometryResolution.md`. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| CSA1 | Player permutations preserve coalition cardinality and complement; under the full symmetric group, cardinality completely classifies coalition orbits. | `PROVED` | `X` | `CoalitionOrbitTransport.lean`; singleton splits are the size-one case. |
| CSA2 | For a transitive player action, one representative security property plus an explicit transport law yields the property for every player. | `PROVED` | `X` | Abstract property transport; the game-automorphism law is still a hypothesis. |
| CSA3 | On the complete coalition-overlap graph, additive phase offsets are globally alignable iff they form an exact gauge cocycle; triangle zero plus antisymmetry is equivalent. | `PROVED` | `X` | `CoalitionPhaseHolonomy.lean`; arbitrary sparse overlap graphs are not yet formalized. |
| CSA4 | A bounded phase-lifted weighted Bellman bias implies the production all-profile welfare cap with boundary loss `2*C/T`. | `PROVED` | `X` | `PhaseLiftedWelfareCap.lean`. |
| CSA5 | One representative singleton security certificate, its transitive transport law, positive weights, and the production welfare cap imply a uniform-equilibrium payoff. | `PROVED` | `X+L` | `CoalitionEquivariantAssembly.lean`; verification/assembly, not production of its hypotheses. |
| CSA6 | Existence of uniform equilibria for all coalition splits supplies CSA5's transport and cap hypotheses. | `OPEN` | `I` | This is the unproved game-facing implication. |
| CSA7 | A letterwise automorphism intertwining law transports finite cycle words, their periodic fixed points, and equivariant acceptance tests; uniqueness forces stabilizer invariance. | `PROVED` | `X` | `EquivariantWordTransport.lean`; the actual resolved-edge action is open. |
| CSA8 | Orbit-summing a positive player weight makes it positive and invariant, and uniform caps for all translated weights combine into the production cap for that orbit weight. | `PROVED` | `X` | `FiniteGroupInvariantWeights.lean`; transport from one actual cap remains open. |

### Falsifiers and wrong turns

- An abstract permutation of players is not a game automorphism until states,
  dependent actions, transitions, payoffs, initial state, and strategies all
  transport coherently.
- A representative certificate that is not fixed by its stabilizer does not
  define a single-valued equivariant selection.
- Nonzero phase-offset cocycle class obstructs global clock alignment.
- The max-affine holonomy of a cycle word is a semigroup product, not an
  element of a group; cyclic word rotations are not conjugate unless the
  intervening block maps are invertible.
- Orbit averaging or quotienting may erase support, terminal action, owner,
  scale, or provenance, invalidating the resolved strategic certificate.
- The K11 overlap, owner nontransfer, terminal packet at infinity, and
  strategic decoder gaps from `CycleGeometryResolution.md` are untouched.

### Production map

```text
one singleton split --actual automorphism--> all security floors       [?]
phase-state social bias --------------------> production welfare cap    [X]
positive cap + automorphism orbit ----------> invariant positive cap    [X -> ?]
all floors + positive welfare cap ----------> uniform payoff            [L]
resolved cycle word --action groupoid-------> orbit/stabilizer reduction [?]
coalition overlap offsets --zero cocycle----> common clock convention   [X]
```

CSA5 checks the middle assembly.  The arrows ending in `?` are the genuine
game-facing coalition-splitting producers or transport adapters.

### Exit conditions

- Mark `MINED` when an actual game automorphism adapter and one supplied
  coalition-split certificate instantiate CSA5, or when an audited
  counterexample rules out that adapter at the intended scope.
- Mark CSA6 `WRONG` only after a game-level counterexample; the bare
  quantifier objection is not enough.
- Mark `BLOCKED` if a named live game supplies symmetric split data but the
  missing dependent action/history transport API prevents formalization.
- Mark `PARKED` if no current P0/P1 producer supplies coalition certificates
  on which the symmetry reduction can act.
- Mark `SUPERSEDED` if another idea group provides the same transport, phase
  alignment, and assembly interfaces with an actual downstream consumer.

## Scope

This note asks exactly how group actions and periodic profiles can strengthen
the coalition-splitting approach to uniform equilibrium.  General cyclic
analysis and general orbit-lattice gluing live in separate notes:

- [`CyclicPhaseReynolds.md`](CyclicPhaseReynolds.md);
- [`FiniteGroupOrbitGluing.md`](FiniteGroupOrbitGluing.md);
- [`EquivariantWordTransport.md`](EquivariantWordTransport.md);
- [`FiniteGroupInvariantWeights.md`](FiniteGroupInvariantWeights.md).

The baseline assembly theorem and its limitations are in
[`CoalitionSecurityWelfareAssembly.md`](CoalitionSecurityWelfareAssembly.md).

## Alignment with the cycle-geometry program

[`ideas/CycleGeometryResolution.md`](../ideas/CycleGeometryResolution.md)
already gives two meanings to cycle structure that must not be conflated with
the groups below:

1. a periodic code is a repeated word in a resolved directed graph, with a
   periodic lift under contraction;
2. the strategic summary of a word is a product in the
   `MaxAffineHolonomySemigroup`, which has no real-valued identity and whose
   block maps need not be invertible.

The cyclic group in this note acts only on the **clock positions of an already
certified periodic split profile**.  The additive offsets below compare clock
choices between coalition certificates.  They are a gauge cocycle, not the
max-affine block holonomy.

The safe group-theoretic object over the resolved atlas is therefore an
**action groupoid**, not a destructive quotient.  If a game automorphism `g`
acts on resolved vertices, edges, and fibers by maps `A_g`, equivariance of a
block map has the form

```text
T_(g.e) = A_g * T_e * A_(g^-1).
```

Induction on a certified word gives the same transport law for its composite.
This reduces word validation to orbit representatives and stabilizer checks,
while retaining support, terminal action, owner, scale, and provenance.  It
does not create the exhaustive repair relation CG5 or the strategic decoder
CG8.  Likewise, rotating a word changes its based semigroup product; it is
only group conjugacy when the relevant block maps are invertible.

The general word calculation and its stabilizer theorem are proved separately
in [`EquivariantWordTransport.md`](EquivariantWordTransport.md).  This
coalition note uses them only after the relabeling action has been supplied on
the fully resolved split certificates.

At the present abstraction boundary, the structurally honest uses of group
theory are therefore: orbit--stabilizer reduction of split obligations,
action-groupoid transport of fully labelled certificates, additive
cohomology of clock choices, and character decomposition of the cyclic clock.
Pushing further requires an actual automorphism action on the resolved game
data.  Group theory can compress or align a supplied producer; it cannot
replace strategic exhaustiveness.

## 1. Symmetries of coalition splits

Let `I` be the finite player set and let `Gamma` be a finite group of
automorphisms of the stochastic game.  An automorphism acts on:

- players `i |-> g.i`;
- states;
- each dependent action type;
- joint actions and histories;
- behavior strategies and profiles;
- payoff coordinates;
- coalitions `C |-> g.C`.

It must preserve the transition law and relabel stage payoffs.  If the initial
state is fixed, finite-horizon and uniform-equilibrium statements transport
without changing the initial condition.

The complement involution commutes with player permutations:

```text
g.(I \ C) = I \ g.C.
```

Thus unordered coalition splits are acted on by the player group together
with complement.  Under the full symmetric group, coalition orbits are
classified by cardinality up to `k <-> |I|-k`.  In particular, all singleton
splits form one orbit.  `CoalitionOrbitTransport.lean` checks the stronger
labelled statement: two coalitions are related by a player permutation if and
only if their cardinalities agree.

### Consequence

In a player-transitive game, one singleton-versus-complement security theorem
transports to every player.  This does not yet glue the strategies, but it
reduces the independent analytic work from one proof per player to one proof
per player orbit.

## 2. Equivariant security--welfare assembly

Assume:

1. `Gamma` fixes the initial state;
2. the target payoff `v` is equivariant, and hence constant on player orbits;
3. a one-sided uniform security certificate is known for one representative
   of each player orbit;
4. certificate transport along game automorphisms is available;
5. a strictly positive invariant weight vector has a uniform weighted welfare
   cap at `v`.

Transport gives a one-sided security certificate for every player.  The
verified theorem

```text
isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_positiveWeightedWelfareCap
```

then yields `IsUniformEquilibriumPayoff s0 v`.

### Transitive special case

If `Gamma` is transitive on players, it suffices to provide:

- one singleton-split security certificate at the common value `m`;
- the invariant total-welfare cap

```text
sum_i payoff_i <= |I| * m + o(1).
```

This is the cleanest genuinely group-theoretic variation of the original
coalition-splitting question.  Group transport supplies all singleton floors;
welfare saturation supplies compatibility.

### Invariantizing the welfare separator

An invariant weight need not be guessed.  Given any strictly positive weight
`alpha`, define

```text
barAlpha(i) = sum_(g in Gamma) alpha(g.i).
```

Then `barAlpha` is strictly positive and invariant.  If a game automorphism
transports a welfare cap for `alpha` to a cap for every translated weight,
summing those finitely many caps gives the cap for `barAlpha`.  The finite
algebra is isolated in
[`FiniteGroupInvariantWeights.md`](FiniteGroupInvariantWeights.md).
The missing statement is again the actual game/profile transport, not the
Reynolds calculation.

## 3. Rotating-role split certificates

Stationary player symmetry is unnecessarily restrictive.  Fix a period `P`
and a homomorphism

```text
chi : Gamma -> C_P.
```

The diagonal action on player--phase pairs is

```text
g . (i,q) = (g.i, q + chi(g)).
```

A periodic profile is diagonally equivariant when

```text
sigma_(g.i, q + chi(g)) = g . sigma_(i,q).
```

This permits turn-taking: the action profile at one phase is asymmetric, but
player relabeling is compensated by rotating time.  If the diagonal action is
transitive, a phasewise deviation calculation for one player--phase pair
transports to every pair.

For a transported selection to be well-defined, the data at a representative
must be invariant under the stabilizer of that representative.  Otherwise two
group elements reaching the same player--phase pair may prescribe different
strategies.

## 4. Phase-lifted coalition welfare cap

Let

```text
W_q(s,a) = sum_i alpha_i * u_i,q(s,a)
```

for invariant positive weights `alpha`.  Suppose a periodic social bias
`B_q(s)` satisfies

```text
W_q(s,a) + E[B_(q+1)(s') | s,a]
  <= sum_i alpha_i*v_i + B_q(s)
```

at every phase, state, and joint action.  A bounded `B` gives, uniformly in
the starting phase and behavior profile,

```text
sum_i alpha_i * gamma_i^T
  <= sum_i alpha_i*v_i + 2*C/T.
```

This is exactly the cap needed by security--welfare assembly.  The cyclic
Reynolds theorem explains why purely oscillatory phase dependence can be
absorbed into `B`: it is a phase coboundary.

## 5. Coalition constraints as group orbits

Suppose a coalition split `C | I\C` produces a feasible continuation set
`F_C`.  Equivariance means

```text
F_(g.C) = g.F_C.
```

There are two safe ways group structure can provide a common selection.

### 5.1 Equivariant transport

Choose one representative per coalition orbit and require stabilizer-fixed
data.  Transport gives a coherent selection for all coalitions in that orbit.
This produces related witnesses, but not necessarily one witness satisfying
all coalition constraints.

### 5.2 Monotone orbit gluing

If the continuation space is a semilattice and all `F_C` are upward closed,
the join of the translated witnesses lies in every `F_C` in the orbit.  For
downward-closed constraints, use the orbit meet.  This is a genuine conversion
from separate split witnesses to one invariant common witness.

For upper Bellman supersolutions the useful operation is normally the
pointwise meet, not the join.

## 6. Phase-offset gauge cocycle for split equilibria

Suppose coalition-split profiles agree on overlaps only after phase shifts.
Attach an oriented offset

```text
omega(C,D) in C_P
```

to each compatible overlap edge, with the reverse edge carrying the negative
offset.  On each connected component of the overlap graph, a phase assignment
`theta(C)` with

```text
omega(C,D) = theta(D) - theta(C)
```

exists exactly when the offset sum around every closed walk is zero.

### Proof

If `omega` is a difference of vertex phases, every cycle sum telescopes to
zero.  Conversely, choose a root coalition and define `theta(C)` by summing
offsets along a path from the root to `C`.  Zero cycle sums make the result
independent of the chosen path.  QED.

Thus vanishing of the additive gauge-cocycle class aligns the split profiles
into one periodic phase convention.  A nonzero class is an explicit
obstruction to periodic coalition-split gluing.  This refines the bare logical
failure of `forall C, exists sigma_C`.

This terminology is intentionally separate from the repository's
max-affine holonomy semigroup.  The latter composes strategic block maps along
one based cycle word.  The former is an additive comparison of clock origins
between different coalition certificates.  The Lean experiment currently
checks the complete-overlap case, where antisymmetry and zero triangle sums
generate all closed-walk conditions.

## 7. Proposed coalition theorem

The strongest defensible target is:

> **Periodic equivariant split assembly.** Let a finite automorphism group
> fixing the initial state act on a stochastic game, its players, and its
> coalition splits.  Suppose singleton-split security certificates are given
> for orbit representatives and transport equivariantly, with any phase
> offsets forming an exact gauge cocycle.  Suppose an invariant positive weighted
> phase-lifted social bias caps weighted welfare at the transported target.
> Then the target is a uniform-equilibrium payoff.

The proof factors into independently checkable modules:

1. coalition/player automorphism transport;
2. phase alignment from exactness of the offset cocycle;
3. phase-lifted welfare telescope;
4. positive weighted security--welfare assembly.

This theorem does not follow from split-equilibrium existence alone.  It adds
precisely the equivariance, phase compatibility, and aggregate saturation
which the naive statement lacks.

## 8. Formalization boundary

The checked files are:

- [`experiments/CyclicPhaseReynolds.lean`](../experiments/CyclicPhaseReynolds.lean),
  for clock averaging, cyclic coboundaries, exact windows, and the `2*C/T`
  estimate;
- [`experiments/FiniteGroupOrbitGluing.lean`](../experiments/FiniteGroupOrbitGluing.lean),
  for invariant orbit suprema/infima and monotone constraint gluing;
- [`experiments/CoalitionPhaseHolonomy.lean`](../experiments/CoalitionPhaseHolonomy.lean),
  for the complete-overlap phase-offset cocycle and diagonal player--phase
  action laws;
- [`experiments/CoalitionOrbitTransport.lean`](../experiments/CoalitionOrbitTransport.lean),
  for coalition permutation, complement, singleton-orbit, and abstract
  transitive property transport;
- [`experiments/PhaseLiftedWelfareCap.lean`](../experiments/PhaseLiftedWelfareCap.lean),
  for the phase-state Bellman telescope into the production welfare-cap
  predicate; and
- [`experiments/CoalitionEquivariantAssembly.lean`](../experiments/CoalitionEquivariantAssembly.lean),
  for the coalition-specific composition of one representative certificate,
  its explicit transport law, and the landed weighted assembly theorem; and
- [`experiments/EquivariantWordTransport.lean`](../experiments/EquivariantWordTransport.lean),
  for whole-word intertwining, periodic fixed-point transport, and
  stabilizer-fixed uniqueness; and
- [`experiments/FiniteGroupInvariantWeights.lean`](../experiments/FiniteGroupInvariantWeights.lean),
  for positive invariant orbit weights and summation of translated linear
  welfare caps.

The last theorem deliberately assumes the transport law rather than building
a speculative dependent stochastic-game automorphism API.  Combining it with
the phase-cap theorem is mathematically immediate through their shared
production predicate, while the experiment files remain independently
checkable and do not import one another.
