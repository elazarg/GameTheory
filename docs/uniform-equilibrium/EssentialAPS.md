# Essential APS: from coherent execution to uniform payoffs

This module family formalizes the certificate-facing part of the essential APS
approach of Ashkenazi-Golan, Krasikov, Rainer, and Solan, *The APS approach for
undiscounted quitting games* (International Journal of Game Theory 55:19,
2026).

The result is conditional: it concerns a compact functional
unique-live-successor singleton-flow stratum.  Within that stratum, the
formalization proves the following chain:

1. algebraic convexification reduces to a one-continuation executable segment;
2. zero-mass propagation is separated from genuine positive-mass progress;
3. local progress choices compose into finite runs and, on the terminal-free
   branch, one coherent infinite run;
4. compact face separation gives positive total mass in every shifted window;
5. total mass diverges along the coherent run;
6. bounded Flesch drift forces every opponent's charged mass to diverge;
7. product/sum accounting gives qualitative deleted-player survival decay;
8. each coarse stage with `p_t < 1` admits a finite adaptive subdivision that
   preserves its survival; and
9. the adaptive nonperiodic compiler gives a uniform-equilibrium payoff.

Thus every point of the displayed terminal-free greatest family is a uniform-
equilibrium payoff.  This is a genuine positive theorem on the stated stratum;
the remaining limitation is production of such a component for an arbitrary
quitting game, not a missing local-equilibrium adapter inside the component.

## 1. Convexification and executable segments

For a general continuation set `E`, the formulas

```text
exists p in [0,1], v in E, w = p R_i + (1-p) v
```

and

```text
co ({R_i} union E)
```

are not equivalent: the first is a union of segments from `R_i`, while the
second can mix several continuation points.  The Lean API therefore keeps the
notions separate:

- `quittingEssentialAPSPrefix` is the literal convex-hull prefix;
- `quittingSegmentEssentialAPSPrefix` selects one continuation;
- `quittingProperEssentialAPSPrefix` additionally requires `p` in `(0,1)`;
- `quittingSegmentEssentialAPSPrefix_subset` embeds executable segments into
  the algebraic prefix.

Every full owner-step image is convex, even if the raw successor union is not.
Consequently the greatest restricted APS family has convex fibers inside
convex carriers.  On a convex live successor fiber, the full prefix is a
single-root convex join and hence has a one-continuation representation.

## 2. Unique live successors and compactness

A displayed successor `s(i)` is *unique live* when every other exact Flesch
successor has an empty greatest-family fiber:

```text
j != s(i) and FleschSuccessor i j  ==>  G_j = empty.
```

This is weaker than graph-theoretic uniqueness.  It still implies

```text
quittingEssentialAPSSuccessorSet reward G i = G_(s(i)).
```

The local total trichotomy is therefore:

- the current point is terminal;
- it propagates unchanged to `G_(s(i))` with mass zero; or
- it has a proper segment into `G_(s(i))` with mass in `(0,1)`.

Unique-live compactness follows by the same closure bootstrap as in the
single-successor case.  If `G_j` is empty, then its closure is empty, so the
unique-live identity survives coordinatewise closure.  The restricted image
of the closed family is closed; hence the closure of `G` is subinvariant.
Maximality gives `closure G <= G`, so every greatest fiber is closed and,
inside a compact carrier, compact.

The capstone is

```text
isCompact_quittingEssentialAPSGreatestFamily_of_compact_convex_unique_live
```

in `QuittingEssentialAPSCompactFixedPointLive.lean`.

## 3. Coherent executable runs

`IsQuittingEssentialAPSFiniteRun` records a concrete finite sequence of values
and masses.  Each value lies in the appropriate greatest-family fiber, each
mass lies in `[0,1)`, and each edge satisfies

```text
v_t = p_t R_(i_t) + (1-p_t) v_(t+1).
```

`exists_quittingEssentialAPSFiniteRun_or_terminal_of_unique_live` constructs a
run to any requested finite horizon unless a terminal point is reached first.

On the terminal-free branch the nonterminal continuation relation is serial.
Classical choice followed by dependent recursion therefore gives one coherent
infinite sequence rather than unrelated runs at different horizons:

```text
exists_quittingEssentialAPSInfiniteRun_of_unique_live_of_terminalFree
```

Every vertex remains in the greatest family, so it is active at its current
owner.

## 4. From total mass to opponent mass

Let the finite player set be `I`, let `s : I -> I` be the displayed successor
map, and suppose the owner path follows it:

```text
i_(t+1) = s(i_t).
```

Let an executable active path satisfy

```text
v_t = p_t R_(i_t) + (1-p_t) v_(t+1),
0 <= p_t <= 1,
v_t(i_t) = R_(i_t)(i_t).
```

Assume all path values and singleton rewards are bounded in absolute value by
`B`.  A Flesch edge has the strict forward cross-gain

```text
R_i(s(i)) - R_(s(i))(s(i)) > 0.
```

Finiteness gives one common lower bound `gamma > 0` for all players.

Fix a player `a` and write `b = s(a)`.  On an edge owned by `a`, activity at the
next vertex gives `v_(t+1)(b) = R_b(b)`.  Taking coordinate `b` in the arc
equation yields

```text
v_t(b) - v_(t+1)(b)
  = p_t (R_a(b) - R_b(b))
  >= gamma p_t.
```

On an edge not owned by `a`, boundedness gives the compensating lower bound

```text
v_t(b) - v_(t+1)(b) >= -2 B p_t.
```

For a finite interval `J`, let

```text
M_a(J)  = sum of p_t over edges owned by a,
M_-a(J) = sum of p_t over edges owned by players other than a,
M(J)    = M_a(J) + M_-a(J).
```

Summing and telescoping gives

```text
gamma M_a(J) <= 2 B + 2 B M_-a(J).
```

Eliminating `M_a(J)` gives the decisive simultaneous lower bound

```text
M_-a(J) >= (gamma M(J) - 2 B) / (gamma + 2 B).
```

Thus total mass cannot remain concentrated on one owner for arbitrarily long:
the successor-coordinate drift created by that owner's mass would exceed the
bounded range available to the path.

The Lean statements are

```text
gap_mul_quittingEssentialAPSOwnerWindowMass_le_bound_add_opponentMass

div_le_quittingEssentialAPSOpponentWindowMass_of_windowMass_le
```

in `QuittingEssentialAPSOpponentMass.lean`.

## 5. One positive mass constant at every shift

Compact active-face separation gives a positive constant `nu_i` for a window
starting in owner fiber `i`.  There are finitely many owners, so the minimum of
the positive local constants is positive.  The orbit identity

```text
owner(start + t) = successorOrbit successor (owner start) t
```

then transports the local theorem to every shift of one infinite path:

```text
nu <= sum_{t=start}^{start+horizon-1} p_t
```

for all `start`.  The theorem is

```text
exists_uniform_quittingEssentialAPSWindowMass_along_successor_path_unique_live
```

in `QuittingEssentialAPSPathContraction.lean`.

After concatenating `q` such windows, total mass is at least `q * nu`.  Choose
`q` so that

```text
gamma * q * nu > 2 B.
```

Then every player receives a common positive opponent-mass floor

```text
eta = (gamma * q * nu - 2 B) / (gamma + 2 B) > 0
```

on every aligned block of length `K = q * horizon`.

## 6. Opponent survival contracts

At the singleton root owned by `i_t`, deleting player `a` leaves continue mass

```text
1       if i_t = a,
1-p_t   if i_t != a.
```

For hazards `q_t` in `[0,1]`, the elementary product-sum inequality

```text
(product_t (1-q_t)) * (1 + sum_t q_t) <= 1
```

implies

```text
product_t (1-q_t) <= 1 / (1 + eta)
```

whenever `sum_t q_t >= eta`.  Hence

```text
rho = 1 / (1 + eta)
```

satisfies `0 <= rho < 1`, and every aligned `K`-block contracts every player's
opponent-survival clock by at most `rho`.

The principal theorems are

```text
isQuittingOpponentBlockContraction_singletonRoots_of_windowMass

exists_quittingEssentialAPSPath_opponentBlockContraction_unique_live
```

in `QuittingEssentialAPSOpponentContraction.lean` and
`QuittingEssentialAPSPathContraction.lean`.

## 7. Infinite contracted APS path

The final composition is

```text
exists_quittingEssentialAPSInfiniteRun_with_opponentBlockContraction_unique_live
```

in `QuittingEssentialAPSInfiniteContraction.lean`.

Under compact convex carriers, a finite unique-live successor map, finite-window
face avoidance, terminal-freeness, and uniform boundedness, every initial
point in the greatest family admits:

- a coherent infinite executable APS run;
- masses in `[0,1)` and exact singleton-arc equations;
- singleton product roots satisfying exact Bellman policy evaluation; and
- constants `K > 0`, `eta > 0`, and `rho in [0,1)` satisfying
  `IsQuittingOpponentBlockContraction`.

This fixed-block route is a quantitative source of the survival hypothesis.
The adaptive compiler below only needs qualitative survival decay and does not
use `K`, `eta`, or `rho`.

## 8. Qualitative survival decay and adaptive subdivision

Shifted-window mass gives divergent total mass. Strict Flesch cross-gains and
bounded drift force every opponent's charged mass to diverge; product/sum
accounting then makes each deleted-player survival clock tend to zero. At each
coarse stage with `p_t < 1`, a finite stage-dependent subdivision preserves
coarse survival exactly and makes the local Quit error sufficiently small.
The adaptive mesh, exact Continue transport, and nonperiodic Snell
supersolution give the payoff theorem without a common hazard ceiling or fixed
block contraction. The `p_t = 1` full-jump case remains outside this step.
Terminal-freeness, functional unique-live execution, and finite-window
face-avoidance remain structural hypotheses.

The source-agnostic public compiler is

```text
isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath_of_initialSurvival
```

and the component capstone is

```text
quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live_adaptiveMesh
```

in `QuittingInfiniteVariableSingletonMeshCertificate.lean` and
`QuittingEssentialAPSAdaptiveMeshUniformPayoff.lean`, respectively.

### Optional common hazard ceiling

The older fixed-mesh specialization obtains a uniform ceiling from compact
terminal-freeness as follows.

For owner `i`, let

```text
gap_i(v) = sum_j |v_j - R_i(j)|.
```

The gap is continuous and vanishes exactly at the singleton endpoint `R_i`.
Greatest-family membership supplies viability, so terminal-freeness excludes
that zero. Compactness of each greatest fiber and finiteness of the player set
therefore give one `delta > 0` with

```text
delta <= gap_i(v)
```

at every point in every relevant fiber. Along an arc

```text
v = p R_i + (1-p) w
```

whose endpoints are bounded by `B`, coordinatewise estimation gives

```text
gap_i(v) <= (1-p) * |I| * 2B.
```

Consequently all coarse hazards satisfy `p <= pStar` for one `pStar < 1`.
This uniform separation is the compactness input needed to choose one finite
subdivision width at each requested accuracy.

The carrier-level theorem is

```text
exists_uniform_quittingEssentialAPSHazardCeiling_unique_live
```

in `QuittingEssentialAPSUniformHazard.lean`.

## 9. Quantitative fixed-mesh specializations

The following ceiling and fixed-subdivision route remains a stronger
quantitative specialization, not a capstone requirement for the adaptive
route.

For a positive integer `m`, replace a coarse hazard `p` by the constant
micro-hazard

```text
q = 1 - (1-p)^(1/m).
```

The `m` microstage Continue probabilities multiply exactly to `1-p`, and the
interpolated values close exactly at the next coarse boundary.  Because
`p <= pStar < 1`, one common `m` makes `D*q` smaller than any prescribed
positive error, uniformly over the entire nonperiodic path.  Full microblocks
preserve deleted-player survival exactly, so a coarse `K`-block contraction
becomes a micro `K*m`-block contraction with the same factor `rho`.

At a singleton microstage, viability and the collision-surplus bound give

```text
immediate Quit value <= prescribed value + D*q,
```

while prescribed Continue and policy evaluation remain exact. Adding the same
error to every continuation value is therefore a global Snell supersolution:
Continue transports only `c*error <= error`. No stagewise error sum appears.
Opponent-survival decay removes the terminal comparison term, yielding
terminal approximate Nash play and exact delivery of the initial path value.
Accuracy-indexed meshes then give a uniform-equilibrium payoff.

The source-agnostic capstone is

```text
isUniformEquilibriumPayoff_of_singletonFlow_uniformHazard
```

in `QuittingInfiniteSingletonMeshCertificate.lean`. It assumes only a bounded
viable singleton-flow path, a common hazard ceiling below one, a collision-
surplus bound, and opponent block contraction. The essential-APS specialization
is

```text
quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live
```

in `QuittingEssentialAPSUniformPayoff.lean`.

## Module map

1. `QuittingFleschSuccessor.lean`: exact asymmetric successor graph.
2. `QuittingEssentialAPS.lean`: algebraic, segment, and proper APS prefixes.
3. `QuittingEssentialAPSFixedPoint.lean`: greatest restricted fixed family.
4. `QuittingEssentialAPSConvexProgress.lean`: convex join and proper progress.
5. `QuittingEssentialAPSConvexFixedPoint.lean`: convex greatest fibers and
   unique-live local progress.
6. `QuittingEssentialAPSCircuitProgress.lean` and
   `QuittingEssentialAPSCircuitProgressTotal.lean`: zero-mass propagation and
   active-face exclusion.
7. `QuittingEssentialAPSCompactFixedPoint.lean` and
   `QuittingEssentialAPSCompactFixedPointLive.lean`: closure bootstrap and
   compact greatest fibers.
8. `QuittingEssentialAPSFiniteRun.lean`: finite executable runs.
9. `QuittingEssentialAPSInfiniteRun.lean`: coherent terminal-free infinite
   runs.
10. `QuittingEssentialAPSUniformWindowMass.lean` and
    `QuittingEssentialAPSUniformWindowMassLive.lean`: compact separation and
    positive total mass.
11. `QuittingEssentialAPSOpponentMass.lean`: successor-coordinate charging.
12. `QuittingEssentialAPSOpponentContraction.lean`: product-sum contraction.
13. `QuittingEssentialAPSPathContraction.lean`: shifted-window and block
    composition.
14. `QuittingEssentialAPSInfiniteContraction.lean`: infinite contracted path.
15. `QuittingEssentialAPSRegression.lean`: zero-mass self-loop regression.
16. `QuittingEssentialAPSCycle.lean`: compilation of a supplied finite proper
    cycle.
17. `QuittingInfinitePathSupersolution.lean`: source-agnostic nonperiodic
    quit-error comparison and accuracy-indexed compiler.
18. `QuittingEssentialAPSUniformHazard.lean`: compact terminal-free separation
    and the uniform coarse-hazard ceiling.
19. `QuittingInfiniteSingletonMesh.lean`: fixed logarithmic subdivision and
    exact interpolated Bellman transport.
20. `QuittingInfiniteSingletonMeshSurvival.lean`: exact survival transport and
    preservation of opponent block contraction.
21. `QuittingInfiniteSingletonMeshCertificate.lean`: local collision control,
    nonperiodic certificates, and the generic singleton-flow payoff theorem.
22. `QuittingEssentialAPSUniformPayoff.lean`: essential-APS uniform-payoff
    capstone.
23. `QuittingInfiniteVariableSingletonMesh.lean`,
    `QuittingInfiniteVariableSingletonMeshSurvival.lean`, and
    `QuittingInfiniteVariableSingletonMeshCertificate.lean`: adaptive
    finite per-coarse-stage subdivision, survival transport, and certificates.
24. `QuittingEssentialAPSAdaptiveMeshUniformPayoff.lean`: adaptive capstone.

`QuittingEssentialAPSAll.lean` exports the complete layer.

## Scope boundary

The payoff theorem is conditional on the compact functional unique-live,
terminal-free stratum, its finite-window active-face avoidance, and the stated
bounds. Those hypotheses are not proved for every quitting game, and the
formalization does not identify the greatest family with all uniform-
equilibrium payoffs. Within the stated component, however, no local root-Nash
assumption remains: adaptive finite subdivision supplies the vanishing Quit
error and the nonperiodic supersolution controls every history-dependent
unilateral deviation.
