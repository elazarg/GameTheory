# Essential APS: coherent execution and opponent contraction

This module family formalizes the certificate-facing part of the essential APS
approach of Ashkenazi-Golan, Krasikov, Rainer, and Solan, *The APS approach for
undiscounted quitting games* (International Journal of Game Theory 55:19,
2026).

The result is still conditional: it concerns a compact functional
unique-live-successor singleton-flow stratum.  Within that stratum, the current
branch now closes the following chain:

1. algebraic convexification reduces to a one-continuation executable segment;
2. zero-mass propagation is separated from genuine positive-mass progress;
3. local progress choices compose into finite runs and, on the terminal-free
   branch, one coherent infinite run;
4. compact face separation gives positive total mass in every shifted window;
5. strict Flesch cross-gains convert total mass into mass contributed by the
   opponents of every player;
6. opponent mass yields a uniform block-contraction factor for the singleton
   roots implementing the path.

The remaining input for the existing exact nonperiodic equilibrium compiler is
local root-Nash control.  Exact Bellman transport and opponent-survival decay
are no longer missing.

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

The existing `QuittingInfinitePathCompiler` can therefore select the supplied
value and control the survival tail once local root-Nash inequalities are
provided.

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

`QuittingEssentialAPSAll.lean` exports the complete layer.

## Current frontier

The opponent-specific contraction gap identified in the review is closed for
the compact functional unique-live terminal-free stratum.  What remains is a
different game-theoretic step: produce exact or asymptotically vanishing local
root-deviation error along the nonperiodic APS path.  The existing periodic
mesh compiler supplies such control for a supplied cycle; the corresponding
nonperiodic adapter is not proved here.  Nor does this branch identify the
functional unique-live stratum with every quitting game.
