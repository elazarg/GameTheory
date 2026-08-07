# A path-consistent conjecture-directed spine

**Status:** research architecture and dependency map, not a theorem and not
live project-control truth.  
**Scope:** a proposed route from arbitrary finite quitting reward data to either
terminal approximate equilibria at every accuracy or the exact fixed-gap
nonexistence certificate.

Production Lean decides theorem truth. [`FRONTIER.md`](FRONTIER.md) states the
current mathematical boundary, [`PIPELINE.md`](PIPELINE.md) owns live
priorities, and [`SystematicApproach.md`](SystematicApproach.md) gives the stable
research guidance. This page proposes one falsifiable mathematical spine joining
several currently separate producer obligations.

The repository's strong point is the back end: many supplied strategic objects
already compile to terminal approximate equilibria and uniform payoffs. The weak
point is the front end that must construct such an object from arbitrary reward
data, or prove nonexistence against unrestricted behavioral deviations.

The intended composition is:

```text
principal support / proper subgame
        |
        v
quantitative glue-or-enlarge
        |
        v
finite strategically legal support atlas
        |
        v
reachable recurrent-component alternative
        |
        +---- path-consistent charged flow
        |              |
        |              v
        |      physical path/lasso realization
        |              |
        |              v
        |      existing terminal compiler
        |
        +---- componentwise dual separators
                       |
                       v
             support or rank descent,
             target retargeting,
             proper-face induction,
             or fixed-gap nonexistence
```

This is a research target. None of the arrows below is silently counted as
proved.

## Stage A — principal-support preprocessing

Start from a normalized reward table, an accepted target packet, or another
finite-dimensional local representation. The stage should return one of:

1. a full-support local packet with a proved strategic target gate;
2. a proper player face or subgame, together with the data needed to reinsert
   excluded players; or
3. a secondary ray, target rejection, or separating obstruction whose strategic
   meaning is explicit.

Normalized singleton LCPs, complementary pivoting, semialgebraic support cells,
and projective packets are possible implementations. Algebraic complementarity
alone is not enough: the output must already identify a next strategic consumer
or a concrete failed inequality.

## Stage B — glue or enlarge

Given a construction on a proper player set, either glue it into the full game
or identify an entering outsider.

A promising quantitative adapter is the following candidate statement. Suppose
an outsider's continuation value at every suffix is at least its solo payoff
minus `eta`, terminal rewards are bounded by `M`, and the conditional
probability of an insider absorption at each stage is at most `delta`. Then the
outsider's gain from each pure quit time should be at most

```text
eta + 2 * M * delta.
```

The existing quit-time/Never extremality theorem could then lift this bound to
arbitrary behavioral deviations. This estimate is not landed until it is proved
in repository semantics and connected to an actual subgame producer.

Failure of gluing should return:

- the first excluded player;
- the relevant suffix or terminal atom;
- the solo, join, or continuation inequality that fails; and
- the support face into which the player should enter.

That payload is the input to Stage C.

## Stage C — finite strategically legal support atlas

Construct a finite or finitely presented directed atlas of legal local
transitions. Each edge must retain the data needed downstream:

- active quitting face or ordered activity pattern;
- continuation values and target information;
- local owner optimality and outsider inequalities;
- nonnegative absorption charge;
- signed Bellman seam or exact transport data;
- punishment or individual-rationality floors; and
- physical-realization provenance for analytic edges.

Every local boundary should already be typed as one of:

1. terminal or Never;
2. sure exit satisfying the exact instant-punishment gate;
3. proper subgame;
4. support enlargement or deletion;
5. target rejection and retargeting;
6. positive-real-arc infeasibility;
7. candidate strategic separator; or
8. a split into recurrent components that cannot be mixed by one legal path.

Lexicographic complementary pivoting, exact multi-owner root equations,
CAD/semialgebraic sign cells, and KKMS/Scarf balanced-support arguments are
candidate proof methods. Their value is whether they construct this atlas or a
typed obstruction, not whether they create another stand-alone formalism.

## Stage D — reachable recurrent component, then flow or separator

This stage must be **path-consistent**. A global circulation polytope is too
large because it convexifies over recurrent components that one infinite path
cannot visit recurrently.

Fix the atlas entry data and decompose the reachable directed graph into
strongly connected components. Since the condensation graph is acyclic, every
infinite legal path has its recurrent edge set inside one reachable SCC after a
finite transient prefix.

For each reachable recurrent SCC `C`, attach to every internal edge `e`:

- a signed defect vector `g_e`; and
- a nonnegative absorption charge `q_e`.

The positive target is the finite disjunction

```text
there exists a reachable SCC C and mu >= 0 supported on internal edges of C:
    B_C * mu = 0
    sum_e mu_e * g_e = 0
    sum_e mu_e * q_e = 1.
```

Path-realizable recurrent occupation measures therefore form a **finite union
of component circulation polytopes**, not one global convex polytope.

### Regression: incompatible convex cancellation

Consider two vertices `a` and `b`, each with only its own loop. Give both loops
charge `1`, and defects `+1` and `-1`. The global mixture placing mass `1/2` on
each loop has zero average defect and unit charge, but every legal path remains
in one component and accumulates defect with one sign. There is no bounded-
discrepancy path.

There is also no single global strict dual of the naive form: on the two loops,
the vertex-potential terms vanish and the inequalities would require both
`lambda >= c` and `-lambda >= c` for `c > 0`.

This example is a permanent boundary condition on Stage D. A feasible global
convex combination is not a positive output unless one common-randomization
theorem explicitly allows mixing entire recurrent components and proves that
such mixing preserves every strategic requirement.

### Componentwise dual alternative

For one fixed component `C`, rational Farkas duality gives the appropriate
alternative between the component circulation above and a strict inequality

```text
h_C(head e) - h_C(tail e) + lambda_C · g_e >= c_C * q_e
```

for every internal edge of `C`, with `c_C > 0`.

If no reachable component admits a positive circulation, the natural negative
output is **one separator per reachable recurrent component**. A single global
`(h, lambda, c)` need not exist.

Summing a component separator along a path segment inside `C` shows that a path
with bounded signed cumulative defect has bounded charge while it remains in
that component. Since the condensation graph permits only finitely many strict
component changes, the transient prefixes can be handled separately. Turning
these componentwise barriers into a strategic conclusion remains a decoder
obligation.

Acceptable decoders include:

- support or rank descent;
- a proper-face theorem;
- a target-rejection pivot;
- an individual-rationality or punishment boundary; or
- the fixed positive terminal exploitability gap from
  `UniformNonexistenceCertificate.lean`.

Finite phase-occupation duality is useful infrastructure inside one component.
It does not establish component nonemptiness, path realization, or strategic
decoding.

## Stage E — realize one component as one legal path

A component circulation is still not itself a strategy. Stage E must convert it
into a single chronological legal word or path and control every extra connector
and physical-lifting error.

### E1. Exact bounded forward-orbit regime

When a bounded exact forward Bellman orbit has arbitrarily large finite-prefix
charge, compact charged return may produce a close block with a fixed positive
absorption denominator. Reversing one finite block then creates one controlled
closing seam. This route is useful only at the exact scope actually proved by
the corresponding orbit theorem.

### E2. Approximate or multi-seam regime

With several local seams, the relevant error is signed survival-weighted
monodromy, uniformly over cyclic entry phase. Bounded cyclic discrepancy plus
Abel summation is a plausible adapter, but legal ordering and component
connectors must be priced explicitly.

A circulation supported on several cycles inside one SCC may require connector
paths. Strong connectivity makes connection possible, but the connectors are
not free: a valid theorem must make their defect and charge negligible relative
to long repetitions, or use an exact Eulerian support with the required
connectivity.

### E3. Physical realization

Formal or Zariski tangent feasibility is insufficient. Atlas edges originating
from singular analytic data require a positive real arc theorem, for example by
regular-chart lifting, semialgebraic stratification and curve selection, or a
signed real-Puiseux argument. Failure should return an infeasible sign type or a
boundary pivot, not merely “the tangent did not lift.”

### E4. Separator regime

Componentwise dual separators must be decoded rather than recorded as LP
infeasibility. The decoder must produce a Stage-C boundary output or the exact
fixed-gap negative semantic certificate.

## Stage F — generic-to-all closure

The landed fixed-skeleton reward-closure theorem is a strong final adapter: a
dense family of solved reward tables yields all reward tables on that skeleton.

It does not permit replacing the hard global theorem by local genericity. Before
invoking closure, the generic program must establish a global statement such as:

- regular complementarity components have only typed endpoints or
  path-consistent charged recurrent components;
- every regular physical chart admits the required real arc lifting; and
- every endpoint and recurrent component is consumed by Stages B through E.

Only after an open dense solved set is proved should reward closure remove
singular degeneracies.

## Dependency order for new mathematics

This is a dependency order, not a replacement for `PIPELINE.md`.

1. **Quantitative proper-subgame gluing.** Prove the behavioral adapter or
   extract the entering outsider.
2. **Explicit support enlargement.** Package the two-owner and smallest
   multi-owner pivot alternatives, reusing landed sure-exit and punishment
   results.
3. **Legal support atlas.** Give every boundary a strategic meaning before
   invoking global topology or flow.
4. **SCC-consistent flow alternative.** Work component by component; reject
   global convex cancellation across incompatible recurrent classes.
5. **Single-path realization.** Price connectors, signed seams, and physical
   lifting inside the chosen component.
6. **Dual decoding.** Turn component barriers into support descent, retargeting,
   proper-face induction, or the fixed all-behavior gap.
7. **Generic-to-all closure.** Use reward closure only after the global generic
   atlas theorem.

An unrestricted negative search should run in parallel using the same atlas and
component separators. A successful local barrier must eventually be translated
into the fixed terminal exploitability gap; failure of one bounded grammar is
not enough.

## Directions receiving reduced conjecture credit

The following remain useful as infrastructure or diagnostics, but do not count
as front-end progress without a producer or decoder theorem:

- another compiler for supplied data;
- repetition of a support or chart label without coefficient and charge
  control;
- target-preserving packet extraction without executable continuation;
- scalar mass-clock compactification without chronological strategic fibres;
- phase-occupation duality without path-consistent nonemptiness;
- a global circulation obtained only by mixing recurrent SCCs;
- an exact-cycle completeness conjecture; and
- exclusion of one stationary, periodic, APS, bounded-controller, or marked
  path grammar.

## Nonclaims

This page does not prove:

- principal-support preprocessing;
- quantitative subgame gluing;
- existence of the finite legal atlas;
- an SCC with a charged zero-defect circulation;
- componentwise strategic decoding of the dual;
- single-path or real-arc realization;
- density of solved generic reward tables; or
- the quitting-game conjecture.

It states how those obligations could compose with the existing back end and
records the path-consistency condition that any flow-based spine must satisfy.
