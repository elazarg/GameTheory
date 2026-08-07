# Uniform payoffs from face circulations

`QuittingFaceCirculationAll.lean` is the public umbrella for the production
certificate/orbit/path chain, its concrete payoff examples, and the sharp
two-coordinate boundary analyses. Downstream proofs that need only the generic
compiler should import `MultiOwnerFaceCirculationCompactPath.lean` directly.

This note records the production face-circulation producer class for finite
quitting games. It is a genuine existence class, not an arbitrary-game
producer: the input is a supplied, finite `FaceCirculationCertificate` whose
phase ratios have one common ceiling strictly below `1`, and whose floor is at
least the formal `quittingPunishmentValue` coordinatewise.

## Certificate and hypotheses

For a quitting weight `r`, a certificate of phase length `L` supplies finite
phase vertices, phase mixing weights, ratios, affine step identities, floor
bounds, and owner pinning. The compiler requires:

- a bound `|r S i| <= M` for every terminal coalition and player;
- a bound on every phase support size;
- `C.ratio l <= a < 1` at every phase; and
- `quittingPunishmentValue (rewardOfWeight r) i <= floor i` for every player.

The natural floor is
`max (r {i} i) (quittingPunishmentValue (rewardOfWeight r) i)`.  The final
theorem is nevertheless stated with an arbitrary supplied floor satisfying the
displayed punishment inequality, so it does not silently identify a certificate
floor with a min--max construction.

## The theorem chain

1. A multi-owner certificate is discretized into a forward real-hazard orbit.
   Inside each phase a balanced owner word realizes the phase mixture with
   uniformly bounded discrepancy.  The resulting rows satisfy exact Bellman
   transport, support-local approximate Nash inequalities, the floor bound,
   and a positive absorption lower bound.  The same discretization reaches
   every requested finite quit-mass target.
2. Each finite forward prefix is reversed.  The reversed prefixes obey the
   chronological root equations.  Compact finite-prefix extraction selects an
   infinite chronological support path.  The per-step absorption lower bound
   makes total absorption nonsummable and joint all-continue survival
   geometric.
3. Joint-survival selection identifies the selected bounded Bellman values
   with the actual terminal tails of that infinite root path.  This selection
   is existential: the produced uniform-equilibrium payoff is not formally
   identified with a named vertex of the input circulation.
4. The floor bound and the punishment inequality give approximate individual
   rationality of every selected tail.  The support-witness path compiler then
   turns the support-rational divergent path, at every accuracy, into an
   existential uniform-equilibrium payoff.

The terminal theorem is
`quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation`; its
singleton-support specialization is
`quittingGame_exists_uniformEquilibriumPayoff_of_singletonCirculation`.

The discrete-hazard stopping law and quitting adapters, together with the
canonical target-anchored tail interface, are the reusable infrastructure used
by this path consumer. The same incorporation wave also landed a parametric
residue payoff theorem and quitting reward-limit closure; those are independent
payoff results, not hidden hypotheses of the circulation chain.

## Concrete corollaries

Two explicit singleton certificates have been compiled all the way to
uniform-equilibrium payoff existence:

- the scaled cyclic quitting weight; and
- the repaired four-player cyclic stress weight at `(x, lambda) = (2, 1)`.

For both, the formal punishment value is proved below the certificate floor.
These are concrete members of the circulation producer class, not evidence
that every cyclic or every four-player quitting game has such a certificate.

## Phase occupation duality: adjacent, not a producer

`Math/Probability/PhaseOccupationDuality.lean` compiles a finite periodic
phase-occupation problem to a standard-form LP.  Given a phase occupation, it
proves the exact semantic feasibility equivalence, LP attainment, a decoded
phase-bias dual certificate, and equality of the optimal occupation reward and
minimal bias slack.

Its strong-duality theorem is conditional only on existence of a phase
occupation.  It does **not** prove that a phase occupation exists, and it does
not provide a strategic circulation or any other producer for a quitting
game.  It is therefore an optimization/verification interface, not an
extension of the circulation existence theorem.

## Path-consistency fence for future flow synthesis

The landed face-circulation theorem is already path-producing: its finite
certificate is discretized to one forward orbit, reversed, and compactly
selected into one chronological path.  The following warning does not weaken
that theorem.  It constrains a possible future attempt to *produce* such data
from a global occupation LP on a finite atlas of legal transitions.

A global zero-defect circulation may cancel signed defects across recurrent
strongly connected components that no single legal path can visit recurrently.
For example, take two isolated vertices, each carrying only its own loop.  Give
both loops charge `1`, and signed defects `+1` and `-1`.  The global circulation
placing mass `1/2` on each loop has zero average defect and unit charge, but
every legal infinite path stays on one loop and accumulates defect with one
sign.  The global feasible point is not a bounded-discrepancy path.

The corresponding single global dual can also fail: the vertex-potential terms
vanish on both loops, so a strict inequality would require both
`lambda >= c` and `-lambda >= c` for `c > 0`.

The correct prospective positive alternative is therefore componentwise:
choose one reachable recurrent SCC `C` and a nonnegative circulation supported
on its internal edges satisfying

```text
B_C * mu = 0,
sum_e mu_e * signedDefect_e = 0,
sum_e mu_e * charge_e = 1.
```

Path-realizable recurrent occupations form a finite union of component
circulation polytopes, not one global convex polytope.  If no reachable
component works, the natural Farkas output is one separator per reachable
recurrent component; one common global separator need not exist.

Even inside one SCC, a circulation supported on several cycles is not yet one
strategic word.  Connector paths, signed seam accumulation, and their charge
cost must be controlled by a separate realization theorem.  Strong
connectivity guarantees reachability, not negligible strategic error.

## Boundaries

The circulation theorem does not solve arbitrary quitting games.  It neither
constructs a `FaceCirculationCertificate` for an arbitrary weight nor removes
the ratio, boundedness, support-size, or punishment-floor hypotheses.  Its
compact reversal selects an existential payoff only.  The remaining
arbitrary-game producer problem is open.

Equal-atom constructions are not production mathematics in this repository.
They may be considered as a next intake target, but they are not a corollary,
an alternative producer, or a claimed extension of this theorem chain.
