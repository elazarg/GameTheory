# D54: Profile-transfer implementation uses canonical weak dominance

Decision: expose one transparent profile-recording transformation and a
mechanism-domain weak-undominance implementation predicate. Do not restore the
universal `KernelGame`, parameterize implementation by arbitrary solution-set
functions, or introduce a second response semantics.

Experiment ID: [EXP-097](../ExperimentLog.md).

## Competing designs

1. Record the chosen profile alongside the existing stochastic outcome, add
   transfers in derived utility, and reuse canonical weak dominance.
2. Restrict implementation theory to deterministic NFG syntax.
3. Restore v1's bundled `KernelGame` and its parallel payoff/solution stack.
4. Define a higher-order implementation framework parameterized by any
   solution-set predicate.

The first design is adopted. The NFG restriction is unnecessarily narrow: the
profile-recording transformation works for every finite-law `GameForm` and
retains its original stochastic outcome law. The kernel hub violates the
accepted semantic ownership. The higher-order framework has only one validated
solution concept and would freeze a hierarchy before reuse is known.

## Representative slice and measurements

Two Boolean players initially prefer `false`. A nonnegative transfer of two
for choosing `true` makes the all-true profile uniquely weakly undominated and
implements it with exact surviving budget four. The same transfer implements a
non-singleton target cylinder by target monotonicity. Zero transfer leaves the
all-false profile weakly undominated and refutes both targets.

`Core.Form` adds a 20-line transparent `recordProfile` transformation and
`Core.Response` adds 10 lines for weak-undominated strategies and profiles.
The mechanism facade is 93 source lines / 75 nonblank; the stable hostile test
is 172 / 139. The facade mentions the paired outcome only in its utility
definition. The test has zero paired-outcome projections, `Profile.update`,
cast, `Eq.ndrec`, tactic `change`, or `Function.update` references. It consumes
the canonical `WeaklyDominates` relation in both positive and falsifying
proofs. Warm warning-clean elaboration of each changed owner and the test takes
about 10--11 seconds against the existing v2 artifacts.
The fast source audit also enforces exactly one definition of each graduated
weak-undominance and implementation predicate.

## Public boundary

- `GameForm.recordProfile` is the reusable utility-free transformation. It
  changes only the outcome carrier; strategy profiles remain definitionally
  unchanged.
- `UtilityGame.withProfileTransfer` adds the transfer and exposes one expected-
  utility calculation theorem. Recording a profile asserts no player
  observability.
- `IsWeaklyUndominated` and `IsWeaklyUndominatedProfile` belong to Core response
  theory.
- `UtilityGame.IsUndominatedImplementation` and
  `IsKUndominatedImplementation` live in opt-in Mechanism and state exactly
  which solution concept they use.

Mixed, correlated, informational, VCG, restricted-transfer, implementation-
price, and attainment theorems remain separate consumer-gated packages. Add
one only when a field-standard hostile slice reaches the canonical owner. A
second game, probability, response, or equilibrium truth is a disproof
condition, not an acceptable compatibility cost.
