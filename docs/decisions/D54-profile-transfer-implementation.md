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

`Core.Form.recordProfile` records the paired outcome, while `Core.Response`
owns weak-undominated strategies and profiles. The mechanism facade needs the
paired outcome only in its utility definition. Consumers use canonical
`WeaklyDominates` without paired-outcome projections, profile updates, or
visible equality transport. Each implementation predicate has one owner.

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
