# D78: exact-law Nash bridges keep direct preference-generic proofs

- **Status:** adopted for the two measured bridge leaves; broader abstractions remain open.
- **Date:** 2026-11-11
- **Experiment:** EXP-173

## Question and alternatives

Can unnecessary expected utility be removed from the behavioral/mixed Kuhn
and Bayesian policy/plan Nash bridges using the existing semantic owners?
Compare direct bridge-local use of `isNash_iff` with `IsNash.of_coverage` on
identical generalized statements. A further law-coverage theorem or certificate
is considered only if these implementations expose a missing reusable operation.

## Evidence and choice

Both alternatives compile. Kuhn needs the existing honest and unilateral
realization laws; Bayesian transfer needs its play law, the plan/update law,
and pullback of preferences along `some`. The strategy conversions supply
coverage, without a deviation bijection. Neither alternative changes any law,
deviation scheme, equilibrium definition, probability carrier, or trust boundary.

Choose direct proofs: the two Kuhn proofs save four nonblank source lines and
the Bayesian equivalence saves five against the coverage implementation, with
zero new shared infrastructure in either case. The expected Bayesian theorem
is derived from the generic theorem using `euPreference_map`, retaining both
expectation-definedness guards. Kuhn's existing transfer theorem names now take
a `WeakPreference` instead of utility; numerical callers pass `euPreference u`.

Three alternating serialized whole-module process runs, with identical imports
and Lean options, gave these median seconds:

| Client | Direct | Existing coverage |
| --- | ---: | ---: |
| Kuhn | 19.125 | 17.617 |
| Bayesian | 11.632 | 11.575 |

These import-inclusive measurements do not isolate theorem elaboration and do
not establish a general performance ranking. No new record is admitted, and
there is no cold construction cost to amortize. Exact reproduction is
`python scripts/compare_abstraction_bridges.py`; its sources, per-run logs and
`timings.json` live under ignored `.codex/scratch/exp173/`. The script reconstructs
both variants from the final sources. Toolchain: Lean 4.35.0, Mathlib v4.35.0.

## Admission and limits

The Kuhn fixture transports a relation accepting only the incumbent law and
proves it cannot equal expected utility for any utility on this finite-history
game. It also retains genuine mixed deviations, a nondeviator-sensitive law,
and the numerical round trip. The Bayesian fixtures retain two-player and
private-type numerical consumers with the original signatures. Existing
`Tests.ApproximateEquilibriumTransport` and `Tests.MixtureSimulation` preserve
the nearby failures of missing same-player reflection and total coverage.

This supports preference generalization and narrows the survey hypothesis that
one new generic bridge lemma should replace every bridge proof. The existing
coverage API is valid; mandatory existential/implication packaging does not pay
for these exact-law leaves. D5, D7, D8 and D60 remain the defaults. No result
here licenses CE/CCE transfer from Nash coverage, binary-to-countable mixture
closure, changing weak to strict equilibrium under partial preferences, or a
replacement of the local law-linear deviation scheme. Later experiment items
remain gated in `AbstractionRedesignExperiment.md`.
