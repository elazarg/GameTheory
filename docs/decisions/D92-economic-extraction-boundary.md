# D92: extract mathematical operations, preserve domain semantics

- **Status:** adopted extraction boundary; investigation closed at diminishing architectural returns.
- **Date:** 2026-11-11
- **Evidence:** EXP-173 through EXP-186, decisions D78 through D91; the
  dependency consolidation and ordinary measure-valued consumer check in
  `MathEconBuildingBlocks.md`.

## Decision

Stop expanding the architecture in the present investigation. Prefer small
operations and theorem-local hypotheses over a universal judgment ladder,
economic problem record, probability carrier, arena or certificate hierarchy.
The last three experiments resolved different questions without adding another
stable owner. This is diminishing architectural return, not a claim that the
field or external integration is complete.

The alternatives were a shared hierarchy organizing all problem data versus
explicit comparison, domain, feasibility, coverage, mixture and regularity
arguments. Existing native game and protocol types enforce operations such as
local law-linear deviations that arbitrary economic relations need not enforce.
The hostile consumers repeatedly distinguish those semantics. A single shared
problem record has not earned its construction or abstraction cost.

## Shared mathematics and domain owners

The five accepted independent mathematical owners are `Math.GuardedOptimality`,
`Math.FiniteChoice`, `Math.Scalarization`, `Math.ParametricOptimality` and
`Math.LinearBudget`. Their authored import closures contain only themselves;
external imports are Mathlib. They are candidates for a shared mathematics
component or Mathlib, subject to a fresh upstream API search and one canonical
owner. Do not create copied implementations or compatibility alias chains.

`Analysis.FeasibleChoiceFixedPoint` has only the parametric-optimality owner
as an authored dependency and explicitly adds the external fixed-point package.
Extract it separately from probability-free/order/topological mathematics.
Retain the current one-way Analysis boundary until an actual package extraction
changes ownership deliberately.

Existing relations and functions are the underlying building blocks. Ranking
laws stay explicit; an admissible incumbent, a feasible incumbent, and offered
deviations are different predicates. Exact-law coverage does not require
numerical utility, a bijection of strategies or a new transport record.
Preference representation, aggregation and approximation spend additional,
operation-specific hypotheses rather than occupying mandatory superclass levels.

Native profiles, information models, protocol execution, coalition membership,
joint contract acceptance, mechanisms and transfers retain their domain owners.
The MathEconLib reference already owns set-based institutional choice and
arbitrary-relation equilibrium problems. Its general measurable mixed games
also use probability measures. None of these facts requires replacing
GameTheory's ordinary PMF semantics or importing a universal economic hub.

## Boundaries established by the continuation

- **Dynamic comparison:** a total transitive law ranking can strictly favor
  both conditional actions yet reject their composition. Non-EU possibility
  comparisons preserve arbitrary supported weak mixtures but need not preserve
  strict comparisons or independence cancellation. Actual-prior comparison closure and whole-law admissibility
  remain separate. Chooser composition does not imply information-local
  policy realizability (EXP-184).
- **Observational representation:** an entire fixed-positive-price budget
  family can leave a strict ranking unidentified despite two globally consistent
  rationalizations. A further price budget distinguishes them. This is a
  richness requirement on observations, not failed rationalization existence
  or a missing demand record (EXP-185).
- **Institutional composition:** quota acceptance can satisfy substitutes/IRC
  and fail item WARP. Rational bundle choice can fail substitutes and the
  joint-to-singleton acceptance implication. Unique bundle selection, tied
  bundle alternatives and accepted contracts must not be conflated (EXP-186).
- **Evaluation conventions:** MathEconLib's integrable-deviation comparison
  contract is expressed by the existing guarded predicate with integrable
  deviations as its allowed set. Requiring every originally offered deviation
  to be integrable is stronger. A Bochner integral's totalized value does not
  establish admissibility. A defined extended expectation such as negative
  infinity is a different legitimate evaluation domain, not an undefined
  finite integral repaired by a carrier wrapper.

## Concrete extraction contract

Use the read-only MathEconLib reference revision
`58f602847d7f131994d32ca7a8cc1af35b7e2dbe` as a specific consumer, not an
assumption about future upstream APIs:

| Consumer | Shared operation | Obligation retained by the consumer |
| --- | --- | --- |
| `ChoiceFunction.ofBundleOrder` | finite greatest choice / existing `IsGreatest` | Represented feasible bundles, enumeration where needed, unique optimum or checked tie rule; substitutes separately, IRC through the owner's stated hypotheses (including its finite-scope consistency theorem). |
| `PairwiseStable.stable_of_substitutable` | contraction of joint acceptance | Contracts, involvement, blocking and stability; reuse the existing MathEconLib owner. |
| `StrategicGame.isMixedNash_iff` | guarded comparison with filtered deviations | Measurable strategies, product probability laws, integrable incumbent and each offered integrable deviation. |
| Equilibrium/demand existence | parametric maximizers and simultaneous feasible choice | Correct native menus, nonempty feasible fibers, objective geometry, and market clearing/uncapping. |

`Tests.MeasureGuardedOptimality.filtered_measure_optimal_iff` verifies the
per-player measure-valued contract directly for arbitrary measures. Its concrete
probability-measure control uses the existing countably supported gamble: the
nonintegrable gamble maximizes the raw totalized integral, is rejected as an
incumbent by the guarded predicate, and is omitted by integrable-deviation
filtering. This is a local consumer check, not a new architecture experiment.
MathEconLib's existing `MathEconLibTest/GameTheory/Integrability.lean` separately
contains diffuse uniform/reciprocal controls. Those external tests were
inspected, not built or imported into the GameTheory validation result.

No external integration or package move has occurred. Before extraction, select
the dependency owner and namespace, move rather than duplicate the mathematics,
and compile a named client in both repositories with their complete checks.
That is the next concrete delivery task; speculative new abstractions are not.

## When to reopen the investigation

Reopen only when a named consumer exposes an operation that these blocks cannot
express, forces duplicated semantics or excessive transport, or refutes a
stated closure/regularity assumption. Infinite-support or continuous-state
information dynamics, general endowment accounting, broader preference
representation and a complete matching compiler remain possible consumers,
not automatic new interfaces. Ordinary theorem recovery on the accepted API
continues under the delivery plan.

## Validation

Every collected experiment passes its full audit. The final ordinary consumer
build passes 3,144 strict jobs and source checks. Final complete validation is
recorded with the extraction checkpoint in `MathEconBuildingBlocks.md` before
collection. No timing comparison or universal minimality theorem is claimed.
On checkpoint `ba311457`, `python scripts/audit.py` passes 3,877 default and
4,800 validation jobs, public lint, authored diagnostics and transitive
standard-axiom checks. Raw output is
`.codex/scratch/abstraction-extraction/integration-audit.log`. Independent
semantic reviews accept the stopping scope, pinned consumer contract and
discrete/diffuse distinction. The collected closing edits are documentation only.
