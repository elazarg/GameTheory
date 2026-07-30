# D13: LP certificates are admissible, but not yet a dependency

Decision: do not add an LP package now. Kernel-checked LP certificates satisfy
the trust and containment rules, but the measured stack does not remove the
finite-game proof work that motivated the dependency.

Experiment IDs: [EXP-026](../ExperimentLog.md).

## Hypothesis

EXP-007's mixed-equilibrium proof explicitly enumerates four profiles and ends
in `norm_num` because kernel `decide` cannot reduce rational arithmetic. A
solver acting only as an oracle, with a pure Lean verifier checking its Farkas
certificate, might replace that hand expansion and create a finite,
non-topological route to correlated-equilibrium existence or minimax.

## Competing designs

*Keep the current proof.* No dependency and no new bridge, at the cost already
recorded by EXP-007.

*Take `lp-verify` only.* Check certificates generated outside Lean and write a
game-to-LP correctness bridge locally.

*Take `lp-tactic` with an out-of-process certificate source.* Reconstruct proof
terms while keeping the solver outside the package graph.

*Take the pure-Lean backend.* Use exact-rational simplex as the untrusted oracle
and the same verifier, avoiding FFI and subprocess requirements.

*Take the SoPlex meta-package.* Fast and convenient, but a separate native,
platform-sensitive dependency decision rather than evidence about the verifier.

## Representative examples

The positive control is a two-row rational implication requiring a genuine
Farkas certificate. The hostile use site is
`GameTheory.Examples.uniformPennies_verify`, including the explicit
`pennyProfiles` and `sum_pennies` helpers it was meant to replace. A final
generic probe multiplies an arbitrary payoff parameter by an existential
probability, the smallest shape needed to distinguish a closed game instance
from a theorem quantified over games.

## Measurements

Full commands, exact revisions, probe text, and failed outputs are preserved in
[`experiments/EXP-026.md`](../experiments/EXP-026.md).

| Measure | Result |
|---|---|
| toolchain skew | packages pin 4.31-era toolchains; all measured candidates compile on this project's `v4.32.0` |
| licenses | four transitive candidates, all Apache-2.0 |
| manifest disturbance | four additions in isolation; zero changes to existing revisions or the repository manifest |
| authored trust hazards | zero custom axioms, `sorry`, `admit`, `unsafe`, `native_decide`, `ofReduceBool`, or FFI declarations |
| meta partiality | 28 `partial def`s in `LPTactic`; none survive as assumptions of produced proofs |
| soundness axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| certificate rejection | verifier tamper suite passes |
| import containment | 15/15 negative probes pass; 3/3 positive LP probes fire |
| downstream build delta | 49 jobs including the probe |
| source surface | 67 Lean files, 9,935 lines |
| concrete Farkas implication | succeeds with the pure backend forced |
| EXP-007 proof reduction | none material; explicit enumeration remains |
| generic payoff/probability product | rejected as nonlinear |

## Evidence from existing libraries

`LPVerify.Verified` carries proof fields for optimal, infeasible, and unbounded
outcomes; failed checks return `unchecked`. The source audit and downstream
`#print axioms` agree with that design. This is the same acceptable
untrusted-oracle/trusted-checker boundary that excludes `native_decide`: the
solver's answer is evidence, not authority.

The limitation is above that boundary. Neither the verifier nor the tactic
defines the semantic map from a finite game to an LP, and the tactic accepts
closed rational coefficients rather than a product of theorem parameters and
existential probabilities.

## Unexpected costs

The dependency is cleanest where it is least useful. `lp-verify` can certify a
manually presented `Problem`, but the missing game-to-`Problem` bridge is the
substantial theorem. `lp-tactic` makes ordinary linear arithmetic pleasant, but
the Matching Pennies proof spends its effort exposing finite sums and dependent
profile updates before linear arithmetic begins.

The full `LP` package would also collapse two decisions into one by adding
SoPlex and native linking. It was therefore excluded from the verifier trust
result rather than treated as its default installation.

## Kill condition

Reject adoption if the checked path adds a nonstandard axiom or compiler-trust
shortcut, requires a native backend, leaks into an audited lower layer, has no
compatible pin, or fails to make the representative proof materially smaller
or more maintainable.

The last condition fired. A second, stronger claimed benefit also failed: the
generic payoff/probability probe is outside the tactic's linear fragment.

## Result: narrow; no dependency

Kernel-checked LP certificates are architecturally admissible. The measured
packages are not adopted because admissibility alone is not a consumer.
`lakefile.lean`, `lake-manifest.json`, the source roots, and the public API stay
unchanged.

Reopen D13 only when one of these is concrete:

1. a finite-game-to-`LP.Problem` bridge whose correctness theorem eliminates
   the explicit enumeration it replaces;
2. a generic checked LP duality/feasibility theorem sufficient for CE
   existence or finite minimax; or
3. a downstream certificate theorem whose measured proof reduction justifies
   the verifier-only dependency.

Any reopening repeats the version, license, trust, manifest, build, and
positive/negative reachability measurements. A solver backend remains a
separate competitor and may not be smuggled in with the verifier.

## Consequences for public API

None. EXP-007's proof stays authoritative, finite algorithms remain free of
external solver code, and the existing Analysis boundary is unchanged.
