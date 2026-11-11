# D80: binary mixing does not supply arbitrary PMF comparison closure

- **Status:** binary-only proposal refuted; guarded client prototypes remain experimental.
- **Date:** 2026-11-11
- **Experiment:** EXP-175

## Question and competing designs

The survey proposes a Mixable level between order and expected utility. Is
the existing binary `Preference.Convex` law sufficient for pure-deviation
reduction and mixed-dominance exclusion on general discrete PMFs?

Compare binary compatibility with direct hypotheses preserving comparison
bounds under the actual PMF deviation kernels. Do not introduce a universal
mixture structure before those clients discriminate the required laws.

## Refuting evidence

`Experimental.Exp175.MixtureClosure` defines a preference on PMFs over naturals:
infinite-support laws outrank finite-support laws, with indifference inside
each class. The module proves reflexivity, transitivity, totality, and the
full simultaneous-pair binary convexity law, including weights zero and one.

Every point mass is weakly below the finite-support base `pure 0`. Mixing the
point masses with the geometric law gives that same infinite-support geometric
law, which is strictly above the base. Thus binary compatibility plus a total
preorder does not preserve a bound under arbitrary PMF mixtures. This is a
failure on a total preference, independent of undefined expected utility.

This refutes the binary-only proposal on general PMFs. It does not refute
finite-support reductions, stronger continuity assumptions, or a correctly
specified countable-mixture law. The original survey remains the historical
hypothesis rather than being rewritten to hide this failure.

## The two clients spend different guards

The direct mixed-Nash prototype assumes only the comparison closure of the
supplied profile's actual pure-deviation kernels. The expected-utility instance
uses `euPreference_bind` and the existing expectation-definedness premise for
each actual mixed deviation. It imposes no condition on unrelated laws.

The strict-gain exclusion prototype is weaker: its closure implication may
assume the positive comparison from the alleged strict gain. For expected
utility that comparison already supplies the mixture's expectation guard, so
no additional definedness premise is required to derive the contradiction.
This matches the logical shape used by mixed-dominance exclusion.

Both prototypes compile, including their numerical instances. They do not
establish a generic rationalizability or survival theorem. This experiment
does not construct a new numerical undefined-mixture counterexample or claim
that componentwise integrability implies mixture definedness. Existing
actual-law guards remain explicit, as required by D62.

## Decision and validation

Keep the counterexample and prototypes under the named experiment. No stable
Mixable predicate, representation theorem, new probability carrier, certificate
record, or equilibrium definition is admitted. Before promoting a closure
interface, find a stable non-EU client and determine whether it needs full
weak comparison, conditional comparison reversal, finite mixing, or arbitrary
PMF mixing. Direct profile-local hypotheses remain a valid baseline.

Baseline: `03e34edb`; implementation checkpoint: `1d908f6b`. Exact commands:

```text
lake --iofail build GameTheory.Experimental.Exp175.MixtureClosure
python scripts/audit.py
```

The focused build passes 3,062 jobs. The full audit passes 3,872 default and
4,763 validation jobs, public lint, authored diagnostic checks and transitive
standard-axiom checks. The axiom driver includes the new experimental module;
the public lint scope excludes experiments as before. Raw output is ignored
`.codex/scratch/exp175/integration-audit-final.log`. Independent semantic review
found no blocker to retaining this experiment-only result.
