# D85: local scalarization and Pareto maximality

- **Status:** adopted for the local mathematical bridge and the two domain consequences.
- **Date:** 2026-11-11
- **Experiment:** EXP-180

## Question and alternatives

Can a shared order theorem connect existing Groves and bargaining scalar
objectives to Pareto efficiency without choosing an interpersonal welfare
scale in the semantic core?

Mathlib already owns `IsMaxOn`, `Maximal`, pointwise orders, aggregate strict
inequalities and global strictly monotone transport
(`MaximalFor.maximal_of_strictMonoOn`). The candidate adds only the missing
incumbent-local implication: a feasible objective maximizer is maximal if
every strict improvement of that incumbent would raise the objective. Both
domain and objective codomain need only preorders. The theorem has no players,
utility representation, game, probability, finite enumeration or topology.

Direct arithmetic proofs remain the baseline. The two clients must consume
the same small theorem, not a new scalarization or welfare record. No speed
or cold-cost advantage is claimed; this experiment tests assumptions and
mathematical ownership.

## Domain meanings stay separate

For Groves, reportwise maximization of the sum implies Pareto maximality in
the range of attainable reported-valuation vectors. This concerns allocation
values at the fixed report, before payments. It neither asserts every Pareto
point maximizes that sum nor identifies reported value with realized net
utility or truthful welfare. No nonempty-player hypothesis is required.

For Nash bargaining, strict positivity of gains at the selected solution
implies the existing full `IsPareto` predicate. Any dominating alternative
remains individually rational. Mathlib's product inequality needs positive
incumbent factors, weak gains everywhere and one strict gain. Other feasible
points may lie on zero-gain boundaries, so global strict monotonicity of the
product on the entire feasible set is stronger than needed. The existing
unconditional weak-Pareto theorem remains unchanged. Empty-player evidence
must continue to compile without a nonemptiness assumption.

## Rejection controls and extraction

Zero or negative player weights do not generally turn scalar maximizers into
Pareto points. Positive weights alone are insufficient when an alternative
bias can outweigh every player's strict gain. An individually rational
zero-product bargaining maximizer can be Pareto dominated. `IsMaxOn` alone
does not include candidate feasibility. These failures must remain explicit
rather than being repaired by changing the Pareto predicate.

Ordinal Pareto comparisons and the selected scalar objective are different
data: independent positive rescaling of player values preserves Pareto
comparisons but can change a fixed-weight sum maximizer. No universal
common-scale axiom, cardinal preference hierarchy, new social objective,
equilibrium engine or choice representation follows.

The mathematical bridge belongs to `Math.Scalarization`, with only Mathlib
imports. Report dependence and Groves payments stay under `Mechanism`;
disagreement, participation and the Nash product stay under `Cooperative`.
This dependency direction can support a later shared mathematical-economics
component without modifying MathEconLib in this experiment.

## Validation

Baseline `1c6112a9`; Lean 4.35.0 / Mathlib v4.35.0. Exact commands:

```text
lake --iofail build GameTheory.Math.Scalarization
lake --iofail build GameTheory.Tests.Groves GameTheory.Tests.BargainingScalarization GameTheory.Experimental.Exp180.ScalarizationBoundary
python scripts/audit.py --source-only
python scripts/audit.py
```

The independent mathematical build passes 716 jobs; focused owner/consumer
and rejection controls pass 3,158 jobs, and source checks pass. The positive
bargaining domain explicitly contains zero-gain boundary improvements with
equal product, refuting global strict monotonicity on that same domain.
Independent semantic review accepts the local hypothesis, domain meanings,
empty-player behavior and actual biased canonical choice. Integration evidence
is recorded in EXP-180 before collection. No performance claim follows from
these build counts.

On checkpoint `eb6a27ad`, `python scripts/audit.py` passes 3,875 default and
4,779 complete validation jobs, public lint, authored diagnostic checks and
transitive standard-axiom checks. Raw output is ignored
`.codex/scratch/exp180/integration-audit.log`.
