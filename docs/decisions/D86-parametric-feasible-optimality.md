# D86: parametric feasible optimality

- **Status:** adopted for the mathematical graph theorem and production specialization; economic probes remain experimental.
- **Date:** 2026-11-11
- **Experiment:** EXP-181

## Question and alternatives

What changes when the alternatives available to an optimizer depend on the
parameter? Compare the existing fixed-menu intersection proof with a
closed-feasible-graph-only proposal and with an explicit lower-hemicontinuity
premise. No correspondence, utility, equilibrium or constraint record is needed
to compare these mathematical statements.

`Core.ConstrainedNash` currently filters ordinary mixed Nash by payoff
thresholds. It does not change any available unilateral replacement. Its
name is not evidence of an existing generalized-game representation, and its
semantics are outside this change.

## Candidate mathematical operation

`Math.isClosed_feasibleMaximizers` asserts closedness of the set of pairs
consisting of a parameter and a feasible maximizing choice. Feasibility has a
closed graph, the feasible correspondence is lower hemicontinuous, and the
objective is jointly continuous into a linearly ordered space with closed
order. The theorem does not require real scores specifically, first
countability, compactness, nonempty values, convexity or a finite dimension.

The proof uses Mathlib's `LowerHemicontinuous.comp` and
`LowerHemicontinuous.inter_hasOpenCGraph`. Strictly improving alternatives
form an open correspondence. Intersecting it with the feasible alternatives
gives a lower-hemicontinuous correspondence whose nonempty domain is open.
The optimizer graph is the closed feasible graph minus that open domain.
This is a nonsequential proof; no selection of a same-index net is assumed.

The theorem uses the existing `IsMaxOn` together with candidate feasibility,
not a new optimization predicate. Compactness and nonemptiness supply
existence separately through Mathlib's extreme-value theorem. The sole
mathematical owner imports only Mathlib; the external fixed-point package
continues to be imported only from `Analysis`.

## Requiring consumers and boundary

The existing local-lottery fixed-point proof specializes the theorem to its
constant simplex menus. Its scores, expectation semantics, convexity and
fixed-point conclusion stay unchanged. This checks production reuse without
claiming that a changing-menu equilibrium theorem has been proved.

The economic consumer is divisible consumption with a changing nonnegative
budget. Feasible choices are an interval; a continuous recovery of a limiting
feasible quantity proves lower hemicontinuity. Existence and closedness of
optimal choices are separate consequences. These are recorded economic
examples, not promotion of a demand or general-equilibrium API.

The refuting budget has zero income, a nonnegative price and quantities capped
at one. At every positive price only quantity zero is affordable. At zero
price every capped quantity is affordable, and quantity one strictly beats
zero. Positive prices converging to zero therefore have optimal choices
converging to a nonoptimal quantity. Feasible graphs are closed, all feasible
values are nonempty compact convex sets, and all values lie in one compact
interval. The missing lower-hemicontinuity premise has independent content.
The budget correspondence is also proved upper hemicontinuous, so that law
alone does not replace the missing premise. Its failure of lower
hemicontinuity is proved separately at the free-price limit.

This is the closed-optimizer-graph component of parametric optimization,
not full Berge: no continuity of the value function, upper hemicontinuity of
the optimizer correspondence, utility-representation result, market clearing,
or generalized-Nash existence follows from this experiment alone.

An expected-utility application must still establish its evaluation-domain
guards before supplying the continuous score. This theorem does not turn an
undefined expectation into an admissible value. The existing finite-lottery
consumer retains its actual score and expectation semantics.

## Cost and validation

The baseline is `80741987`, Lean 4.35.0 / Mathlib v4.35.0. The production proof
previously intersected inequalities for a fixed family of alternatives; the
new theorem makes the missing assumption explicit for changing menus and
reuses Mathlib's existing correspondence calculus. No record candidate or
performance advantage is claimed. Comment-masked nonblank source counts use
`scripts.audit.source_code`, comparing the `replies_closedGraph` block up to
`domain_nonempty` at that baseline with the selected source: 25 direct lines
versus 26 client lines plus 31 shared theorem lines. This is not a reduction
of the fixed-menu proof or its cold source footprint. The admission is for a
genuinely new changing-menu operation used by both the budget and production
clients, rather than a claim that every fixed-menu proof becomes cheaper.
The D7/D60 new-record budgets do not license a record here; none is introduced.

Exact focused and integration commands:

```text
lake --iofail build GameTheory.Math.ParametricOptimality
lake --iofail build GameTheory.Analysis.LocalChoiceFixedPoint GameTheory.Experimental.Exp181.DivisibleBudget GameTheory.Experimental.Exp181.BudgetBoundary
python scripts/audit.py --source-only
python scripts/audit.py
```

The independent Math target passes 1,006 jobs; the production and complete
economic controls pass 3,633 strict build jobs. Independent read-only semantic
review accepts the general topological hypotheses, unchanged local-lottery
meaning, nonlinear budget consumer and the closed-graph-only refutation.
Integration evidence is recorded in EXP-181 before collection. Build counts
do not imply a performance advantage.

On checkpoint `ec2977ff`, `python scripts/audit.py` passes 3,876 default and
4,782 complete validation jobs, public lint, authored diagnostic checks and
transitive standard-axiom checks. Raw output is ignored
`.codex/scratch/exp181/integration-audit.log`.
