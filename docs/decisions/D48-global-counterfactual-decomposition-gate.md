# D48: Gate global counterfactual decomposition on root usefulness

- **Status:** adopted for bounded common-depth topological chains
- **Date:** 2026-08-10
- **Experiment ID:** EXP-085, EXP-086

## Decision

Any across-information-set deviation decomposition must include information
sites reached only by the alternative policy and weight local counterfactual
terms by that alternative's own reach. Baseline-reached-only sums are rejected.

For a common-depth information site, split the canonical behavioral run at the
site depth. A policy replacement that agrees off that site is invisible before
the cut and on cut histories outside the site. Reindex the cut law over the
canonical information-history fiber, factor history reach into own and
counterfactual reach, and obtain exactly

`root gain = own reach * D45 counterfactual regret`.

For general PMFs, both actual root laws and the counterfactual continuations
being evaluated must have integrable payoffs. Integration of the root laws
alone cannot certify a continuation at zero own reach. The separate
counterfactual certificate applies exactly where counterfactual reach is
nonzero; it does not impose a global payoff bound. Finite telescoping chains
likewise certify the actual root law at each intermediate profile.

Perfect recall supplies common own reach. Apply the theorem to a topologically
ordered finite chain of local replacements and telescope the root gains. This
is the adopted whole-policy decomposition surface. It is not yet a global CFR
convergence or exploitability claim; those require the next cumulative
consumer.

## Hostile evidence

The incumbent in the two-stage complementarity fixture plays `false,false`;
the alternative plays `true,true`. Every actual one-site deviation test is
harmless, but the whole policy gains one. The first-site D45 action regret is
zero. The off-path `second-after-true` D45 action regret is one. Alternative
own reach gives the two relevant sites unit coefficients and the exact sum is
the root gain. Baseline own reach assigns the decisive off-path site zero mass.

This evidence is theorem-level: it evaluates canonical behavioral
continuations, D45 counterfactual action regret, recursive player reach, and
the existing well-founded root value. It does not receive credit merely for
naming a sum.

## Evaluator contract

The API takes an explicit site depth and continuation fuel. Common depth makes
the cut well-defined. A runner-support theorem handles shorter terminal
branches by absorption and proves every nonterminal cut history consumed the
full prefix fuel. Different sites may use different continuation fuels; no
second horizon-indexed payoff or regret definition is introduced.

Sites with unequal-depth histories remain outside this theorem. They require a
separate evaluator experiment rather than weakening the adopted statement.

## Kill conditions and next gate

Reject a proposal if it omits off-path sites, uses baseline own reach, adds a
second runner or regret semantics, stores global finiteness in the model,
exposes raw update or transport, or labels an arithmetic telescoping lemma as
global CFR without proving the single-site semantic bridge.

The hostile two-site consumer establishes exact unit root gain from a zero
first term and a unit off-path term. Thus a local decomposition must account
for changes at sites that the incumbent profile never reaches. See EXP-086
in the [experiment log](../ExperimentLog.md).
