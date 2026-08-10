# D48: Gate global counterfactual decomposition on root usefulness

- **Status:** provisional; coefficient decided, generic root theorem pending
- **Date:** 2026-08-10
- **Experiment ID:** EXP-085

## Decision so far

Any across-information-set deviation decomposition must include information
sites reached only by the alternative policy and weight local counterfactual
terms by that alternative's own reach. Baseline-reached-only sums are rejected.

This is not yet an adopted global CFR interface. Promotion requires a generic
single-site theorem relating a canonical root payoff change to the matching
local counterfactual term, followed by a telescoping theorem for a topological
sequence of site changes. The final consumer must bound root regret or
two-player zero-sum exploitability using all local learners.

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

## Evaluator constraint

The first and second sites have different remaining depths. The hostile slice
uses continuation fuels two and one. A common larger fuel is also sound once a
bounded-termination certificate guarantees absorption, so EXP-085 does not
choose prematurely between a remaining-horizon evaluator and a sufficiently
large absorbing evaluator. A generic theorem must make one of those contracts
explicit; an unqualified fixed-fuel identity is not acceptable.

## Kill conditions and next gate

Reject a proposal if it omits off-path sites, uses baseline own reach, adds a
second runner or regret semantics, stores global finiteness in the model,
exposes raw update or transport, or labels an arithmetic telescoping lemma as
global CFR without proving the single-site semantic bridge.

Next prove that bridge under the smallest bounded evaluator certificate, then
telescope topologically ordered local replacements. Only a root-regret or
exploitability consumer can move this decision to adopted.
