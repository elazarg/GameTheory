# Fixed-target communication separation does not rule out retargeting

## Lifecycle card

| Field | Value |
|---|---|
| Lifecycle | `ACTIVE` |
| Status | `PROVED (M+L), scope fence` |
| Priority | `P2` |
| Provenance | Private-recommendation target separator, its absorbing lift, and Question 100's quantifier audit |
| Audited | 2026-08-03 |
| Consumer | Any attempted obstruction to ordinary uniform-equilibrium existence based on correlation nonimplementation |
| Formalization destination | Documentation fence beside the separator/lift; a future selectorwise theorem would need a new module |
| Formalization status | The fixed-target facts and alternative ordinary targets are landed; no selectorwise impossibility theorem exists |
| Reactivation / exit | Exit after all separator consumers state the target quantifier; reactivate when a universal target-selection argument is proposed |

## Claim ledger

| ID | Claim | Status |
|---|---|---|
| FT-SEP-1 | The target `(5/7,5/7)` of the explicit private-recommendation witness is separated from every independent mixed root law. | `PROVED (M+L)` |
| FT-SEP-2 | The absorbing lift preserves that exact target separation for ordinary behavior at the root. | `PROVED (M+L)` |
| FT-SEP-3 | The same example has other ordinary Nash, hence ordinary uniform, targets. | `PROVED / explicit witness` |
| FT-SEP-4 | Failure to implement one mediated target disproves existence of some ordinary uniform equilibrium payoff. | `FALSE inference` |
| FT-SEP-5 | Every sustainably selectable correlated target fails ordinary implementation. | `OPEN; not established by the witness` |

## Intuition

Failure to reproduce a particular mediated payoff is a target-preservation obstruction, not an equilibrium-existence obstruction. An ordinary construction may choose a different sustainable payoff. To rule out retargeting, a negative result must control every admissible target or every ordinary strategy, rather than one point selected for its correlation gap.

## Mathematical quantifier boundary

A fixed-target separator proves a statement of the form

\[
\exists v^\star\in V_{\mathrm{mediated}}
\quad
\forall \sigma\in\Sigma_{\mathrm{ordinary}},
\quad
\|\gamma(\sigma)-v^\star\|\ge\delta.
\]

An equilibrium-existence counterexample would require a much stronger conclusion, schematically

\[
\forall \sigma\in\Sigma_{\mathrm{ordinary}},
\quad
\sigma\text{ is not a uniform equilibrium},
\]

or, for a compiler obstruction tied to a target selector,

\[
\forall v\in V_{\mathrm{sustainably\ selectable}},
\quad
v\text{ cannot be implemented ordinarily with the required incentives}.
\]

The first formula does not imply either stronger formula. A positive proof is free to retarget to another implementable equilibrium payoff.

## Evidence

- [`PrivateRecommendationTargetSeparator.lean`](../../GameTheory/Concepts/Correlation/PrivateRecommendationTargetSeparator.lean) proves the exact private target and its positive distance from the product mixed-payoff image.
- [`PrivateRecommendationTargetAbsorbingLift.lean`](../../GameTheory/Concepts/Stochastic/PrivateRecommendationTargetAbsorbingLift.lean) proves the target-specific ordinary nonimplementation in a finite one-decision absorbing stochastic game.
- The same construction retains ordinary alternatives: the underlying one-shot game has pure Nash equilibria and an ordinary mixed Nash equilibrium with payoff `(2/3,2/3)`. Their absorbing lifts provide ordinary uniform targets.
- [Question 100](../../questions/old/Question100-EndogenousAutonomousCorrelationCompiler.md) explicitly separates witnesswise target preservation from selectorwise existence and records that the separator does not refute the root existence conjecture.
- [`ProductImageConvexification.lean`](../../GameTheory/Concepts/Correlation/ProductImageConvexification.lean) explains the geometry behind the fixed target without adding the missing equilibrium quantifier.

## Correct uses

The separator is strong enough to reject:

- a theorem claiming every private-recommendation target equals one product mixed payoff;
- a witnesswise compiler required to preserve the exact payoff `(5/7,5/7)` in the absorbing lift;
- an argument that convex-hull membership alone produces an exact ordinary profile.

It is not strong enough to reject:

- an ordinary equilibrium selecting a different payoff;
- a dynamic construction whose target is chosen after checking implementability;
- the root conjecture that every finite stochastic game has some ordinary uniform equilibrium.

## Falsifiers and missing theorem

The scope fence would be falsified only if the example had no alternative ordinary equilibrium target, contrary to the explicit pure and mixed Nash witnesses, or if the root conjecture itself imposed preservation of this particular mediated target. It does not.

To turn the construction into a root-level negative result, one would need a new theorem controlling **all** ordinary behavior strategies and all candidate equilibrium targets. The current production supplies neither an arbitrary-behavior payoff gap nor a semialgebraic reduction of that problem. Conversely, a positive construction need not solve target-preserving compilation if it proves that its chosen target is ordinarily sustainable.

## Exit condition

Keep the quantifier fence permanent wherever this separator is cited. Close this idea file after those citations are repaired. Reopen only for a new selectorwise invariant, an all-target nonimplementation theorem, or a positive retargeting theorem that makes the distinction operational.
