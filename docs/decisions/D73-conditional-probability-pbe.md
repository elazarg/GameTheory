# D73: conditional-probability perfect Bayesian equilibrium

- **Status:** adopted within the explicit-chance boundary
- **Date:** 2026-10-28
- **Experiment IDs:** [EXP-167](../ExperimentLog.md)

## Mathematical target and competing designs

The user selected conditional-probability PBE for general finite extensive
games. This is distinct from the observed-action, independent-type
Fudenberg--Tirole notion considered in the inconclusive EXP-166 prototype.

The specification follows Definitions 1--2 of Merotto and Wolitzky,
[*Conditional Probability Perfect Bayesian Equilibrium* (March 2026)](
https://economics.mit.edu/sites/default/files/inline-files/CPPBE%20March%201%202026.pdf).
One conditional probability system on terminal histories represents all
information-set beliefs, including off-path ones. Conditional continuations
agree with the strategy at nodes assigned positive assessment belief.
Nature is treated as having singleton information sets, so its continuation
law is constrained even off path. Whole-policy sequential rationality uses
the existing assessment contexts and actual-law integrability conditions.

Competing representations were a concrete PMF conditional system with the
chain rule, its characterization by limits of fully supported terminal laws,
and the existing sequential-equilibrium perturbations. The first is the
semantic definition. Compactness supplies the second as a construction tool;
requiring the third in the definition would identify a different refinement.

## Semantic boundary

`Math.Probability.ConditionalSystem` stores an ordinary PMF on each nonempty
conditioning event, support in that event, and the nested-event chain rule.
It introduces no probability carrier or new conditioning operation; fully
supported laws use the existing posterior. The constructor works on arbitrary
discrete carriers. Subsequence compactness requires a finite carrier and
belongs in `ConditionalSystemCompactness`, outside the stable data leaf.

`Protocol.ConditionalPBE` represents belief atoms by conditional terminal
cone probabilities. Its continuation field retains the positive-belief guard;
its Nature field imposes continuation compatibility at every nonterminal
history with no active player. These are named certificate fields, not prose
assumptions. `IsConditionalPBE` requires a `HasExplicitChance` parameter:
every legal action at a reachable player node has a deterministic successor.
Its body composes only this consistency condition and the canonical
whole-policy rationality predicate. The EFG solution leaf is a transparent
specialization; language syntax imports no solution concept.

The original API conjoined `HasExplicitChance` with the assessment conditions.
That made nonexistence automatic on unsupported game representations. Requiring
the certificate when forming the predicate preserves the applicability
boundary without mixing a property of the game into equilibrium. The SE bridge
and existence theorem take the certificate explicitly; common-system
consistency remains independent of it. The off-path rejection consumer supplies
its game's certificate, so its nonexistence proof still refutes the beliefs.

The explicit-chance certificate is material. General stochastic protocols
can hide a random draw inside an active player's transition. If the action
has probability zero, parent-node continuation compatibility alone leaves
that draw's conditional probabilities unrestricted. The source instead gives
Nature singleton nodes, which constrain those probabilities off path. This
slice enforces the source presentation with a named certificate, rather than
silently admitting that representation gap. A two-successor player-transition
control refutes the certificate. Native embedded randomness would require
an explicit Nature-node transformation or a separately validated generalized
compatibility condition; neither is claimed here.

The existing terminal runner is retyped onto its terminal-history support.
Its reachability support theorem is moved from Analysis to stable
`HistoryBackward`; there is one declaration and one execution semantics.

The source's standard game-theoretic scope is finite extensive games with
perfect recall and at most one mover per node. Definitions are available for
Protocol assessments generally; each theorem states its actual assumptions.
Finite-history sequential equilibrium gives a common system by taking one
subsequence of all fully mixed terminal-law conditionals. Its existence
consumer retains finite players, decision recall, a total legal fallback and
a well-founded terminal certificate, with the explicit-chance certificate for
the resulting PBE. No finite raw action, state or information
carrier is imposed when finitely many legal histories suffice.

## Hostile slice and measurements

The representative positive slice constructs the common system from an
existing sequential-equilibrium assessment. The hostile slice reuses the
weak-PBE-but-not-SPE example: its off-path guess belief is dogmatic, whereas
the intervening chance step chooses the hidden bit fairly. Representation
would assign probability one and Nature compatibility probability one-half
to the same terminal event under the same conditioning event.

Kill conditions were another play evaluator, changing existing weak PBE or
SE, an assumed common-system witness instead of a construction, deleting the
positive-belief guard, or allowing unconstrained off-path Nature. The initial
unrestricted-protocol interpretation failed the last condition and was
narrowed by `HasExplicitChance`, with a two-successor player-transition
counterexample. This failure and the positive separated-chance control are
preserved in EXP-167.

The focused strict bridge/existence/control build passes 3,807 jobs. The full
`python scripts/audit.py` passes the public build (3,872 jobs), complete
validation build (4,673 jobs), public lint and transitive standard-axiom
checks. Source boundaries and driver coverage also pass. The common system is
constructed from SE approximations, and the weak-PBE control is rejected by
the required one-versus-one-half conditional mass contradiction.

The certificate-parameter API and its positive and rejection consumers pass
the complete strict validation target (4,673 jobs), including the lint and
axiom drivers, followed by `lake --iofail lint` and
`python scripts/audit.py --source-only`.

## Deliberate limits

This package does not identify weak PBE with CPPBE or CPPBE with SE. A general
CPPBE-to-subgame-perfection theorem and a CPPBE-but-not-SE example remain
separate theorem delivery. Infinite-history existence and the
Fudenberg--Tirole observed-action specialization are not claimed.
