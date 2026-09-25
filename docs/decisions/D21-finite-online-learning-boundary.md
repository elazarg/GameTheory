# D21: finite online learning uses law-free mathematics and an analytic bridge

- **Status:** adopted and promoted
- **Date:** 2026-08-02, amended 2026-08-16
- **Experiment IDs:** EXP-049, EXP-101

## Decision / question

Where the pinned finite multiplicative-weights algorithm and its game-theoretic
self-play consumer belong without coupling its vector theorem to the canonical
PMF representation or adding analytic dependencies to Core.

## Competing designs

1. Put a PMF-valued multiplicative-weights implementation directly in
   `GameTheory.Math.OnlineLearning`.
2. Prove the normalized finite-vector algorithm and regret theorem in
   `GameTheory.Math`, package the vector as a PMF in a thin Probability
   adapter, and compose it with finite self-play in `GameTheory.Analysis.Learning`.
3. Put the algorithm and self-play capstone in `GameTheory.Core.Learning`.
4. Retain the predecessor's direct `PMF` implementation or leave the
   quantitative family deferred.

Design 2 is adopted. Design 1 couples a reusable vector theorem to one law
representation and prevents the focused online-learning module from being used
without probability. After EXP-101 the adapter is a sibling below
`GameTheory.Math`, so this is a module-level boundary rather than a top-level
namespace boundary. Design 3 would make Core own exponential and logarithmic
analysis solely for one algorithm. Design 4 retains probability in the
algorithm's foundational interface; the vector/adapter split preserves a
probability-free quantitative theorem while using the same canonical PMF law
as game semantics.

## Representative hostile slice

For an arbitrary nonempty finite action carrier and gains in `[0,1]`, the
independent module constructs cumulative gains, exponential weights, normalized
probability coordinates, and the best-in-hindsight regret, then proves the
fixed-positive-rate external-regret bound. The Probability adapter constructs
the unique law with those coordinates using `PMF.ofFintype` and proves the
expectation identity.

The game-facing slice recursively runs one such learner per player, proves its
score equals the game-independent cumulative gain, and combines the regret
bound with Core's independent-self-play averaging theorem. It produces both an
explicit finite-horizon approximate CCE bound and, for every positive
tolerance, a concrete rate and finite horizon witnessing an approximate CCE.

## Measurements

| Measure | EXP-049 result |
|---|---|
| Mathlib overlap | exponential convexity/logarithm estimates reused; no multiplicative-weights or external-regret implementation found |
| law-free online-learning module | 227 nonblank lines; two direct Mathlib analysis imports |
| canonical-law adapter | 49 nonblank lines; imports only `FinDist` and the law-free module |
| analytic game bridge | 197 nonblank lines; imports Core learning, the adapter, and the law-free module |
| stable Core learning growth | 133 to 301 nonblank lines; all 168 added lines are finite product-law/normalization identities, with no `Real.exp` or `Real.log` |

## Kill condition

Reject the split if finite online learning essentially needs an infinite law,
if Core must import the exponential/logarithmic implementation, if a second
probability, regret, or CCE API appears, if the proof needs an untrusted
evaluator or custom axiom, if finiteness must be stored in game data, or if the
bridge reaches Protocol or the fixed-point dependency.

Probability coordinates are the algorithmic object. The sibling adapter
constructs their PMF without coupling the vector proof to probability or
introducing a second law representation.

## Result

`GameTheory.Math.OnlineLearning` owns finite vector algebra and the quantitative
regret theorem. `GameTheory.Math.Probability.OnlineLearning` is the sole
representation adapter. `GameTheory.Core.Learning` owns topology-free finite
self-play and regret-to-CCE identities. `GameTheory.Analysis.Learning` is the
one-way consumer that mentions `Real.exp`, `Real.log`, and the quantitative
self-play capstones.

## Consequences for public API

Core users do not pay for or reach the MW implementation. Algorithm users get
canonical PMF laws. Game-facing
results reuse the sole `UtilityGame.externalRegret` and
`IsεCoarseCorrelatedEq`; the independent module's external regret is explicitly
the game-free best-action-minus-algorithm quantity.

The bridge is opt-in, like the existing Repeated and Protocol analytic
bridges. This is a dependency decision, not a claim that finite-horizon online
learning requires topology or fixed points.

## Promotion evidence

`GameTheory.Math.OnlineLearning` remains independent of probability laws.
`Core.Learning` owns game averaging, while `Analysis.Learning` connects the
vector regret theorem and its law adapter to the game capstone. Protocol and
fixed-point existence do not belong in that bridge.

EXP-101 moved the adapter from `GameTheory.Probability` to
`GameTheory.Math.Probability` and validated the whole `GameTheory.Math` subtree
as a separate Lake target. It did not merge the two modules or change the
algorithmic interface.
