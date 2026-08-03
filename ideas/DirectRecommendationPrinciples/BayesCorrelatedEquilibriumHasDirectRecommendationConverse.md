# Bayes-correlated equilibrium has a direct-recommendation converse

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Proof-mining §42, extracted 2026-08-03; revelation-principle attribution required | Target: `Mechanism/Bayesian/BayesCorrelatedEq.lean` | `INDEPENDENT` |

The landed direction maps every Bayes-Nash outcome under an information
structure to a BCE law. Conversely, given a finite BCE law `ψ`, choose each
signal type to be the player's recommended action, use `ψ` as the joint
type/recommendation law, and let every player follow the recommendation.
Bayes plausibility gives the prior marginal; BCE obedience is exactly the
Bayes-Nash inequality against deviations depending on private type and
recommendation. The outcome law is `ψ`.

Thus finite BCE laws are exactly outcomes implementable by Bayes Nash under
some finite information structure. This grants a mediator/information
structure; it is not an implementation by an ordinary complete-information
Nash profile and does not close the stochastic de-correlation problem.
Mathematics is complete, but a source audit should precede any novelty claim.
