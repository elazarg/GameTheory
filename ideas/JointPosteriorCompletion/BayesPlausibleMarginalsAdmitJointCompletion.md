# Bayes-plausible posterior marginals admit joint completion

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED` under finite full support, maturity `M` | Proof-mining §47, extracted 2026-08-03; attribution/novelty unassessed | Target: `Mechanism/Bayesian/JointFeasiblePosteriors.lean` | `INDEPENDENT`; reactivate for private-recommendation completion |

Given prior `π` and each agent's Bayes-plausible law `τ_i` over posteriors,
define, for `π(ω)>0`,

\[
q_i(b\mid\omega)=\frac{\tau_i(b)b(\omega)}{\pi(\omega)}.
\]

Bayes plausibility normalizes `q_i`. Draw the agents' posteriors independently
conditional on `ω`. Then

\[
Pr(\omega,b_i)=\pi(\omega)q_i(b_i\mid\omega)
              =\tau_i(b_i)b_i(\omega),
\]

so every requested marginal is recovered and each posterior is calibrated.
Thus projection of the jointly feasible set onto the product of individual
feasible sets is surjective; obstructions concern a **prescribed correlation**,
not coexistence of the marginals.

Nonclaims: the theorem does not realize an arbitrary joint posterior law,
preserve a desired cross-agent correlation, or cover zero-prior states without
additional bookkeeping. Standalone audiences are information design, Bayesian
persuasion, and common-prior geometry. Novelty is unassessed and likely related
to standard Bayes-plausibility constructions.

It returns to `ACTIVE` if a stochastic correlation construction needs a
jointly feasible private-recommendation completion from marginal devices.
