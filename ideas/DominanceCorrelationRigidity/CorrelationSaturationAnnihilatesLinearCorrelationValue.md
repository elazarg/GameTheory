# Correlation saturation annihilates linear correlation value

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Proof-mining §49, extracted 2026-08-03 | Target: `CorrelationSaturation.lean` / `ValueOfCorrelation.lean` | `INDEPENDENT` |

In a finite correlation-saturated game, every correlated-equilibrium law is a
public mixture of independent mixed-Nash laws. Therefore, for any linear
functional `L` on action laws,

\[
\max_{\mu\in CE}L(\mu)
=\max_{p\in MNE}L(productLaw(p)).
\]

The `>=` direction uses that every mixed-Nash product law is correlated
equilibrium. For `<=`, linearity turns the value of a public mixture into the
average of component values. Finiteness supplies maxima rather than suprema.

This is not true for arbitrary nonlinear risk criteria, and a public mixture
of mixed-Nash laws need not itself be one independent mixed strategy profile.
The theorem packages saturation's operational meaning for welfare and every
other linear planner objective. It is a formal-library corollary; novelty is
unassessed.
