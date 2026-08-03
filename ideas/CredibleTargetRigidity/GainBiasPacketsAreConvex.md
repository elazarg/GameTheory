# Gain--bias packets are convex

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Proof-mining §36, extracted 2026-08-03 | Target: split-domain gain--bias packet module | `INDEPENDENT`; reactivate for target selection |

If `(u,H,K)` and `(v,H',K')` are gain--bias packets for the same architecture
and split domain, and `0 <= λ <= 1`, then

\[
(\lambda u+(1-\lambda)v,
 \lambda H+(1-\lambda)H',
 \lambda K+(1-\lambda)K')
\]

is again a packet. Every packet equality is linear; every inequality is
preserved by nonnegative linear combination. Through the landed semantic
characterization, credible delivered targets form a convex set—and the
companion uniqueness theorem makes that set a singleton on the delivery
domain.

The coefficients must use the same architecture, domains, and row indexing.
Convex combinations of packets from different support-pruned domains are not
covered. Convexity verifies supplied witnesses; it does not produce one or
justify randomization between incompatible controllers.

Likely value is API-level: interpolation and selection of proof witnesses.
Novelty is unassessed and probably modest.
