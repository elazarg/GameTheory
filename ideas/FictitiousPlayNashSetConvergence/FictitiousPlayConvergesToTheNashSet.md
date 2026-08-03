# Fictitious play converges to the Nash set

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED` by compactness; maturity `M` | Proof-mining §39, extracted 2026-08-03 | Pending companion to `Learning/FictitiousPlayPotential.lean` | `INDEPENDENT`; reactivate for a learning-based response producer |

## Statement and proof

For the finite potential-game fictitious-play process already formalized, let
`b_t` be empirical beliefs and `I(b)` aggregate mixed improvement. Production
proves `I(b_t) -> 0`, while `I(b)=0` is equivalent to mixed Nash.

Compactness gives both stronger conclusions:

1. if `b_{t_k} -> b`, continuity gives `I(b)=0`, so `b` is mixed Nash;
2. if `dist(b_t, Nash)` failed to tend to zero, some subsequence would stay a
   fixed positive distance away and admit a non-Nash cluster point,
   contradicting item 1.

The proof requires no convergence of the beliefs themselves. The missing Lean
surface is topology: continuity of the finite-sum improvement, compactness of
the mixed-profile simplex, closedness/nonemptiness of the Nash set, and a
distance-to-set wrapper.

Nonclaim: this is not convergence to one Nash equilibrium and does not extend
to arbitrary games without the already-landed vanishing-improvement premise.
Standalone value is a clean set-convergence theorem for learning dynamics;
the result is likely classical, so publication would require attribution and a
formalization-oriented framing rather than a novelty claim.

It returns to `ACTIVE` if a learning-based response producer needs actual
Nash-set proximity rather than vanishing regret alone.
