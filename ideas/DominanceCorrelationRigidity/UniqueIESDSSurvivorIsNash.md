# A unique IESDS survivor is Nash

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Proof-mining §40, extracted 2026-08-03 | Target: `DominanceSolvability.lean` / correlation adapter | `INDEPENDENT` |

Suppose iterated elimination of strictly dominated strategies leaves only the
pure profile `σ`. Mixed-Nash existence supplies a mixed equilibrium `p`, whose
independent action law is correlated equilibrium. The landed dominance theorem
forces every correlated-equilibrium law to be `PMF.pure σ`. Coordinate
marginals then force every `p_i` to be pure at `σ_i`; the mixed Nash
inequalities reduce to pure Nash inequalities for `σ`.

This removes the currently redundant Nash hypothesis from the corresponding
correlation-saturation theorem. It requires strict dominance and a unique full
profile survivor; it says nothing comparable for weak elimination or multiple
survivors. The proof is complete once a product-law marginal lemma is exposed.
The result is likely standard; novelty is not claimed.
