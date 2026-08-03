# A fixed response architecture has a unique delivered credible target

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Proof-mining §36, extracted 2026-08-03 | Target: `SplitDomainSemanticCredibilityCharacterization.lean` companion | `INDEPENDENT`; reactivate for architecture gluing |

Let `A` be one finite public response architecture and `D` one split response
domain. If targets `u` and `v` are semantically credible for the same `(A,D)`,
then for every delivered configuration and player,

\[
  D.\mathrm{delivery}(z) \Longrightarrow u(z,i)=v(z,i).
\]

Each semantic witness bounds the same prescribed finite-horizon payoff within
`M/T` of its target. The triangle inequality gives
`|u(z,i)-v(z,i)| <= (M_u+M_v)/T` for every positive horizon; Archimedean
order, or uniqueness of the two limits, gives equality.

This is a rigidity theorem on the declared delivery domain. It does not imply
equality at omitted nodes, enlarge the domain, or construct a credible target.
Its most useful falsifier is underspecification: two targets differing only
outside `D.delivery` are allowed.

The production dependencies are the existing finite-horizon convergence
method on `SemanticCredibilityWitness`. A source/novelty audit is required
before external publication; the mathematical content is a concise formal
specification theorem.
