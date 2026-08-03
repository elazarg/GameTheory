# Total-variation data-processing equality iff no fiber cancellation

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Proof-mining §46, extracted 2026-08-03; standard equality-case attribution required | Target: `Transport/Distinguishing.lean` companion | `INDEPENDENT`; reactivate for a lossless monitoring quotient |

For finite laws `μ,ν` and map `g`, write `d_x=μ(x)-ν(x)`. Equality in

\[
  \sum_y\left|\sum_{x:g(x)=y}d_x\right|
  \le \sum_x |d_x|
\]

holds iff, in every fiber of `g`, all nonzero `d_x` have the same sign. This is
also exactly the condition under which the sign-optimal Boolean test for
`μ` versus `ν` is constant on fibers and therefore factors through `g`.

The result characterizes when monitoring coarsening is lossless for a
designated pair of hidden laws. It is pair-specific: one garbling may be
lossless for one pair and lossy for another. It does not characterize equality
for general f-divergences or stochastic channels.

Standalone audiences include statistics, information theory, privacy, and
monitoring design. This is a standard triangle-inequality equality case;
novelty is not claimed. Its value is a small exact formal interface and a
falsifier for claims that a coarsening preserves all deviation evidence.

It returns to `ACTIVE` if a monitoring compiler must certify that a chosen
signal quotient loses no relevant deviation distinction.
