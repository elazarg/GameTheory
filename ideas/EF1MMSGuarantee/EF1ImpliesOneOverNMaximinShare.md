# EF1 implies a one-over-n maximin-share guarantee

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED` for finite additive nonnegative valuations, maturity `M` | Proof-mining §48, extracted 2026-08-03; prior-literature audit required | Target: fair-division EF1/MMS companion | `INDEPENDENT`; reactivate for stronger MMS approximation work |

Fix agent `i`. For every other allocated bundle that `i` envies, choose the
EF1 witness good whose removal removes the envy. There are at most `n-1`
marked goods. In a partition attaining `i`'s maximin share, at least one of the
`n` bundles contains no marked good. Its value is at least `MMS_i`, hence the
value of all unmarked goods is at least `MMS_i`.

Each allocated bundle contributes at most `v_i(A_i)` unmarked value: this is
trivial for `A_i`, and for every other bundle it is exactly the EF1 inequality
after removing its marked witness (or the whole bundle if it was not envied).
Therefore

\[
  MMS_i \le v_i(\text{all unmarked goods})
        \le n\,v_i(A_i),
\]

which proves `v_i(A_i) >= MMS_i/n`.

The proof needs completeness, finite nonempty agents, additive nonnegative
valuations, and existence/attainment of the finite MMS partition. It does not
prove `1/2`-MMS or a stronger guarantee for every EF1 allocation.

Standalone audiences are fair division and approximation guarantees. The
bound may be known; novelty must be checked. Its immediate independent value is
to connect two already-formalized notions and give the existing round-robin
construction a machine-checked MMS corollary.

It returns to `ACTIVE` if fair-division development becomes an objective
priority or a stronger algorithm-specific bound reuses the marked-good lemma.
