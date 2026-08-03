# Sorin's finite-horizon singleton benchmark

| Field | Value |
| --- | --- |
| Citation of record | Sorin, *Asymptotic properties of a non-zero sum stochastic game*, IJGT 15(2):101--107 (1986) |
| Source confidence | `PRIMARY_VERIFIED` |
| Mathematical status | `PROVED` |
| Repository status | `ADAPTED` |
| Lean status | `PARTIAL` |
| Objective priority | `P2` |
| Exact scope and quantifiers | In the cited absorbing game, every finite horizon has the stated singleton equilibrium payoff `(1/2, 2/3)`, with the source first-stage mixing recursion; this is a horizon-by-horizon statement. |
| Source alignment | Discounted equilibrium and the uniform-separation direction are landed; finite-horizon existence/uniqueness is not. |
| Lean destination | `SorinFiniteHorizonSingleton.lean` |
| Acceptance and consumer | Check horizon one and recursion, prove existence and uniqueness, and retain the landed uniform-payoff separation as a distinct theorem. |
| Discrepancies | Finite-horizon singleton does not provide one profile uniform across horizons. |

See [`30-counterexamples.md`](../../docs/uniform-equilibrium/references/30-counterexamples.md).
This is a benchmark and source-aligned formalization candidate, not a new route
to general existence.
