# Static stationary repair boundary

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `MIXED` |
| Objective priority | `P0` |
| Last audited | 2026-08-03, generic API at `949689a` and full-interval regression at `9f6614c` |
| Central live claim | Determine whether the calibrated three-player table has stationary terminal exploitability bounded away from zero over the entire hazard cube, including all faces and vanishing-rate charts. |
| Next discriminant | Minimize the exact stationary unilateral-cap gaps over `[0,1]^3`, resolving zero-survival faces separately; either exhibit an accuracy-indexed stationary repair and its asymptotic support/scale or certify a positive global gap. |
| Production destination | Stationary quitting-game boundary discriminator, then the dynamic-lasso producer if the stationary gap is positive |
| Supersedes / superseded by | Refines the owner-solo and sure-set repair lane; no successor yet |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| SSR1 | A nonempty sure set plus one positive owner hazard has the stated two-atom payoff and exact behavioral unilateral cap; its cap inequalities are equivalent to terminal approximate Nash. | `PROVED` | `M+L+C` | `QuittingSureSetOwnerRepair`; fixed stationary grammar only. |
| SSR2 | The calibrated three-player table has an exact half-root Nash packet with value `(1,1,1/4)`, positive cutoff-one debt only for player zero, marked mass `1/4`, and marked owner advantage `3`. | `PROVED` | `M+L` | Regression input; does not optimize debt over roots. |
| SSR3 | On that table, every positive-hazard owner-zero/sure-set root, including the empty sure set, has terminal exploitability at least `1/3`. | `PROVED` | `M+L+C` | Exact exclusion of this grammar, not arbitrary stationary roots. |
| SSR4 | Every nonempty direct pure First profile on that table has terminal exploitability at least `1`. | `PROVED` | `M+L+C` | All seven nonempty quitter sets; no mixed-profile conclusion. |
| SSR5 | The infimum of terminal exploitability over all stationary product roots on the table is positive. | `OPEN` | `I` | Full stationary cube, with exceptional all-continue/zero-rate faces treated semantically. |
| SSR6 | If SSR5 is false, an explicit accuracy-indexed stationary repair has a finite asymptotic support/scale chart that can be used by the producer. | `OPEN` | `I` | Constructive alternative to the positive-gap branch. |

### Falsifiers and wrong turns

- The earlier three-player table does not refute full-rate repair: `{0,1}` is
  itself an exact direct First equilibrium. It remains a regression only for
  the vanishing-hazard rung.
- Failure of the `p → 0` inequalities does not exclude an interior or
  full-rate solution. SSR3 therefore quantifies over the complete positive
  interval before drawing its grammar-level conclusion.
- SSR3 and SSR4 do not imply SSR5. A mixed root with no sure quitter may
  balance the same deviations, and a vanishing multi-rate chart may converge
  through a face not represented by one owner plus sure quitters.
- A numerical minimum away from cube faces cannot establish SSR5. Every face,
  relative vanishing-rate direction, and the exceptional all-continue tail
  must be resolved analytically or by a certified exhaustive reduction.

### Production map

```text
exact debt packet and marked atom                 [L]
        |
        v
generic sure-set/owner exact-cap iff              [L+C]
        |
        v
full-interval owner+sures obstruction             [L+C]
        +---- direct pure First exhaustion         [L+C]
        |
        v
full stationary hazard-cube optimization          [?]
        +---- infimum zero --> asymptotic chart    [? -> producer]
        +---- positive gap --> dynamic lasso needed[? -> discriminator]
```

### Exit conditions

- Mark `MINED` when SSR5 is proved or refuted and the resulting stationary
  chart/gap is routed to its next producer or discriminator.
- Mark `PARKED` only if the dynamic architecture independently subsumes every
  stationary boundary chart and no stationary classification is needed by a
  downstream proof.
- Mark SSR5 `WRONG` immediately upon a proved stationary family whose exact
  exploitability tends to zero; retain its support and scale as SSR6 data.
- Mark `SUPERSEDED` only when another group owns both the full stationary
  classification and the interface to dynamic repair.

## Objective and current boundary

The owner-plus-sure-set grammar is now an exact, semantic verifier rather than
a heuristic. On the calibrated table it fails uniformly, and all direct pure
First profiles fail even more strongly. This isolates the next honest
question: whether mixed stationary hazards can repair what every static
support endpoint and every one-owner/sure-set chart cannot.

The distinction matters. A positive full-cube gap would be a genuine reason
to leave stationary play and study finite-memory or time-inhomogeneous
architectures. A zero infimum would instead expose the missing stationary
boundary chart and should be mined before adding dynamic machinery.

No claim here concerns arbitrary behavioral profiles, private memory,
history-dependent punishments, or global nonexistence of uniform equilibrium.
