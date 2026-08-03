# Static stationary repair boundary

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `MINED` |
| Verdict | `MIXED` |
| Objective priority | `P1` |
| Last audited | 2026-08-03, generic API at `949689a`, grammar regression at `9f6614c`, and exact stationary repair at `bc86435` |
| Central live claim | Resolved: the narrow owner-plus-sure-set grammar fails uniformly on the calibrated table, but the table has an exact mixed stationary repair at hazards `(1/2,1,1/4)`. |
| Next discriminant | None internal to this table; retain it as a regression requiring any proposed static grammar to admit a sure quitter together with two independently mixed coordinates. |
| Production destination | Static-repair grammar regression and exact-stationary-repair example |
| Supersedes / superseded by | Refines the owner-solo and sure-set repair lane; no successor yet |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| SSR1 | A nonempty sure set plus one positive owner hazard has the stated two-atom payoff and exact behavioral unilateral cap; its cap inequalities are equivalent to terminal approximate Nash. | `PROVED` | `M+L+C` | `QuittingSureSetOwnerRepair`; fixed stationary grammar only. |
| SSR2 | The calibrated three-player table has an exact half-root Nash packet with value `(1,1,1/4)`, positive cutoff-one debt only for player zero, marked mass `1/4`, and marked owner advantage `3`. | `PROVED` | `M+L` | Regression input; does not optimize debt over roots. |
| SSR3 | On that table, every positive-hazard owner-zero/sure-set root, including the empty sure set, has terminal exploitability at least `1/3`. | `PROVED` | `M+L+C` | Exact exclusion of this grammar, not arbitrary stationary roots. |
| SSR4 | Every nonempty direct pure First profile on that table has terminal exploitability at least `1`. | `PROVED` | `M+L+C` | All seven nonempty quitter sets; no mixed-profile conclusion. |
| SSR5 | The infimum of terminal exploitability over all stationary product roots on the table is positive. | `WRONG` | `M+L+C` | Refuted by the exact stationary root in SSR6; no dynamic-architecture inference is available from this table. |
| SSR6 | The root with hazards `(1/2,1,1/4)` is exact terminal Nash, has payoff and exact cap `(1,3/4,1/2)`, and delivers that stationary uniform-equilibrium payoff. | `PROVED` | `M+L+C` | Full behavioral unilateral deviations; constant stationary repair, not merely an accuracy-indexed limiting chart. |

### Falsifiers and wrong turns

- The earlier three-player table does not refute full-rate repair: `{0,1}` is
  itself an exact direct First equilibrium. It remains a regression only for
  the vanishing-hazard rung.
- Failure of the `p → 0` inequalities does not exclude an interior or
  full-rate solution. SSR3 therefore quantifies over the complete positive
  interval before drawing its grammar-level conclusion.
- SSR3 and SSR4 do not imply SSR5. In fact the exact root
  `(1/2,1,1/4)` balances the same deviations while retaining a sure quitter
  and adding a second independently mixed coordinate. No vanishing-rate or
  exceptional-tail limit is needed.
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
full stationary hazard-cube discriminator         [resolved]
        +---- exact root (1/2,1,1/4)               [L+C]
        +---- claimed positive stationary gap      [WRONG]
```

### Exit conditions

- `MINED` is reached: SSR5 is refuted and the exact stationary repair is
  umbrella-routed at `bc86435`.
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
First profiles fail even more strongly. The full stationary discriminator is
also settled: mixed stationary hazards repair what every static support
endpoint and every one-owner/sure-set chart cannot.

The missing chart is elementary but genuinely outside the tested grammar:
player one quits surely while players zero and two mix independently with
hazards `1/2` and `1/4`. Its prescribed payoff and complete behavioral caps
are both `(1,3/4,1/2)`. Thus this example gives no reason to leave stationary
play; using it to motivate a dynamic lasso would be an overstatement.

No claim here concerns arbitrary behavioral profiles, private memory,
history-dependent punishments, or global nonexistence of uniform equilibrium.
