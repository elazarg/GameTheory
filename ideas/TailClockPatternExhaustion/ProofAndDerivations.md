# Tail clock-pattern exhaustion

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `MINED` |
| Verdict | `PROVED` |
| Objective priority | `P2` |
| Last audited | 2026-08-03, against the positive-debt tail, marginal-hazard domination, and Q128 closure |
| Central live claim | Resolved: once positive debt selects an owner with summable opponent clock, that owner's own hazard is either nonsummable, which is the closure branch, or summable, which forces every individual hazard and every opponent clock to be summable. No third clock pattern exists. |
| Next discriminant | none; reopen only if a later producer uses a clock notion not pointwise comparable to the landed opponent-absorption charge |
| Production destination | No independent producer. The resolved split is consumed by the fully summable exceptional branch in `ideas/PositivePlateauBoundaryClosure/README.md`. |
| Supersedes / superseded by | Superseded operationally by `ideas/PositivePlateauBoundaryClosure/README.md`; retained as the proof and terminology record for the exhausted split. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| TC1 | A positive exact dynamic-debt coordinate for owner \(i\) on the extracted projective tail forces summability of \(i\)'s additive opponent-absorption charge. | `PROVED` | `M+L+A` | `summable_clock_of_quittingDynamicDebtTail_pos` and the optimized-tail adapter. |
| TC2 | For every \(j\ne i\), the individual Quit hazard of \(j\) is pointwise bounded by \(i\)'s opponent-absorption charge and is therefore summable. | `PROVED` | `M` with landed inequality | `quittingProbability_le_opponentAbsorptionMass` supplies the pointwise bound; summable domination is elementary. |
| TC3 | Exactly two cases remain: owner \(i\)'s own hazard series is summable or it is not summable. | `PROVED` | `M` | Exhaustive classical split for one nonnegative real series. |
| TC4 | If owner \(i\)'s own hazard is nonsummable, then every other player's opponent clock is nonsummable, while \(i\)'s opponent clock remains summable. The Q128 exact-path argument closes this branch by an exact terminal Nash profile. | `PROVED` | `M` | The clock pattern follows by pointwise domination. Strategic closure additionally uses exact Bellman/Nash identities, bounded values, and the positive singleton endpoint; it is not a clock-only theorem. |
| TC5 | If owner \(i\)'s own hazard is summable, then every player's individual hazard is summable; consequently every player's additive opponent clock is summable. | `PROVED` | `M` | Finite-player union bound. This is the fully summable relative-boundary branch. |
| TC6 | A mixed pattern with owner-own hazard summable but some nonowner hazard divergent, or with some third playerwise opponent-clock status, cannot occur under TC1. | `PROVED` | `M` | Immediate from TC2--TC5. No re-rooting is needed. |

### Falsifiers and wrong turns

- **Do not conflate two clocks.** The selected owner has a summable
  *opponent* clock from the outset. The only unresolved scalar series is that
  owner's *own Quit hazard*. Once it is split into summable/nonsummable, the
  status of every remaining hazard and opponent clock is forced.
- **No \(2^{|I|}\) research lattice remains.** For a nonowner \(j\),
  \[
    h_j(t)\le p^{-i}(t),
  \]
  where \(p^{-i}(t)\) is the probability that at least one opponent of \(i\)
  Quits. Summability of the right side rules out a divergent nonowner hazard.
- **The reverse domination is used on the divergent branch.** For
  \(k\ne i\), owner \(i\) is one of \(k\)'s opponents, so
  \[
    h_i(t)\le p^{-k}(t).
  \]
  Nonsummability of \(h_i\) therefore forces nonsummability of every
  \(p^{-k}\).
- **All individual hazards summable implies all opponent clocks summable**
  only because the player set is finite:
  \[
    p^{-k}(t)\le\sum_{j\ne k}h_j(t).
  \]
- **Clock classification is not value compatibility.** TC5 identifies the
  exceptional branch but does not make its relative boundary attainable,
  sustainable, or strategically credible. Q130's vanishing-scale escape and
  the corrected two-ended packet remain valid fences.
- **Clock divergence alone does not prove equilibrium.** TC4's strategic
  closure also needs the supplied exact Bellman/Nash path and the positive
  singleton boundary for the sole player whose opponents may survive
  forever.

### Production map

```text
positive exact debt for owner i
        |
        v
sum_t p^{-i}(t) < infinity                                      [L]
        |
        +---- h_j(t) <= p^{-i}(t), j != i
        |            |
        |            v
        |      every nonowner hazard is summable                 [M]
        |
        v
split sum_t h_i(t)
        |
        +---- nonsummable
        |        |
        |        +---- h_i(t) <= p^{-k}(t), k != i
        |        |            -> every other opponent clock diverges
        |        |
        |        +---- exact path + positive singleton endpoint
        |                     -> exact terminal Nash              [M]
        |
        +---- summable
                 |
                 +---- all individual hazards summable
                 +---- all opponent clocks summable               [M]
                              |
                              v
                 fully summable relative-boundary producer        [P0 open]
```

### Landed ingredients

- `QuittingDynamicDebtProjectiveTail.lean` supplies TC1 through
  `summable_clock_of_quittingDynamicDebtTail_pos`.
- `QuittingMarkedTimeAdvance.lean` supplies both pointwise
  marginal-to-opponent-clock comparisons through
  `quittingProbability_le_opponentAbsorptionMass`.
- `QuittingOpponentClockDichotomy` converts nonsummable additive charge to
  vanishing multiplicative opponent survival and supplies the complementary
  positive-survival suffix.
- `QuittingNashBellmanValueConvergence` supplies finite variation and value
  convergence on a summable opponent clock.
- The Q128 divergent-own-clock argument supplies TC4's strategic closure at
  mathematical status. Its ingredients are reusable; this group does not
  claim a new all-pattern producer.

### Optional production cleanup

If a consumer would become materially shorter, one small synthesis theorem may
package TC2--TC5:

> Given a finite root path and owner \(i\) with summable opponent charge,
> either \(i\)'s own hazards are summable and all playerwise opponent charges
> are summable, or \(i\)'s own hazards are nonsummable and every other
> player's opponent charge is nonsummable.

This is consolidation, not open mathematics and not a reason to keep the idea
group active. The strategic exact-Nash closure should remain a separate
theorem because it consumes Bellman and payoff hypotheses absent from this
pure clock lemma.

### Exit conditions

- The group is `MINED` now: the proposed mixed-pattern search was based on
  overlooking the two pointwise domination inequalities.
- Reopen only if the main producer changes to a clock not comparable to
  one-stage opponent-absorption mass, or if infinitely many players are
  admitted.
- The fully summable branch remains `OPEN` in its P0 owner; that is a
  boundary-attainability and strategic-decoder problem, not an unclassified
  clock pattern.
