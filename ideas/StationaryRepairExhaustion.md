# Stationary repair exhaustion: exact verifier to gap-or-escape

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `MIXED` |
| Objective priority | `P1` |
| Last audited | 2026-08-03, through E39, E44--E45, E48, and the corrected Q132 nonattainment theorem |
| Central live claim | The full stationary-product layer has an exact infimum dichotomy: zero infimum gives accuracy-indexed stationary terminal equilibria, while positive infimum gives a uniform typed stationary obstruction. A compactified zero is an escape family, not necessarily an attained stationary equilibrium. |
| Next discriminant | Formalize the actual-profile gap functional and its zero-or-positive-infimum consumer; then determine whether a finite scale/direction graph compactification can describe and synthesize every zero escape without adding spurious relaxed zeros. |
| Production destination | `QuittingStationaryRepairGap` consuming `QuittingFullRateStationaryVerifier` and terminal-to-uniform payoff selection; negative-route stationary filter. |
| Supersedes / superseded by | Supersedes the naive attained-root SR5 formulation in this file; no successor. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| SR1 | For every stationary product profile, the full-rate unilateral cap is the exact supremum over arbitrary behavioral deviations. Its pointwise cap inequalities are equivalent, for every error, to terminal approximate Nash. | `PROVED` | `M+L+C` | `QuittingFullRateStationaryVerifier`. Verification of supplied stationary data; no root construction or search. |
| SR2a | Positive exact dynamic debt for a fixed owner yields either that owner's solo payoff as a uniform-equilibrium payoff or a universal joining obstruction at every positive owner hazard. | `PROVED` | `M+L+C` | E39 and `QuittingOwnerSoloCertification`. |
| SR2b | Ownerwise assembly gives either some solo uniform payoff or the universal joining obstruction for every positive-debt owner in every admissible finite chain. | `PROVED` | `M+X` | E39's experiment extension; not E49, which is the two-ended compactification. |
| SR3a | A universal constant-rate joining obstruction yields a strict stagewise joiner at every positive date of every owner-hazard sequence. | `PROVED` | `M+X` | E39's scalar transfer kernel. It does not itself prove a profitable global deviation. |
| SR3b | Every exact time-varying owner-solo terminal equilibrium induces a certifying constant owner hazard. | `OPEN` | `I` | Would make the universal joining obstruction exhaustive over the full owner-solo behavior class; the global payoff comparison is missing. |
| SR4 | First scale/direction coordinates and the singleton-reward direction-barycenter estimate describe stationary payoffs to first order at zero total hazard. | `PROVED` | `M+X` | E44--E45. No cap continuity, Nash transfer, or hierarchical-scale completeness follows. |
| SR5 | On a compactified stationary family, an attained zero minimum of the relaxed cap violation implies that some actual stationary profile is an exact terminal equilibrium. | `WRONG` | `M` | Refuted by Q132's two-player nonattainment table: actual stationary exploitability tends to zero, but no exact behavioral, hence no exact stationary, equilibrium exists. |
| SR6 | Let `g_r(x)` be maximum full-rate unilateral regret at the actual stationary product profile `x` and `δ_stat = inf_x g_r(x)`. Exactly one of the following holds: `δ_stat = 0`, giving actual stationary terminal ε-equilibria for every ε > 0; or `δ_stat > 0`, giving a uniform stationary exploitability gap. | `PROVED` | `M` | Elementary infimum alternative plus SR1. The zero branch is accuracy-indexed and need not be attained. |
| SR7 | Closing the graph of the bounded objective `x ↦ g_r(x)` in a compact ambient product gives an attained relaxed minimum equal to `δ_stat`. A zero boundary minimizer is the limit of actual profiles with regret tending to zero, not an actual root. | `PROVED` | `M` | Honest existential compactification; opaque as a synthesis device. |
| SR8 | A finite, explicitly described scale/direction compactification, possibly iterated on simplex faces, represents the graph closure of all relevant caps and has no relaxed zero without an actual vanishing-regret stationary sequence. | `OPEN` | `I` | The useful constructive replacement for the false SR5. First-scale barycenters alone do not establish it. |
| SR9 | If `δ_stat > 0`, then every actual stationary profile has some player with regret at least `δ_stat`, and that witness has one of E48's two exact regime labels: contracting opponents or saturated opponents. | `PROVED` | `M` | The witnessing player and regime may vary with the profile; no single global player is claimed. |

### Falsifiers and wrong turns

- **Q132 refutes attained zero, not the infimum dichotomy.** For
  \[
  r(\{1\})=(1,-1),\qquad
  r(\{2\})=(-1,-1),\qquad
  r(\{1,2\})=(-2,0),
  \]
  the stationary profiles \(x(a)=(a,2/3)\) have maximum terminal regret
  \(a^2/(a+2)\to0\), while the game has no exact behavioral terminal Nash
  equilibrium. Thus \(\delta_{\rm stat}=0\) without an attaining actual
  profile.
- **A relaxed zero is not a root.** At the limiting actual profile
  \(x(0)=(0,2/3)\), the full-rate cap switches to the saturated-opponents
  regime and the regret is positive. A boundary chart may retain the
  approaching contracting-regime value, but it then represents an escape
  direction rather than the strategy \(x(0)\).
- **Semicontinuity in the naive cube fails in the needed direction.** The
  preceding sequence has regret tending to zero while the limiting actual
  profile has larger regret. Compactness of the profile cube therefore does
  not turn the infimum into an exact equilibrium.
- **First scale need not be a complete atlas.** E44 explicitly retains only
  leading scale/direction; rates inside a limiting simplex face may require
  iterated scales. No finite hierarchy has yet been proved exhaustive for the
  cap graph.
- **Do not call arbitrary stationary profiles roots.** E48 verifies every
  stationary product profile directly. Complementarity or a separately
  supplied Bellman root is not an input to its terminal-Nash equivalence.
- **Q125 separates stationary repair from exact-D chain repair.** Its
  stationary certificate closes at rate \(1/2\) although optimized
  zero-boundary chain debt stays positive. Neither optimization subsumes the
  other.
- **Positive \(\delta_{\rm stat}\) is only a strategy-class exclusion.**
  Cyclic, time-inhomogeneous, or general behavioral terminal equilibria remain
  possible. It is not a counterexample to quitting-game existence.
- **A fixed witness player is not automatic.** Finiteness gives a maximizing
  player at each profile and a constant label along selected subsequences,
  not one player witnessing the gap on the entire stationary cube.
- A proposed explicit compactification is falsified if it admits a zero
  point not approximable by actual stationary profiles with vanishing
  regret, or if an actual vanishing-regret sequence has no convergent
  representation.

### Production map

```text
actual stationary product profile x
        |
        v
terminal payoff u(x) + exact full-rate behavioral caps c_i(x)       [L, E48]
        |
        v
g_r(x) = max_i max(0, c_i(x) - u_i(x))
        |
        +---- inf g_r = 0 ----> stationary terminal eps-Nash
        |                       for every eps > 0                    [M -> L]
        |                                  |
        |                                  v
        |                       uniform-equilibrium payoff           [L+C]
        |
        +---- inf g_r > 0 ----> uniform typed stationary gap         [M -> L]

graph closure of (x, g_r(x))                                        [M]
        |
        +---- zero boundary point --> actual vanishing-regret sequence
        |
        +---- positive minimum ----> same typed stationary gap

scale/direction and barycenter charts                               [X, E44--E45]
        |
        v
explicit finite graph compactification / synthesis                  [?]

positive-debt owner --> solo payoff or universal joining obstruction [L, E39]
```

### Landed and experimental artifacts

- `QuittingFullRateStationaryVerifier`: exact cap and terminal-Nash
  equivalence for arbitrary stationary product profiles.
- `QuittingStationaryBestResponse`: contracting-opponents Snell cap.
- `QuittingOwnerSoloCertification`: per-owner positive-debt refinement;
  E39 additionally checks ownerwise assembly and the stagewise kernel.
- E44 `HazardScaleDirectionBlowup.lean` and E45
  `QuittingDirectionBarycenter.lean`: first-scale payoff chart only.
- `QuittingTerminalUniformization` and
  `QuittingTerminalUniformPayoffSelection`: semantic consumer of the
  zero-infimum branch.
- E49 is deliberately absent from this lane: it is
  `TwoEndedDynamicDebtCompactification.lean` and belongs to the
  positive-plateau bridge/holonomy producer.

### Missing production arrows

1. Define the nonnegative finite-player regret functional from E48's exact
   caps and actual terminal payoff.
2. Formalize SR6, including the approximation extraction from infimum zero
   and the terminal-to-uniform consumer. This is a short theorem, not a
   compactness argument.
3. Formalize SR9 as a typed negative object usable by stationary-search and
   counterexample filters.
4. If an explicit stationary synthesis layer is still useful, define its
   compactification as a closure of realizable graph data or prove a decoder
   from every relaxed point. Never identify its base-point projection with an
   actual profile's cap.
5. Prove or refute SR3b before claiming that E39 exhausts time-varying
   owner-solo behavior.

### Exit conditions

- Mark `MINED` once SR6/SR9 and their terminal-to-uniform consumer are in
  production and either SR8 has an explicit synthesis consumer or is
  deprioritized as an opaque stationary search problem.
- Mark SR8 `WRONG` only with an actual vanishing-regret sequence escaping
  every proposed finite chart, or a chart zero that cannot be decoded to such
  a sequence.
- Mark `PARKED` if stationary synthesis ceases to be on the shortest P0
  route after the exact gap/escape theorem lands.
- Mark `SUPERSEDED` if another group owns both the full-rate stationary
  objective and its positive-gap/zero-escape consumers.
- Never mark the quitting-game conjecture refuted from the positive branch of
  SR6 alone; that requires a gap over every behavioral profile.

## Exposition

### 1. The exact functional lives on profiles, not supplied roots

For a stationary product profile \(x\), write \(u_i(x)\) for its actual
terminal payoff and \(c_i(x)\) for E48's full-rate unilateral cap. Define
\[
g_r(x)=\max_i\max\{0,c_i(x)-u_i(x)\}.
\]
The extra maximum with zero is harmless and makes nonnegativity syntactic.
E48 says exactly that \(g_r(x)\le\varepsilon\) is terminal
\(\varepsilon\)-Nash against every behavioral unilateral deviation.

The profile domain is nonempty and \(g_r\) is bounded below by zero and above
by a finite reward-dependent constant. Hence
\[
\delta_{\rm stat}=\inf_x g_r(x)
\]
exists. If it is zero, the definition of infimum supplies, for every
\(\varepsilon>0\), an actual stationary profile with
\(g_r(x)<\varepsilon\). If it is positive, every stationary profile has gap
at least \(\delta_{\rm stat}\). This is the complete existential
stationary-class split. It needs no minimizer.

### 2. What compactification can honestly add

Although \(x\) ranges over a compact cube, \(g_r\) need not attain its
infimum because terminal payoff and the full-rate cap change regime at
zero absorption. The safe compactification is the closure of the graph
\[
\Gamma_r=\{(x,g_r(x)):x\text{ is an actual stationary product profile}\}
\]
inside a bounded compact product. The second-coordinate minimum on
\(\overline{\Gamma_r}\) is attained and equals \(\delta_{\rm stat}\).
Every zero point in that closure is, by definition, approached by actual
vanishing-regret profiles.

This construction is existentially exact but may be algorithmically opaque.
Scale/direction coordinates are valuable only if they describe the relevant
graph fibers and preserve realizability. At a singular base profile they may
carry several limiting cap values. Those are distinct boundary directions,
not contradictory values of one actual strategy.

### 3. The useful negative object

On the positive branch, finite-player maximization gives at each profile a
player whose regret is at least \(\delta_{\rm stat}\). E48 then types that
witness as either:

1. contracting opponents, where the Snell cap applies; or
2. saturated opponents, where every opponent is pure Continue and the exact
   cap is the maximum of Never and immediate solo Quit.

This is a quantitative stationary search certificate and a useful filter for
candidate barrier tables. The witness may rotate with the profile, and the
certificate excludes only stationary products.

### 4. Relation to the positive-debt lane

E39 is orthogonal but complementary. Positive dynamic debt selects a specific
owner and yields either an owner-solo uniform payoff or a joining obstruction
at every owner hazard. SR6 instead ranges over every stationary product
profile and either supplies stationary approximations or excludes that whole
strategy class by a positive gap.

The lanes meet only through a producer: E39 can suggest which stationary
faces to search first, while SR6 certifies whether all stationary faces have
actually been exhausted. E49 does not belong to this stationary assembly; it
retains the separate forward and reverse ends of optimized exact-D chains for
the P0 boundary/holonomy problem.
