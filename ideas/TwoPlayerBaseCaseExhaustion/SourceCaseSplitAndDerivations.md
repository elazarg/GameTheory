# Two-player base case: stationary approximate equilibria

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `PROVED` |
| Objective priority | `P1` |
| Last audited | 2026-08-03, against the six-scalar case split of Solan--Vieille §2.1, the full-rate stationary verifier, and Q132's exact-nonattainment regression |
| Central live claim | Every standard two-player quitting game admits a stationary terminal ε-equilibrium for every ε > 0. The mathematics is known; the active work is a direct six-scalar Lean formalization and terminal-to-uniform consumer. |
| Next discriminant | Formalize the exhaustive pure-profile/no-pure-profile case split, reusing the landed pair-repair branch and adding the complementary vanishing owner-solo approximation. |
| Production destination | `QuittingTwoPlayerStationaryExistence.lean`, then `QuittingTerminalUniformPayoffSelection`. |
| Supersedes / superseded by | Supersedes this file's proposed S⁰ search and four-parameter scan; no successor. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| TP1 | For every reward table of a standard two-player quitting game and every ε > 0, some stationary product profile is terminal ε-Nash against arbitrary behavioral unilateral deviations. | `PROVED` | `M` | Classical two-player theorem; Solan--Vieille §2.1 gives the complete elementary case split and cites Flesch--Thuijsman--Vrieze (1996). |
| TP2 | A generic two-player terminal table has six payoff scalars: two coordinates at each of \(\{1\},\{2\},\{1,2\}\). There is no global four-parameter description without an explicit, case-valid normalization. | `PROVED` | `M` | Corrects the intake statement. Never payoff is fixed at zero, so translating terminal rewards alone is not harmless. |
| TP3 | If one of the four pure stationary profiles is exact terminal Nash, it closes the game. Otherwise, after possibly exchanging the players, the six scalars satisfy \(a_1>0\), \(a_2<d_2\), \(d_1<b_1\), and \(b_2<0\). | `PROVED` | `M` | Exhaustive linear-comparison reduction. Not yet packaged in Lean. |
| TP4 | In the no-pure orientation, if \(a_2\ge b_2\), player 1 using a sufficiently small positive stationary hazard while player 2 always Continues is terminal ε-Nash. | `PROVED` | `M` | Complementary vanishing owner-solo branch; E48 reduces its proof to one explicit cap inequality. |
| TP5 | In the no-pure orientation, if \(a_2<b_2\), player 1 using a sufficiently small positive stationary hazard while player 2 Quits surely is terminal ε-Nash. | `PROVED` | `M+L+C` | Already covered, up to naming and role orientation, by `QuittingTwoPlayerPairRepair`. |
| TP6 | Two-player stationary approximate equilibria imply a uniform-equilibrium payoff through compact payoff selection and terminal-to-uniform transfer. | `PROVED` | `M` | The generic semantic consumer is landed, but the all-table stationary producer and its adapter are not yet in Lean. |
| TP7 | Every two-player quitting game has an exact stationary, or even exact behavioral, terminal equilibrium. | `WRONG` | `M` | Q132 gives a two-player table with no exact behavioral terminal Nash equilibrium although stationary exploitability tends to zero. |

### Falsifiers and wrong turns

- **The parameter count is six, not four.** Write
  \[
    a=r(\{1\})=(a_1,a_2),\qquad
    b=r(\{2\})=(b_1,b_2),\qquad
    d=r(\{1,2\})=(d_1,d_2).
  \]
  The all-Continue/Never payoff is zero by the standard convention. Positive
  rescaling per player preserves incentives, but no single normalization
  removes two coordinates across zero and sign-degenerate cases without
  changing the theorem's case split.
- **Stationary sufficiency is not conjectural at two players.** A primary
  source gives the explicit proof; a search for a rational table surviving
  every stationary profile is therefore aimed at refuting a known theorem.
- **Do not strengthen approximate to exact.** In the Q132 table,
  \(\inf_x\operatorname{Expl}_{\rm stat}(x)=0\), but no exact behavioral
  equilibrium exists. Accuracy-indexed hazards are essential.
- **The result is stronger than a Never/First/stationary disjunction.** The
  stationary branch alone is universal. Never and pure First appear as pure
  subcases but are not separate completeness obligations.
- **E48 is a verifier, not the producer.** It turns each candidate profile
  into exact all-behavior cap inequalities. The six-scalar case split and the
  choice of a sufficiently small hazard still need to be formalized.
- **The positive-debt pair repair is not by itself an all-table proof.** It
  supplies TP5. TP4 and the pure/symmetry reduction are the missing pieces.
- **No player-count induction follows.** Three-player cyclic behavior shows
  that the two-player stationary theorem is a base case, not an induction
  backbone.

### Production map

For the oriented table
\[
  a=r(\{1\}),\qquad b=r(\{2\}),\qquad d=r(\{1,2\}),
\]
the known proof has the following finite shape.

```text
six-scalar reward table
        |
        +---- one of four pure stationary profiles is exact Nash
        |                  |
        |                  v
        |             exact terminal Nash
        |
        +---- no pure stationary Nash
                  |
                  +---- orient players so a_1 > 0
                  |
                  +---- derive a_2 < d_2, d_1 < b_1, b_2 < 0
                  |
                  +---- compare a_2 and b_2
                         |
                         +---- a_2 >= b_2
                         |       profile (h, 0), h -> 0+
                         |       full-rate cap error -> 0          [? -> L]
                         |
                         +---- a_2 < b_2
                                 profile (h, 1), h -> 0+
                                 pair-repair error -> 0             [L]
                                           |
                                           v
                         stationary terminal eps-Nash for all eps
                                           |
                                           v
                             uniform-equilibrium payoff             [L+C]
```

### Exact no-pure reduction

The payoff matrix is
\[
\begin{array}{c|cc}
 & C_2 & Q_2\\ \hline
C_1 & (0,0) & b\\
Q_1 & a & d .
\end{array}
\]
If \(a_1\le0\) and \(b_2\le0\), \((C_1,C_2)\) is exact Nash. Hence absence
of a pure equilibrium gives \(a_1>0\) or \(b_2>0\); exchange players and
assume \(a_1>0\).

Now:

1. if \(a_2\ge d_2\), then \((Q_1,C_2)\) is exact Nash, so no-pure implies
   \(a_2<d_2\);
2. under \(a_2<d_2\), if \(d_1\ge b_1\), then \((Q_1,Q_2)\) is exact Nash,
   so no-pure implies \(d_1<b_1\);
3. under \(d_1<b_1\), if \(b_2\ge0\), then \((C_1,Q_2)\) is exact Nash, so
   no-pure implies \(b_2<0\).

These are the only reductions. No direction-flow or stationary-root
compactification is needed.

### The two approximation branches

For \(h\in(0,1)\), consider first \(x=(h,0)\): player 1 Quits with
probability \(h\) at every live date and player 2 always Continues. The
profile absorbs almost surely at \(\{1\}\), so its payoff is \(a\). Player
1's exact cap is \(\max\{0,a_1\}=a_1\). Player 2's exact cap is
\[
  \max\left\{
    a_2,\ (1-h)b_2+h d_2
  \right\}.
\]
When \(a_2\ge b_2\), its regret tends to zero with \(h\). This proves TP4.

For \(x=(h,1)\), player 2 Quits surely, so absorption occurs at the first
stage and the prescribed payoff is
\[
  (1-h)b+h d.
\]
Player 1's cap is \(b_1\), and its regret is
\[
  h(b_1-d_1)\longrightarrow0.
\]
Player 2's cap is the maximum of its prescribed payoff and \(a_2\). When
\(a_2<b_2\), the prescribed payoff exceeds \(a_2\) for all sufficiently
small \(h\). This is TP5 and is already subsumed by the landed pair-repair
module.

The cap formulas quantify over arbitrary behavioral deviations, not merely
one-stage deviations.

### Sources and production reuse

- Eilon Solan and Nicolas Vieille, *Quitting games -- an example*,
  International Journal of Game Theory 31 (2002), §2.1, gives the displayed
  two-player proof and states that every two-player quitting game has a
  stationary ε-equilibrium:
  [author PDF](https://www.math.tau.ac.il/~eilons/notequitting4.pdf).
- That paper cites J. Flesch, F. Thuijsman, and K. Vrieze,
  *Recursive repeated games with absorbing states*, Mathematics of Operations
  Research 21 (1996), 1016--1022, for the original result.
- Reuse `QuittingFullRateStationaryVerifier` for arbitrary-deviation caps,
  `QuittingTwoPlayerPairRepair` for TP5 and role reversal, and
  `QuittingTerminalUniformPayoffSelection` for TP6.

### Missing production arrows

1. Package the four pure stationary profiles and prove the three strict
   inequalities in the no-pure orientation.
2. Add the TP4 owner-solo approximate family with an explicit error bound and
   a role-parametric version.
3. Assemble TP4, the existing TP5 pair repair, pure profiles, and role
   reversal into
   \[
     \forall\varepsilon>0,\ \exists x\text{ stationary},\
       x\text{ is terminal }\varepsilon\text{-Nash}.
   \]
4. Apply the landed terminal-payoff selection theorem to expose a
   two-player uniform-equilibrium payoff capstone.
5. Protect the exact-versus-approximate boundary with Q132's nonattainment
   table and the off-chain stationary Q125 table.

### Exit conditions

- Mark `MINED` after the all-table stationary theorem and its
  terminal-to-uniform consumer are in production.
- Mark `BLOCKED` only on a named mismatch between the literature's standard
  quitting payoff convention and the repository's terminal-payoff semantics;
  E48 should make that adapter direct.
- Do not reopen the S⁰ rotation search or a stationary counterexample scan:
  the mathematical claim they were meant to decide is already proved.
- Do not mark TP7 proved even if the compactified stationary objective attains
  a relaxed zero; Q132 shows why exact attainment can fail.
