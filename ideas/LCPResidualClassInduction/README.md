# LCP residual class and subgame induction

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `OPEN` |
| Objective priority | `P0` |
| Last audited | 2026-08-04 |
| Central live claim | The open range of the finite-quitting conjecture is exactly the weights whose normalized solo matrix `M` is a `Q`-matrix but not a `Q̄`-matrix, and on that class an induction on the number of players is available through a gluing step that is stated in the literature only as a remark. |
| Next discriminant | Prove or refute the gluing lemma: a sequentially `0`-perfect object for the `J`-subgame, along which every player outside `J` receives a non-negative payoff, is sequentially `0`-perfect for the whole game. |
| Production destination | `none yet` |
| Supersedes / superseded by | complements the absorption-path carrier of [`AbsorbingCycleCarrier`](../AbsorbingCycleCarrier/README.md); does not supersede it |

## Why this group exists

Two published sufficient conditions cover the finite-quitting problem from
opposite sides, and until now the repository recorded only one of them. Put
together they leave a **finite, algebraically stated residual class**, which is
a much sharper description of what is open than anything the program had.

Write `M_{ij} := r_i({j}) − r_i({i})` for the normalized solo matrix: row `i`
is the payoff receiver, column `j` the sole quitter, and the diagonal is zero.
`M` is the matrix `R(Γ)` of Ashkenazi-Golan–Krasikov–Rainer–Solan after their
standing normalization, transported into the repository's model (never-terminate
payoff `0`) by adding the constant `−r_i({i})` to every payoff of player `i` —
which preserves every player's incentives exactly. Details and the audit of
that transport:
[`QBarMatrixQuittingGamesHaveContinuousEquilibria`](../UniformEquilibriumLiterature/QBarMatrixQuittingGamesHaveContinuousEquilibria.md).

Then:

- `M` **not** a `Q`-matrix ⟹ a stationary approximate equilibrium
  (Solan–Solan 2020, at the audited scope in
  [`NonQQuittingGamesHaveUniformApproximateEquilibria`](../UniformEquilibriumLiterature/NonQQuittingGamesHaveUniformApproximateEquilibria.md)).
- `M` a `Q̄`-matrix — itself and every principal minor a `Q`-matrix — ⟹ a
  continuous equilibrium (AGKRS Theorem 5.4).
- Residual: **`M` is a `Q`-matrix and some proper principal submatrix `M_J`
  is not.**

That residual is the whole open problem, for `n ≥ 4`. At `n ≤ 3` everything is
settled independently — Solan, *Three-player absorbing games*, Math. Oper. Res.
**24**(3), 669–698 (1999), recorded at
[`ThreePlayerAbsorbingGamesHaveUniformEquilibria`](../UniformEquilibriumLiterature/ThreePlayerAbsorbingGamesHaveUniformEquilibria.md),
whose conclusion is *undiscounted* and whose upgrade to *uniform* is sourced
separately. That record is `SECONDARY_VERIFIED`, primary text unread — and this
group's C1 has no meaning without it, so it is C1's largest single exposure.

> ⚠ **Two gates on the `Q̄` half, neither discharged here.** Theorem 5.4
> delivers a *continuous equilibrium*; reaching "`ε`-equilibria for every `ε`"
> from it runs through AGKRS Theorem 4.15, whose definitional endpoint
> (Definition 4.13, `SP.1`) is recorded as **defective** in
> [`20-nonzero-sum-equilibrium.md`](../../docs/uniform-equilibrium/references/20-nonzero-sum-equilibrium.md)
> and [`SourceCorrections-QuittingAbsorptionPaths.md`](../../docs/uniform-equilibrium/references/SourceCorrections-QuittingAbsorptionPaths.md),
> which say the source theorem must not be used as a literal
> path/nonexistence equivalence until a repaired bridge is proved. Theorem
> 4.15 is also *stated* under a hypothesis its converse proof does not use.
> Both gates are described in
> [`QBarMatrixQuittingGamesHaveContinuousEquilibria`](../UniformEquilibriumLiterature/QBarMatrixQuittingGamesHaveContinuousEquilibria.md).
> So C1's containment is **not currently supported end to end**: it is a
> containment of the open range in the residual class *modulo* those two
> gates plus Solan–Solan's audited scope. Discharge them or downgrade C1;
> do not quote C1 as established.

## Contents

- [`TheGluingStepIsOnlyARemark.md`](TheGluingStepIsOnlyARemark.md) — the
  subgame-to-whole-game step, its exact statement, and why it is the rung to
  build next.
- [`TheInspirationDigraphIsProbablyTheSignDigraph.md`](TheInspirationDigraphIsProbablyTheSignDigraph.md)
  — Simon's cycle-structure theory for counterexamples, the digraph
  infrastructure the repository already has, and the identification that would
  make the residual class combinatorial.

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| C1 | The open range of the finite-quitting conjecture is contained in `{M : M is Q, some proper principal minor of M is not Q}`. | `OPEN` — **conditional on three named gates**, see the warning above | `I` | Finite quitting games, `n ≥ 4`; `ε`-equilibria for every `ε > 0`. | The conjecture. |
| C2 | **Gluing.** If `π` is sequentially `0`-perfect for the `J`-subgame (players outside `J` always continue) and every `i ∉ J` has non-negative payoff along `π`, then `π` is sequentially `0`-perfect for `Γ`. | `OPEN` | `I` | As stated. | C3, and the induction. | 
| C3 | On the residual class, an induction on `|I|` closes the conjecture unless, for every proper `J` with `M_J` not `Q`, every solution of the `J`-subgame leaves some outsider strictly negative. | `OPEN` | `I` | As stated. | The conjecture, or a sharply described obstruction. |
| C4 | That last corner is nonempty. | `OPEN` | `I` | As stated. | If empty, C3 closes the conjecture; if nonempty, its witnesses are counterexample candidates. |

C2 is asserted in AGKRS's Remark 5.5(1) in the course of explaining why
Theorem 5.4 is not tight: *"it may further happen that the players not in `J`
obtain non-negative payoffs along this AP. In such a case, all players are
sequentially `0`-perfect at `π`."* It is a remark, not a numbered result, and
carries no proof. It is exactly the kind of borrowed step this program has been
burned by, and it is also the cheapest genuinely new rung available.

## Falsifiers and wrong turns

- **C1 fails** if Solan–Solan's theorem does not apply at the scope claimed.
  The audited scope correction is real: the literal theorem carries two extra
  hypotheses and the unconditional reading is a synthesis of three results.
  Any use of C1 must discharge all three cases, and must not silently upgrade
  a *stationary undiscounted* conclusion to a *uniform* one.
- **C2 fails** if a player outside `J`, having a non-negative payoff along `π`,
  can still profit — for instance by quitting at a moment that changes what the
  players inside `J` face. Test this before building on it. A single explicit
  four-player weight settles it either way.
- Do **not** conclude from `M_J` not being a `Q`-matrix that the `J`-subgame's
  solution is *stationary in the whole game*; the outsiders' continuation is
  part of the object being glued.
- Do **not** treat `M` as carrying the whole weight. `M` is built from the
  singleton rows only; the multi-quitter rows are invisible to it. That is a
  feature for continuous equilibria, which put no mass on simultaneous quits,
  and a trap for anything else — including every finite-cycle and inverse-iterate
  question, where the pair rows matter.

## Production map

```text
AGKRS Thm 5.4 + Solan--Solan  ->  residual class C1
                              ->  gluing lemma C2 (formalize)
                              ->  induction on |I| C3
                              ->  conjecture, or the corner C4 as a search target
```

## Exit conditions

`MINED` when C2 is decided and C3's corner is either shown empty or given an
explicit witness.
