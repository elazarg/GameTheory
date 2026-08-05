# Exact-cycle strata carry the relaxed families

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity mixed by leg (see ledger), P0-adjacent | NumericalAnalysis intake, E64–E67, Q154/Q156/Q158 wings | `MATH-P0-9` (lock/unlock), `MATH-P0-5/6` (the hole), P13 search | a relaxed family whose backward distance decouples from its defect, or the three-lens identity failing |

## The frame

In the space of weights, let `Σ_L` be the set admitting an exact cycle of
period `L` — semialgebraic per fixed `L`. Backward error analysis reads every
relaxed cycle as an exact cycle of a *nearby* weight, so the exact-vs-relaxed
program becomes **metric**: relaxed families exist at tolerance `δ` exactly
insofar as strata pass within backward distance `~δ`, and the minimal-period
law `d(ε,δ)` is the index of the first stratum within reach. Existential
questions about cycles become quantitative questions about stratum geometry.

## Ledger

- **(S1) `L` (E64, experiments lane).** The base case is a theorem: every
  `ε`-complementary row is exactly complementary for a table within
  `C·ε`, via the per-player own-set shift, with the condition number
  explicit: `C = 1/min(yᵢ, 1−yᵢ)` over interior coordinates, `C = 1` at pure
  rows. **Fixed tail only** — the cycle-feedback case is open and is the
  lens's genuine frontier (the same fixed-rows-versus-optimized split the
  seam-price law had; expect the middle leg to be the hard one).
- **(S2) `X` (E65).** On the `Γ_η` period-`3m` family: defect tracks
  `η·log2/(3m)`; the best single own-set shift leaves **exactly half** the
  defect at every tested `m` (ten digits) — a hard Chebyshev floor whose
  predicted mechanism is seam localization (defect concentrated at handoff
  phases); the richer absorption family is brittle in `m` — the
  overdetermination signature. Within this family, backward distance to
  `Σ_{3m}` is order `1/m`, predicting the **linear** `d(ε,δ)` law under this
  frame — upper-bound-family evidence only.
- **(S3) `X`-certified (E66).** Period-1 nonexistence of exact cycles for the
  Q154 weight: 26/26 support patterns refuted by certified interval
  arithmetic, zero undecided, the tool validated on the FTV table's known
  cycle with positive and negative controls. First computational certificate
  feeding the trichotomy lane; the Lean port path is the K11 island pattern
  (quarantined certificates, containment-checked).
- **(S4) postulate.** The three-lens identity: the backward condition number,
  the lock margin (Q156), and the `ε`-bridge's weighted-gain weakness at
  extreme hazards are one phenomenon. If it holds, a lock is a certificate of
  positive stratum distance in a named direction, and the lock/unlock
  dichotomy and the `d(ε,δ)` law are two faces of the same geometry.
- **(S5) reading of the open core.** A Q159 trap — and any counterexample to
  the conjecture, through the repaired equivalence — is a weight the
  accumulating strata *permanently avoid* at some fixed distance, uniformly
  in `L`, within the rational region. The search objective is maximizing the
  minimal backward distance; proving the conjecture in this frame means
  showing overdetermination thins the strata but never lets them stay away.

## Open

- The cycle-feedback backward-stability theorem (S1 beyond fixed tail) — the
  conditioning should appear analytically in the value-recursion coupling.
- The seam-localization explanation of the exact `½` (per-phase defect
  vectors decide it immediately).
- The symbolic check of the on-support equality behind the screen-inertness
  mechanism: at exit-support coordinates, leading-order complementarity
  should force `(1+ρ)·r_i({i}) = (Mā)_i`, confining all cutting power to
  off-support coordinates.
- Whether any family approaches `Σ_L` faster than `1/L` on `Γ_η` — the
  log-vs-linear question, now falsifiable by construction.
