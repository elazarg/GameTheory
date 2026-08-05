# Two-player quitting is closed

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `PROVED`, maturity `L`, capstone | `QuittingTwoPlayerExistence.lean` | the `n ≥ 3` program (branch map below); this group's gate | — (unconditional theorem, standard axioms) |

## The theorem

`quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`: every two-player
quitting game (`ι = Bool`) has a uniform equilibrium payoff. **Zero
hypotheses.** Four exhaustive branches: zero-solo (payoff `0`); solo-quitter
rate (the owner's solo payoff); pair-repair; joint-exit (the pair payoff,
exact). Three branches are pre-existing `n`-agnostic machinery; the new
mathematics is two lemmas (the affine interpolation on the unit interval,
and the joint-exit instantiation). No discount limit anywhere. Registered in
the axiom audit at the standard three axioms.

Known mathematics since Vrieze–Thuijsman (1989) — this is a ground-rung
result, not a novelty claim — but the first machine-checked uniform-existence
theorem for a nontrivial class, by a route (branch classification) built to
generalize where the classical vanishing-discount route is not.

## The publishable negative en route

**There is a two-player weight with no exact stationary equilibrium at
all**: `r({owner}) = (1, −2)`, `r({blocker}) = (0, −1)`,
`r({owner,blocker}) = (−1, 0)` — hand-checked over all four corners and the
interior of the rate square (recorded in the capstone's docstring;
deserves its own Lean statement). Consequence, already acted on: the
six-scalar stationary route this group's gate and `LEAN-P1-1` aimed at is
**refuted as a complete route even at `n = 2`** — genuinely approximate
equilibria are mandatory at two players. This group's gate is superseded by
the theorem itself.

## The `n = 3` map (mined from the proof, each item actionable)

- **Blocker designation generalizes now**: at `n ≥ 3`, finitely many
  opponents plus affine-in-`p` failure of the no-join condition forces one
  opponent to block on all of `(0,1]`; `le_of_lt_affine_on_unitInterval`
  nearly suffices as is.
- **What breaks is the pair repair**: coalitions of size `≥ 2` open
  internal-leaver deviations (a branch of the sure-set owner cap the
  two-player proof never enters) and spectator preemption — the same
  mechanism as the four-player family's blocked instant profiles. This is
  the precise `n = 3` frontier.
- **The general sure-exit-set theorem** ("no member leaves, no outsider
  joins", arbitrary coalition `S`) is one instantiation away from the landed
  machinery and unstated.
- Hygiene: `hsolo` is unused in the joint-exit branch (the branches
  overlap); the zero-sum uniqueness lemma generalizes to `ε`-slack with the
  same proof; `ι = Bool` rather than any two-element type (a relabeling
  transport does not exist).
