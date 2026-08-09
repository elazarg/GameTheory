# Exact repair ladder and rational-table CEGIS

This experiment makes the finite quitting-game search lane executable while
preserving the repository's producer/compiler/diagnostic boundary.

Every calculation uses Python's `fractions.Fraction`; JSON inputs accept only
integers or rational strings.  Floating-point tolerances are never used to
accept a certificate.

## Repair ladder

The default ladder checks, in order:

1. **cutoff one** — one product root followed by all-Continue, accepted only
   when the root is exact Nash at zero continuation and every positive-singleton
   Continue endpoint is safe;
2. **stationary** — the general stationary grid stratum, accepted using the
   exact full-rate unilateral cap against arbitrary behavioral deviations;
3. **quitter subsets** — every pure subset, including Never;
4. **quitter pairs** — boundary roots with one or two genuinely mixed
   coordinates and all remaining coordinates at `0` or `1`;
5. **short holonomy words** — finite cyclic root words, accepted only when
   exact policy recursion, exact phasewise root Nash, and playerwise
   opponent-cycle contraction hold at every cyclic entry phase.

The subset and pair rungs use the same full-rate stationary checker; they are
kept separate because they are cheap boundary charts and useful CEGIS witness
classes.  A hinted rational root or word is checked before enumeration but is
never trusted without exact recomputation.

The corresponding kernel-facing types are in
`UniformEquilibrium/Diagnostics/Quitting/ExactRepairCertificate.lean`:

- `QuittingCutoffOneRepairCertificate`;
- `QuittingStationaryRepairCertificate`;
- `QuittingCyclicRepairCertificate`.

Each type exposes an exact terminal-Nash theorem and a uniform-payoff theorem
through the existing production compilers. The JSON search output is exact
external arithmetic evidence, not an instantiated Lean proof: reports identify
the applicable theorem schema with `status: theorem_schema_only`. Promotion to
a library theorem requires constructing that certificate in Lean. The
diagnostic module contains no search procedure and no
failure-to-nonexistence theorem.

## Exact semantics checked by Python

For a product root `p`, let `A` be its one-stage absorbing contribution and
`q` its all-Continue mass.

For cutoff one, the prescribed terminal value is `V = A`.  Player `i`'s exact
behavioral cap is

```text
max(Q_i, C_i + q_{-i} * max(0, r_i({i}))),
```

so an accepted report is precisely the safe cutoff-one theorem's finite data.

For an absorbing stationary root,

```text
u_i = A_i / (1 - q).
```

Against stationary opponents, arbitrary behavioral deviations reduce to the
exact full-rate cap: immediate Quit versus Never in the contracting regime,
and `max(0, r_i({i}))` on the saturated face.  The checker reports the full
cap and exact regret for every player.

For a cyclic word, the phase values solve

```text
u_k = A_k + q_k * u_{k+1}.
```

The word is accepted only if every phase is exact root Nash against `u_{k+1}`
and every player's product of opponent-continuation masses over one turn is
strictly below one.  The implementation also independently computes the exact
pure-time/Never behavioral cap at every entry phase.  Small coefficient return,
finite-label recurrence, or a formal holonomy calculation alone is not an
accepted word.

## Reports and claim discipline

Reports use `quitting-repair-report/v1`.

- `classification: repair` contains complete exact finite data and names the
  Lean certificate schema it can instantiate; the JSON itself is not a Lean
  proof term.
- `classification: gap_counterexample` contains a profile whose exact terminal
  exploitability is below the proposed positive gap.  It refutes that fixed-gap
  candidate but need not be an equilibrium.
- `classification: filter` records the finite grammar, budgets, and minimum
  observed regret.  It always includes `proves_nonexistence: false`.
- `classification: nonexistence` is rejected unless the payload names a Lean
  declaration proving `GameTheory.HasTerminalExploitabilityGap` with a positive
  gap against **every behavioral profile**.  The experiment never generates
  such a report from bounded search.

Thus stationary, subset, pair, or finite-period failure cannot be silently
upgraded to the all-behavior terminal gap required by
`UniformEquilibrium/Diagnostics/Uniform/NonexistenceCertificate.lean`.

## Running the ladder

From the repository root:

```bash
python3 -m experiments.quitting_repair_cegis ladder \
  experiments/quitting_repair_cegis/tables/cutoff_one_mixed.json
```

Save and independently recompute a report's exact Python arithmetic:

```bash
python3 -m experiments.quitting_repair_cegis ladder TABLE.json \
  --output report.json
python3 -m experiments.quitting_repair_cegis verify-report \
  TABLE.json report.json
```

A search configuration is an optional JSON object containing the rational
probability grid and finite budgets.  The generated report embeds the complete
configuration.

## Fixed-gap rational-table CEGIS

A `quitting-table-cegis/v1` manifest supplies a positive rational gap and
either a finite list of tables or a base table with finitely valued rational
reward entries.  The loop:

1. reuses previously found root/word profiles against the next table;
2. runs the exact repair ladder;
3. searches the bounded cutoff, stationary, and pure-root cyclic profile
   grammar for exact exploitability below the proposed gap; and
4. labels any survivor only as a finite filter.

Run the committed two-candidate regression with:

```bash
python3 -m experiments.quitting_repair_cegis cegis \
  experiments/quitting_repair_cegis/regressions/fixed_gap_cegis.json \
  --output-dir /tmp/quitting-fixed-gap
```

One candidate has an exact cutoff-one repair matching a stable Lean certificate
schema; the other survives only the deliberately coarse finite grammar and is
reported as a filter.

## Regressions

The committed rational tables include:

- a mixed safe cutoff-one root;
- the three-player table whose exact stationary repair is
  `(1/2, 1, 1/4)` with payoff `(1, 3/4, 1/2)`;
- a two-phase accepted cyclic word; and
- a stationary nonattainment family with exact regrets
  `1/10`, `1/36`, and `1/136` at the listed hazards.

Regenerate and test all artifacts:

```bash
python3 -m experiments.quitting_repair_cegis.regressions.generate_expected
python3 -m unittest discover \
  -s experiments/quitting_repair_cegis/tests -v
git diff --exit-code -- \
  experiments/quitting_repair_cegis/regressions/expected
lake build +UniformEquilibrium.Diagnostics.Quitting.ExactRepairCertificate
```
