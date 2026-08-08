# Experiments

This directory contains reproducible search code whose outputs are not library
theorems by default.  An experiment may emit proof-carrying data for a stable
checker under `UniformEquilibrium/Diagnostics/`, but search exhaustion remains
an experimental filter unless a named theorem proves the required semantic
quantifiers.

Current experiments:

- [`quitting_repair_cegis/`](quitting_repair_cegis/) — exact rational repair
  ladder and fixed-gap counterexample CEGIS for finite quitting games.
