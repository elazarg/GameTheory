# CLAUDE.md

Read `AGENTS.md` first; it is the canonical operational guidance. Then read the
relevant decision and falsification test in `docs/GameTheory2Design.md` before
changing an architectural surface.

## Project state

This is a fresh Lean 4/Mathlib project. Its Lake package, public library, and
Lean namespace are named `GameTheory`.

Phases 0 through 3 of the RFC spike have passed, so every architecture decision
D0–D10 is now recorded rather than open. The static semantic core lives under
`GameTheory/Core`, the finite-support law type under `GameTheory/Probability`,
the sequential layer under `GameTheory/Protocol`, native encodings under
`GameTheory/Languages`, the executable rational frontend under
`GameTheory/Finite`, everything needing convexity or topology under
`GameTheory/Analysis`, and architecture spikes under `GameTheory/Experimental`
(never re-exported).

`GameTheory/Analysis` is a one-way boundary. It is the only root allowed to
import the external fixed-point package, and no module outside it may import it
back; a file that does can reach all of `stdSimplex` and `Polynomial`, which the
core and the executable frontend must never see. Both directions are checked by
`scripts/phase2-audit.ps1`; its explicit `-DeepReachability` release mode also
asserts that the analytic root *does* reach them. See
`docs/Phase2IncentiveSlice.md` and
`docs/Phase3SequentialSlice.md` for what the gates guarantee and, more usefully,
for the recorded limits they do not, and `docs/Phase4StaticHarvest.md` for the
theorem families recovered on the settled API.

With the architecture settled, the mode shifts from validation to theorem
delivery against the accepted API and the successor-native delivery ledger.

## Tempo: move fast, depth first

Move fast in two deliberate stages:

1. First validate the architecture depth first. Push one hostile vertical slice
   through its downstream theorem, kill or repair weak abstractions immediately,
   and do not spend time building breadth on an unsettled foundation.
2. Once the relevant gate passes, reuse standard theorem statements, proof
   structure, helpers, and tests instead of reproving them gratuitously.

Parallelize independent theorem families after their shared definitions are
stable. Use faster models for routine translation, import repair, short proofs,
and repetitive ports; move semantic ambiguity, architecture decisions,
counterexamples, persistent proof failures, and integration conflicts to
stronger reasoning models. Check parallel work against the shared target often
so speed does not create duplicate concepts or divergent APIs.

Every architecture spike gets a short `EXP-NNN` entry in
`docs/ExperimentLog.md`. Record the question before or when work starts, then
add exact artifacts/commands, observations, outcome, and next action. Log
positive, negative, narrowed, and inconclusive evidence. Decision records and
RFC changes must cite the experiment ID; do not erase a failed hypothesis by
quietly rewriting the design document.

## Documentation boundary

Phases, experiment IDs (`EXP-NNN`), decision IDs (`D0`–`D12`), and RFC section
or kill-criterion citations are **plan and history**. They belong in
`docs/ExperimentLog.md`, `docs/decisions/`, and the phase gate documents.

Do not put them in Lean docstrings. Code outlives the plan: a reader a year from
now should learn from a module docstring *what the design is and why*, stated in
timeless terms, without needing the planning documents to decode it. Write "a
`Prop`-valued reachability relation would make this vacuous" rather than "RFC
9.1.7 makes this a core-invalidating failure".

The `GameTheory/Experimental/` tree is the exception: those files exist only as
recorded evidence for a named experiment, and their directory names say so.

## How to work here

- The working directory is already the project root; do not prepend `cd` to
  commands.
- Use `rg` and `rg --files` for repository search.
- Begin with the smallest RFC spike capable of killing the proposed design.
- Reserve its experiment-log ID before substantial implementation.
- Compile one definition or theorem at a time once Lean code exists.
- Inspect the actual goal before writing proof tactics; test small candidate
  tactics before committing a proof.
- Search Mathlib APIs before inspecting or recreating general-purpose proofs.
- Address all diagnostics and linter warnings before calling a slice complete.
- During design validation, do not broaden scope with adjacent theorem
  families. During theorem delivery, work only against the assigned scope and
  accepted shared API.

## Environment commands

```text
lake update
lake env lean --version
lake exe cache get
```

There is no meaningful library build until the first source module is created.
After that, use the narrowest target during iteration and reserve `lake build`
for dependency or phase-gate validation.

## Architectural reminders

- `GameTheory` is the public namespace; `GameTheory2` is only the repository and
  RFC generation label.
- Static forms, execution protocols, and information models are distinct until
  their experiments justify sharing more.
- Equilibrium deviations are local and law-linear by construction; response
  and dominance concepts keep their profile-quantified logical shape.
- Finite-support probability is the stable default. Infinite stochastic path
  laws wait for a measurable layer.
- Executable finite algorithms and real-valued correctness proofs live in
  separate dependency roots.
- D0 is decided from measured dependency baselines and a small hybrid
  prototype—not by rebuilding the hardest theorem three times.

When an RFC choice fails its kill condition, record the failure and narrow or
replace the design. Do not patch around it to preserve sunk work.
