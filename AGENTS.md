# AGENTS.md

## Mission and current phase

This is a greenfield Lean 4 rewrite of the GameTheory library. The Lake package,
public library, and public namespace are all named `GameTheory`; the repository
directory being named `GameTheory2` is not an API choice.

The foundational architecture gates have passed and the repository now contains
the validated core, protocol, finite, analysis, repeated, and scoped language
layers. Current work is post-architecture delivery: close the frozen
obligations, then recover mature theorem families in dependency-gated waves.
The governing architecture is `docs/GameTheory2Design.md`; the mutable delivery
order is `docs/PostArchitectureDeliveryPlan.md`, current status is
`docs/DeliveryLedger.md`, and public workflows are in
`docs/CapabilityMatrix.md`.

## Sources of truth

Read the relevant RFC decision before changing foundations. Its status labels
matter:

- adopted decisions are defaults;
- provisional decisions must survive their listed vertical slice;
- experiment-gated decisions require a decision record with measurements;
- disproof conditions override architectural preference.

For delivery status, use the post-architecture plan and delivery ledger rather
than inferring completion from a phase name, module count, or nearby theorem.
Update the owning ledger row in the same commit as the evidence that changes
its status.

## Tempo: move fast, depth first

**Move fast.** The intended sequence is depth first, then broad and parallel:

1. **Validate the design first.** Drive one thin but hostile slice all the way
   from foundational types to a representative downstream theorem. Prefer the
   shortest experiment that can falsify a decision, resolve the failure, and
   continue until the dependency path is trustworthy. Do not create breadth to
   make an unvalidated foundation look productive.
2. **Then recover theorem depth.** After a gate passes, reuse established proof
   ideas and standard mathematical statements instead of reproving known
   mathematics gratuitously. Do not preserve bad APIs, compatibility surfaces,
   duplicate semantics, or unsound statements.
3. **Parallelize routine recovery.** Partition independent theorem families or
   leaf modules among agents when integration boundaries are already fixed.
   Give each task a narrow file/theorem scope and an explicit target API so
   parallel work does not fork definitions.
4. **Match model cost to difficulty.** Use faster models/agents for mechanical
   statement translation, import repair, short proofs, and repetitive ports.
   Escalate architecture, semantic validation, stubborn proof failures,
   counterexamples, and cross-module integration to stronger reasoning models.
5. **Integrate continuously.** Fast parallel output is provisional until it
   compiles against the shared branch, uses the canonical definitions, and
   passes the relevant architecture checks. Reassign or escalate quickly when a
   routine port exposes a foundational issue.

Speed is measured by validated dependency depth and integrated theorem
coverage, not declarations drafted or agents kept busy.

## Experiment evidence

Treat every architecture spike as an actual experiment, not merely a future
edit to the RFC. Reserve an `EXP-NNN` entry in `docs/ExperimentLog.md` when the
spike starts and complete it when the result is known. Keep the entry short:
hypothesis/question, representative slice, exact artifacts and commands,
observations or measurements, outcome, and next action.

Log supporting, refuting, narrowing, and inconclusive results. Link bulky logs
or code instead of pasting them. Preserve surprising failures; do not rewrite
the original hypothesis or kill condition after seeing the outcome. Decision
records cite experiment IDs and synthesize their evidence. The RFC records the
current design, not the only surviving account of how it was chosen.
Decision records and RFC changes must cite the experiment ID; do not erase a
failed hypothesis by quietly rewriting the design document. When an RFC choice
fails its kill condition, record the failure and narrow or replace the design.
Do not patch around it to preserve sunk work.

An EXP entry records an experiment on the design (a question, competing
designs, kill conditions, and what the evidence showed), not a changelog. Do
not open an entry for ordinary feature work, and do not inventory migrated
predicates, renamed lemmas, or touched files inside one: that belongs in the
commit message. Keep only observations that would change a future design
decision.

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

## Working discipline

1. Work in dependency-gated order. Do not add domain breadth before the
   relevant architecture gate passes; after it passes, recover the matching
   theorem family quickly.
2. For an experiment-gated choice, log the run in `docs/ExperimentLog.md`, then
   state the competing designs, representative slice, measurements, kill
   condition, experiment IDs, and result under `docs/decisions/` before
   freezing a public API.
3. Build the smallest hostile example that can falsify a design. A toy example
   that cannot expose the known risk is not validation.
4. Define each mathematical concept once at its lowest sufficient semantic
   layer. Familiar names should be transparent specializations, not parallel
   definitions.
5. Put invariants in types or named certificates. Directory placement and prose
   do not count as enforcement.
6. Search Mathlib before adding general mathematics. Keep reusable mathematics
   independent of game-specific modules and suitable for upstreaming.
7. Put assumptions on the operation or theorem that needs them. Do not store
   avoidable `Fintype`, `Finite`, `DecidableEq`, topology, or preference
   assumptions in semantic data.
8. Preserve the proof/execution boundary. Executable algorithms use explicit
   finite enumerations and computable scalars; correctness modules connect them
   to proof semantics.
9. Keep stable, provisional, Frontier, and Challenges trust surfaces separate.
   Trusted code contains no `sorry`, `admit`, custom axioms, or challenge
   dependencies.
10. Treat a machine-refuted source claim as a proved counterexample, not as an
    open proof obligation.

## Greenfield constraints

- No source-compatibility aliases or migration adapters.
- No universal semantic hub, probability abstraction, certificate hierarchy,
  or category instance before its RFC competition has passed.
- No direct `Function.update` outside the future profile implementation.
- No user-visible `cast`/`Eq.ndrec` plumbing outside designated transport
  modules; measure this at source level, not in elaborated proof terms.
- No `open Classical` or `Fintype.ofFinite` in executable algorithm modules.
- No language syntax importing solution concepts, and no stable module
  importing Frontier or Challenges.
- No unfocused `Facts.lean` dumping grounds.

## Repository layout

```text
docs/GameTheory2Design.md       architecture RFC
docs/PostArchitectureDeliveryPlan.md active delivery waves and domain gates
docs/DeliveryLedger.md          successor family and gate status
docs/CapabilityMatrix.md        recognizable public workflows
docs/ExperimentLog.md           concise chronological evidence ledger
docs/decisions/                 measured architecture decisions
GameTheory/                     current public and opt-in Lean modules
GameTheory/Math/                 independently reusable mathematics
lakefile.lean                   package and `GameTheory` library targets
lean-toolchain                  pinned Lean toolchain
```

Game source belongs under `GameTheory/` and public declarations below the
`GameTheory` namespace. Package boundaries in the RFC are logical dependency
roots; create a new one only when its first hostile slice validates the need.

The static semantic core lives under `GameTheory/Core`, probability under
`GameTheory/Math/Probability`, the sequential layer under `GameTheory/Protocol`,
native encodings under `GameTheory/Languages`, the executable rational frontend
under `GameTheory/Finite`, everything needing convexity or topology under
`GameTheory/Analysis`, and architecture spikes under `GameTheory/Experimental`
(never re-exported).

`GameTheory/Analysis` is a one-way boundary. It is the only root allowed to
import the external fixed-point package, and no module outside it may import it
back; a file that does can reach `Convexity.StdSimplex` and `Polynomial`, which the
core and the executable frontend must never see. Both directions are checked by
`scripts/phase2-audit.ps1`; its explicit `-DeepReachability` release mode also
asserts that the analytic root *does* reach them. See
`docs/Phase2IncentiveSlice.md` and
`docs/Phase3SequentialSlice.md` for what the gates guarantee and, more usefully,
for the recorded limits they do not, and `docs/Phase4StaticHarvest.md` for the
theorem families recovered on the settled API.

## Architectural reminders

- `GameTheory` is the public namespace; `GameTheory2` is only the repository and
  RFC generation label.
- Static forms, execution protocols, and information models are distinct until
  their experiments justify sharing more.
- Equilibrium deviations are local and law-linear by construction; response
  and dominance concepts keep their profile-quantified logical shape.
- Ordinary Mathlib PMF is the stable discrete probability carrier. Request
  payoff integrability or finite support only where needed. Infinite stochastic
  path laws remain separate from stable execution semantics.
- Executable finite algorithms and real-valued correctness proofs live in
  separate dependency roots.
- D0 is decided from measured dependency baselines and a small hybrid
  prototype—not by rebuilding the hardest theorem three times.

## Verification

Use `rg`/`rg --files` for local search. Prefer Lean language-server diagnostics
for iteration when available, then run the narrowest relevant Lake target. Run
a full build only at a phase gate or when imports/package configuration change.

Toolchain checks after dependency or environment changes:

```text
lake update
lake env lean --version
lake exe cache get
```

Warnings are failures and the relevant target must build without placeholders.
Keep `.lake/` and local tool state ignored.

- The working directory is already the project root; do not prepend `cd` to
  commands.
- Compile one definition or theorem at a time.
- Inspect the actual goal before writing proof tactics; test small candidate
  tactics before committing a proof.
- Search Mathlib APIs before inspecting or recreating general-purpose proofs.
- Address all diagnostics and linter warnings before calling a slice complete.
- `lake lint` sees only what `lint/GameTheory/LintAll.lean` imports, and that
  target is not built by default. After adding, moving, or deleting a library
  module, update its import list (every module outside `Experimental/`,
  `Tests/`, and `*Test` fixtures), remove a deleted module's `.lake/build`
  artifacts, and run `lake build GameTheory.LintAll` before `lake lint`.
  Otherwise new modules go unlinted and deleted ones break the driver.
- During design validation, do not broaden scope with adjacent theorem
  families. During theorem delivery, work only against the assigned scope and
  accepted shared API.

## Scope and repository hygiene

Preserve unrelated user changes. Do not modify generated dependency trees or
`lake-manifest.json` by hand. Keep commits focused on one
decision or vertical slice, and report the exact validation performed.

## Current toolchain-bump reference

The completed Lean 4.34 / Mathlib v4.34.0 bump and its client migration lessons
are in [docs/Lean434BumpLessons.md](docs/Lean434BumpLessons.md): published pins,
mechanical renames, simplex and measure API changes, tooling limits, and final
validation. Keep bump plans and raw diagnostics local.

## Toolchain-bump lessons (Lean 4.33 / mathlib v4.33.1)

These notes describe the earlier 4.33 bump. Diagnose current failures before
carrying its transparency or deriving workarounds into another release.

- **Two different failure modes, two different fixes.** Lean 4.33 stopped
  unfolding semireducible definitions in two places, and they need opposite
  responses. A `rw`/`simp` that reports *"Did not find an occurrence of the
  pattern"* is a **matching** failure: fix it at the definition by marking the
  type-synonym or fixture wrapper `@[reducible]` (or `abbrev`). An error whose
  note says *"the target expression is not type-correct under the `implicit`
  transparency level"* is a **different, stricter check that `@[reducible]`
  does not satisfy**; only
  `set_option backward.isDefEq.respectTransparency false in` on the
  declaration clears it. Do not rewrite the proof for the second kind — keep
  the original tactic script and add the option. Enumerate the sites with
  `rg -n "respectTransparency" --type lean -g '!.lake'`.
- **Try `exact` before reaching for either.** Many of these goals are `rfl`-true
  (possibly after a trivial `rw [one_mul]`), and `exact` elaborates at default
  transparency, so it sees through everything. It is smaller than a `simp` set,
  needs no option, and is often shorter than the proof it replaces.
- **A `whnf` heartbeat timeout may mean divergence, not slowness.** If raising
  `maxHeartbeats` an order of magnitude still times out, the elaboration is
  running away; replace the offending `simp`/`simpa`, do not raise the limit.
- **Never bulk-apply `linter.unusedSimpArgs` suggestions.** It flags each
  argument as individually removable when several are redundant with each
  other, or when the real progress comes from beta/delta reduction rather than
  any named lemma. Removing every flagged argument on a line can empty the simp
  set and break the proof; for a single-element `simp only [X]` it often means
  `dsimp only`, not deletion. Re-check every file whose simp set you touch.
- **`deriving Fintype` on plain enums is broken at this toolchain.** It
  reproduces in four lines with no project code. Mathlib's own
  `MathlibTest/DeriveFintype.lean` works around it with
  `set_option backward.isDefEq.respectTransparency false in` before each
  inductive; this repo does the same at every enum site.
- **Never edit files while `lake build` is running.** Lake reads each module's
  source as it schedules that target, so a mid-build edit yields a mixed
  snapshot whose failure list cannot be trusted. Finish editing, then build.
- **`lake env lean` reads the *oleans* of imports.** After changing a module
  that others import, `lake build <that module>` first or every downstream
  single-file check is stale — a fix can look like it failed when it worked.
