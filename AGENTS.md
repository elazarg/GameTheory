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
GameTheoryMath/                 independently reusable mathematics
lakefile.lean                   package and `GameTheory` library targets
lean-toolchain                  pinned Lean toolchain
```

Game source belongs under `GameTheory/` and public declarations below the
`GameTheory` namespace. Package boundaries in the RFC are logical dependency
roots; create a new one only when its first hostile slice validates the need.

## Verification

Use `rg`/`rg --files` for local search. Prefer Lean language-server diagnostics
for iteration when available, then run the narrowest relevant Lake target. Run
a full build only at a phase gate or when imports/package configuration change.

Toolchain checks after dependency or environment changes:

```text
lake update
lake env lean --version
```

Once source exists, warnings are failures and the relevant target must build
without placeholders. Keep `.lake/` and local tool state ignored.

## Scope and repository hygiene

Preserve unrelated user changes. Do not modify generated dependency trees or
`lake-manifest.json` by hand. Keep commits focused on one
decision or vertical slice, and report the exact validation performed.
