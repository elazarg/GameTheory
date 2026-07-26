# Phase 3 sequential vertical slice

Status: in progress. D6 is decided; the language encodings, D7, and the
finalization of D0 are outstanding.

## What was built

| Module | Contents |
|---|---|
| `GameTheory/Protocol/Execution.lean` | general-state execution: legality, terminality, chance, run semantics, realized transitions, `Type`-valued histories, bounded horizon, tree-shapedness |
| `GameTheory/Protocol/Tree.lean` | the finite-first presentation: inductive trees, structural evaluation, plan types over the tree's own decision sites |
| `GameTheory/Protocol/Backward.lean` | well-foundedness certificate, backward-induction recursor, and the bridge to the fuelled evaluator |
| `GameTheory/Protocol/Extraction.lean` | reachable decision sites, site-indexed strategies, and the faithfulness theorem |
| `GameTheory/Protocol/Information.lean` | signals, information states, information-local policies, menus and their adequacy law, beliefs |
| `GameTheory/Protocol/Assessment.lean` | contexts, local optimality, the one-shot-deviation interface, sequential rationality |
| `GameTheory/Protocol/Strategic.lean` | compilation of a protocol into a static `GameForm` |

## Kill criteria

Neither sequential core-invalidating failure fired.

*Execution semantics.* A total legal-action chooser is not merely unnecessary —
it cannot be written, because `terminal_no_legal` is a theorem: legality was
defined to include non-terminality. Chance is carried by the transition law and
the runner steps through it rather than halting.

*Information semantics.* `Policy` takes an information state and no execution
state, recorded as an `rfl`-checked type equation. Two states in one information
set give equal information states, so every information-local policy agrees
there by `congrArg` — with no locality hypothesis anywhere. Menu adequacy is a
law over traces; the `menu` field never receives a state.

## Hostile tests

| Test | Result | Where |
|---|---|---|
| terminal play without a total chooser | passed | `Tests/Execution.lean` |
| chance with a normalized law, no dummy data | passed | `Tests/Execution.lean` |
| the chooser's answer drives the run | passed | `Tests/Execution.lean` |
| information locality by typing | passed | `Tests/Information.lean` |
| merging arena refutes tree-shapedness | passed | `Tests/Arena.lean` |
| cyclic arena refutes every bounded horizon | passed | `Tests/Arena.lean` |
| finite strategy extraction over own decision sites | passed by both presentations | `Tree.lean`, `Tests/Extraction.lean` |
| simultaneous actions | general-state only | `Tests/Simultaneous.lean` |

## Decisions

D6 is recorded in
[`decisions/D6-execution-and-information.md`](decisions/D6-execution-and-information.md):
general-state execution is the primary interface, and the finite-first tree is
retained as a derived presentation for single-mover games. The deciding
measurement was that sequentializing a simultaneous move strictly enlarges the
strategy space, so the tree needs an information layer to be faithful — the
machinery whose absence made it cheaper elsewhere.

## Measurements

Reproduce with:

```text
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

| Measure | Value |
|---|---:|
| `GameTheory/Protocol` nonblank lines | 1391 |
| `GameTheory/Protocol` modules | 7 |
| Source-level transport tokens in the sequential layer | 0 |
| `Function.update` in the sequential layer | 0 |
| `sorry`, `admit`, `native_decide`, custom axioms | 0 |
| Layering violations | 0 |
| Reachability probes passed | 3 / 3 |

## Findings

1. **Legality including non-terminality turns an assumption into a theorem.**
   The obvious design stores `terminal_no_legal` as a field. Folding
   non-terminality into `Legal` instead makes it provable and makes a total
   chooser unwritable, which is strictly stronger than the runner simply not
   asking for one.

2. **Histories must be data.** Stating history uniqueness over a `Prop`-valued
   reachability relation is vacuous by proof irrelevance, and a merging arena
   would pass. Both the real refutation and that vacuity are machine-checked
   side by side in `Tests/Arena.lean`.

3. **Two certificates, provably not a second semantics.** The general-state
   candidate needs `StopsWithin` (fuel-shaped, chooser-indexed) and
   `WellFoundedPlay` (order-shaped, chooser-independent), and neither derives
   from the other. What justifies them is `backwardValue_eq_expect_runFor`:
   the backward-induction value and the fuelled run law provably compute the
   same real, while being defined by different recursions.

4. **Information-local policies are history-indexed; the runner is
   state-indexed.** `infoOf` recurses over traces, but `runFor` consumes a
   state-indexed chooser. Folding a full profile of information-local policies
   into a run therefore needs a history-indexed runner, or a bind dependent on
   a law's support — neither of which the finite-support law type provides.
   This is why `Strategic.lean` compiles *state*-indexed policies, which is the
   perfect-information case, and why the one-shot-deviation interface takes its
   context as given rather than deriving it from a profile.

5. **Storing carriers as structure fields costs a reducibility annotation
   everywhere.** Every concrete protocol needs `@[reducible]`, and indexed
   `Trace` inductions additionally need the index typed at the protocol's
   `State` projection rather than the reduced carrier — otherwise `cases` fails
   with an internal motive error. This has now recurred in five modules and is
   evidence about the signature-ownership decision, not an isolated waiver.

## Outstanding

- Language encodings and the written list of language-specific workarounds.
- The certificate-versus-direct-bridge measurement, and hence D7.
- Finalization of D0.
