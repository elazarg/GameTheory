# Phase 3 sequential vertical slice

Status: gate passed. Neither sequential kill criterion fired, D6 and D7 are
decided, and D0 is final at every semantic level.

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
| `GameTheory/Languages/MAID.lean` | a three-node influence diagram compiled into the execution and information layers, with its workaround list |
| `GameTheory/Languages/Rounds.lean` | a two-round simultaneous game, checking that simultaneity composes across rounds |

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
| simultaneity composes across rounds | passed | `Languages/Rounds.lean` |
| two languages reach the static core with no language-specific machinery | passed | `Tests/Transfer.lean` |

## Decisions

D6 is recorded in
[`decisions/D6-execution-and-information.md`](decisions/D6-execution-and-information.md):
general-state execution is the primary interface, and the finite-first tree is
retained as a derived presentation for single-mover games. The deciding
measurement was that sequentializing a simultaneous move strictly enlarges the
strategy space, so the tree needs an information layer to be faithful — the
machinery whose absence made it cheaper elsewhere.

D7 is recorded in
[`decisions/D7-certificate-stratification.md`](decisions/D7-certificate-stratification.md):
no named adequacy certificates. The budget said a certificate level must beat
the bespoke bridge it replaces, and the bridge turned out to cost nothing —
each language reached the static core by applying one existing generic function,
and both take their outcome law from one theorem instantiated twice. Nothing
beats zero. The rejection is scoped to languages compiling *into* a shared
target; a transfer that must preserve what the target forgets, such as recall,
would reopen it, and none exists here yet.

D0 is finalized in
[`decisions/D0-semantic-architecture.md`](decisions/D0-semantic-architecture.md).
Its one substantive change is at the protocol level: Phase 0 predicted
coordinated native branches, and the measurement is stronger than that, because
both native shapes fit a single execution base. The finalization also records
what it does not rest on — two of the four frozen transfers were never built,
and it carries a correction about what one of them would show.

## Measurements

Reproduce with:

```text
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

| Measure | Value |
|---|---:|
| `GameTheory/Protocol` nonblank lines | 1418 |
| `GameTheory/Protocol` modules | 8 |
| `GameTheory/Languages` nonblank lines | 973 |
| second language front-end, nonblank lines | 158 |
| Source-level transport tokens in the sequential layer | 0 |
| `Function.update` in the sequential layer | 0 |
| `sorry`, `admit`, `native_decide`, custom axioms | 0 |
| Layering violations | 0 |
| Reachability probes passed | 3 / 3 |

The second front-end is the one that measures amortization. The shared layer is
larger than the two front-ends put together, so the total is not the argument;
the marginal cost is. `Rounds.lean` is 158 lines and receives the run law,
histories, reachability, backward induction, information locality, assessment,
and compilation into the static core, contributing none of them.

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

## Language encodings

A three-node influence diagram compiles into the execution and information
layers with no fake players, no fake actions beyond the canonical no-op, and no
escape fields — each recorded with a theorem in that module's `## Workarounds`
section. The honest remainder is recorded there too, including one bounded
limit: the diagram's DAG must be linearized, and a diagram with two
incomparable decision nodes would make the compiled protocol assert an order the
diagram does not have. That case is untested.

That encoding also rediscovered finding 4 above independently, from a different
direction.

A two-round simultaneous game compiles with no workaround at all: no fake
players, no fake actions, and the no-op never appears, because no state has an
idle player. Its recorded limit is that the middle state carries the round's
*outcome* rather than its actions, so a game needing the exact previous profile
would need a wider state.

## Outstanding

Nothing blocks the gate. What follows is carried forward:

- A native extensive-form encoding with its own workaround list. The
  imperfect-information and chance protocols under `GameTheory/Tests/` exercise
  the interface but are not a language module and produce no such list.
- The behavioral/mixed equivalence, in both directions. It is the frozen
  transfer with the largest gap between its name and its real obligations:
  reach mass, support factorization, and player-local action posteriors. Its
  value is as a test of the accepted interfaces against a real theorem — it is
  a statement about two strategy representations within one information model,
  not a transfer between languages, so it is not evidence about the certificate
  decision either way.
- The one-shot embedding commuting with compilation, the other frozen transfer
  that was not built.

## Close-out list

- `GameTheory.lean` now re-exports `GameTheory.Protocol`, which was held back
  until D7 settled because the sequential interface's shape was what D7
  measured. `GameTheory.Languages` stays outside the umbrella: those encodings
  are demonstrations with recorded scope limits, not coverage of their source
  formalisms.
- **Done since the gate.** A history-indexed runner now exists in
  `GameTheory/Protocol/History.lean`, and finding 4's first half is resolved: a
  profile of information-local policies can be run. The state law is that law's
  pushforward, so it is not a second semantics, and the gap it closes is
  measured — the merging protocol in `Tests/History.lean` exhibits a profile
  whose law no state-indexed chooser produces, together with a control profile
  whose law one does. What remains of finding 4 is the one-shot-deviation
  theorem, which now has the runner it was missing. The paragraph below is the
  close-out item as it stood at the gate.
- A trace-indexed runner is the single change that would remove the largest
  remaining limitation. Finding 4 blocks two things at once: the strategic
  compilation is restricted to state-indexed policies, and the one-shot
  deviation *theorem* — local optimality at every information state implying
  global optimality under `WellFoundedPlay` — cannot be stated, because it needs
  a run law fed by history-indexed policies. A law over `Trace` with the state
  law as its pushforward would lift both, and `infoOf` already recurses over
  traces. Worth evaluating in the same pass that revisits signature ownership,
  since both rest on how carriers are indexed.
