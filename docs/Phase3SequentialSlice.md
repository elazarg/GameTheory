# Phase 3 sequential vertical slice

Status: gate passed. Neither sequential kill criterion fired, D6 and D7 are
decided, and D0 is final at every semantic level.

## What was built at the gate

This is the gate inventory. The history and randomized runners and the theorem
close-outs added afterwards are recorded separately at the end rather than
retroactively folded into the gate measurements.

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
| `GameTheory/Experimental/PostArchitecture/RoundsWitness.lean` | a two-round simultaneous game, checking that simultaneity composes across rounds |

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
| simultaneity composes across rounds | passed | `Experimental/PostArchitecture/RoundsWitness.lean` |
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

## Measurements at the gate

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
the marginal cost is. `RoundsWitness.lean` is 158 lines and receives the run law,
histories, reachability, backward induction, information locality, assessment,
and compilation into the static core, contributing none of them.

## Findings at the gate

These findings describe the interface at the gate revision. Finding 4 is the
one subsequently resolved in stages; the close-out records the replacement
runners, compilers, and theorems without rewriting this evidence.

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

## Outstanding at the gate

Nothing blocked the gate. These were the carry-forwards at that date; the
close-out below records which have since been discharged.

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
- **History-local execution is done (EXP-016).**
  `GameTheory/Protocol/History.lean` runs a `HistoryChooser` and proves that,
  when the chooser ignores history, pushing its history law forward along
  `History.state` recovers `runFor`. It is therefore a refinement of the state
  runner, not a second semantics. The merging test also shows why it is
  necessary: an information-local profile can distinguish two histories that
  reach one state and induce a law no state-indexed chooser induces.
- **Randomized history-local execution is done (EXP-017).**
  `GameTheory/Protocol/Randomized.lean` lets each history return a law over legal
  joint actions. Point-mass answers recover the deterministic history runner by
  theorem. `Information.lean` uses that runner for behavioral policies and uses
  the deterministic history runner after one initial policy draw for mixed
  policies.
- **Both behavioral/mixed directions are done (EXP-017 and EXP-018).** Local
  randomization becomes one draw over policies under
  `ActsOnceWhereItMatters`; one draw becomes local randomization under
  `ConstrainsAlike`, which perfect recall implies. The quotable result,
  `runBehavioral_image_eq_runMixed_image`, equates the realizable sets of laws
  over histories when both distinct conditions hold. This closes T2 as a
  theorem about two representations in one information model, not as evidence
  for a certificate layer.
- **The state-chooser one-shot principle is an equivalence (EXP-021).**
  Under `WellFoundedPlay`, `IsOneShotOptimal` implies that the chooser beats
  every alternative chooser from every state, and the converse constructs
  `deviateAt`. `Assessment.lean` reads the forward direction as local
  optimality in a supplied context.
- **Composed static compilation and its forward one-shot bridge are done
  (EXP-025).** `InformationModel.toGameForm` gives players information-local
  `Policy` strategies and retains full histories as outcomes;
  `toBehavioralGameForm` presents behavioral policies, while the ordinary
  mixed extension of the pure-policy form is definitionally `runMixed`. The
  two sharp behavioral/mixed law theorems therefore commute with compilation
  rather than being reproved for it. For finite horizons,
  `IsOneShotOptimalWithin` quantifies over every history and every local
  replacement choice. It implies that no whole replacement policy improves
  expected payoff from any history, and
  `isNash_toGameForm_of_isOneShotOptimalWithin` carries the from-start result
  into the ordinary static `IsNash`. `historyContext` supplies the actual
  profile-plus-continuation context at a history, and
  `isOneShotOptimalWithin_iff_sequentiallyRationalAt_historyContext` identifies
  the quantified one-shot premise exactly with `IsSequentiallyRationalAt` in
  those contexts.
- **The full well-founded historywise theorem is closed (EXP-036, renamed by
  EXP-075/D42).**
  `Protocol.SubgamePerfect` adds history-preserving backward recursion over the
  existing `WellFoundedPlay` certificate and proves that it agrees with the
  forward history runner whenever the latter has stopped. Its
  `IsHistorywiseOptimal` predicate quantifies over every player, every whole
  information-local replacement policy, and every complete history, including
  off-path histories. Under `ActsOnceWhereItMatters`, it is equivalent to
  `HasNoProfitableOneShotDeviation`. The discriminating probe is optimal from
  the initial history yet fails historywise optimality because of a profitable
  deviation after an off-path decision. `IsSubgamePerfect` now uses
  information-set-closed subgame roots; the hidden-card control rejects a root
  that cuts a nonsingleton information set. No general imperfect-information
  one-shot iff SPE theorem is claimed. The exact frozen T4 NFG-to-FOSG
  embedding remains a separate language theorem.

## Post-gate EFG amendment

EXP-033 has since closed the native finite-EFG presentation item with a
transparent bundle of the canonical execution and information semantics.
EXP-034 carries that same hostile chance/imperfect-information EFG through the
analytic consistency adapter to a concrete sequential equilibrium. EXP-035
then gives that assessment a nonconstant hidden-state/action matching payoff
and proves value `1 / 2` against every whole replacement behavioral policy.
EXP-036 closes the full semantic SPE/one-shot-deviation theorem at the Protocol
layer. A thin EFG-facing wrapper, T1 strategic/Nash extraction, and T4 remain
delivery work; the nonconstant continuation-payoff and off-path SPE checks do
not.

The current reconciliation is maintained in
[`DeliveryLedger.md`](DeliveryLedger.md), rather than by rewriting the
gate-era findings above.
