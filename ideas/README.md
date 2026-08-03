# Idea-to-production pipeline

This directory is the repository-wide durable lifecycle pipeline for
methodological and structural ideas. The current index is concentrated on the
uniform-equilibrium program because that is where the active groups presently
live; the mechanism is not exclusive to that program. The unit of organization
is one coherent **idea group**, not one theorem, experiment, question, or work
session.

New groups should normally get one file in this directory. Existing substantial
notes under `ephemeral/` may remain in place and count as the group
file once they carry the lifecycle card below. Migrate files only when the move
improves navigation; do not duplicate their mathematical content.

## Open intake, orchestrated promotion

Idea generation and independent proof work are decentralized:

- anyone may add an idea-group file, append a falsifier or correction to an
  existing group, or propose a self-contained mathematical question;
- anyone may add an independent Lean proof probe under
  `ephemeral/experiments/`, including a competing formulation or
  counterexample;
- prior assignment is not required. Lack of an active worker is never a reason
  to withhold a precise idea or proof;
- contributors should mark new work conservatively (`PENDING`, normally with
  seal `I` or `X`), state its exact scope and nonclaims, and identify possible
  duplicates and consumers.

Production promotion is orchestrated centrally. The orchestrator:

1. triages new material by objective dependency priority rather than arrival
   time;
2. detects duplicates, incompatible statements, and shared-file collisions;
3. assigns independent mathematical/adversarial audit where the result is
   load-bearing;
4. chooses the smallest honest production theorem surface and the appropriate
   module;
5. assigns or performs promotion, checks the target and umbrella builds, and
   commits stable points promptly; and
6. updates adapters, consumers, lifecycle cards, the idea index, and current
   frontier documents without inflating strategy-class coverage.

An experiment author may report `X`; a rigorous audit establishes `M`; a
public production artifact establishes `L`; actual-data and downstream proofs
establish `A` and `C`. No one needs permission to investigate, but no isolated
proof self-promotes merely by compiling.

## Two independent status axes

A single label such as “done” is too lossy. Every group records both a workflow
lifecycle and an epistemic verdict.

### Lifecycle

| Status | Meaning |
| --- | --- |
| `PENDING` | Triaged enough to retain, with a concrete claim or falsifier, but not yet actively mined. |
| `ACTIVE` | Has objective priority, a named next discriminant, and an assigned research or formalization lane. |
| `BLOCKED` | Remains high-value but cannot advance until a named mathematical prerequisite, artifact, or external input arrives. |
| `MINED` | All presently valuable consequences, counterexamples, and production candidates have been extracted; revisit only on new evidence. |
| `PARKED` | Still plausible or useful, but downstream or deliberately deprioritized. |
| `SUPERSEDED` | A better idea group now owns every live obligation; the replacement path is recorded. |

`MINED` is a workflow conclusion, not a truth claim. An idea can be mined
because it was proved, because its useful fragment was promoted, or because a
counterexample exhausted it.

`BLOCKED` and `PARKED` are deliberately distinct. A blocked group remains an
objective priority and names the prerequisite preventing progress. A parked
group has been deprioritized even if it remains plausible. Neither is an
epistemic verdict: use `WRONG` only on the verdict axis for a claim or group
that has actually been refuted.

### Verdict

| Status | Meaning |
| --- | --- |
| `OPEN` | Central claim remains undecided. |
| `CONDITIONAL` | The claim is proved or highly supported under explicit hypotheses whose production is open. |
| `PROVED` | Exact intended claim is proved at the stated mathematical/strategy-class scope. |
| `WRONG` | Exact stated claim has a rigorous counterexample or contradiction. |
| `MIXED` | The group contains multiple load-bearing claims with different verdicts; the claim ledger must split them. |

Never mark an entire group `WRONG` merely because one motivating analogy died.
Mark the failed claim `WRONG`, preserve its falsifier, and separately classify
the surviving claims.

## Claim maturity

Truth and production readiness are also separate. Each load-bearing claim uses
the existing evidence seals, augmented by an experiment marker:

| Seal | Evidence |
| --- | --- |
| `I` | Precisely stated idea with scope, consumer, and falsifier. |
| `X` | Bounded computation or isolated Lean experiment; no production import. |
| `M` | Rigorous mathematics or exact counterexample, independently auditable. |
| `L` | Production Lean declaration in the public import graph. |
| `A` | Checked adapter from the actual game/certificate data that should supply it. |
| `C` | Checked downstream consumer reaching a semantic theorem or valid recursive output. |

The seals are not a linear ladder in every case, but promotion from an idea
group into the implementation plan requires an exact claim, scope, and
consumer. An `X` result never silently becomes `M`; an `L` verifier never
silently becomes `A`; and `L+A` does not imply strategy-class coverage.

## Required lifecycle card

Place this immediately below the title of every idea-group file:

```markdown
## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `PENDING` |
| Verdict | `OPEN` |
| Objective priority | `P0`, `P1`, `P2`, or `P3` |
| Last audited | YYYY-MM-DD, checkpoint or commit |
| Central live claim | One falsifiable sentence |
| Next discriminant | One experiment, theorem, or counterexample |
| Production destination | Named module/consumer, or `none yet` |
| Supersedes / superseded by | Paths or `none` |
```

Priority is objective rather than chronological:

- `P0`: lies on the shortest honest path to the semantic conjecture or its
  refutation;
- `P1`: supplies a load-bearing producer, exhaustive split, or regression;
- `P2`: reusable infrastructure or a substantial positive subclass;
- `P3`: exploratory language or distant analogy.

The card is followed by four short ledgers before long exposition:

1. **Claim ledger** — exact claim, verdict, seals, scope, source, consumer.
2. **Falsifiers and wrong turns** — tests that would kill it and claims already
   killed.
3. **Production map** — experiments, production modules, adapters, consumers,
   and missing arrows.
4. **Exit conditions** — what changes the lifecycle to `MINED`, `BLOCKED`,
   `PARKED`, `WRONG` at the claim level, or `SUPERSEDED`.

## Workflow

```text
capture a precise idea
        |
        v
PENDING: name scope, consumer, falsifiers, and smallest test
        |
        v
ACTIVE: alternate proof attempts and adversarial counterexamples
        |
        +---- named prerequisite ---> BLOCKED; retain objective priority
        |
        +---- false claim ----------> mark WRONG; retain regression
        |
        +---- bounded evidence -----> X only; state the bounded class
        |
        +---- rigorous result ------> M; nominate exact production surface
                                      |
                                      v
                            L -> A -> C where applicable
                                      |
                                      v
                         update implementation/frontier docs
                                      |
                                      v
                  MINED / PARKED / SUPERSEDED with exit reason
```

Stable production code is committed as soon as its own target and umbrella
builds pass. Unrelated idea groups are not bundled in one commit.

## Promotion gate

Before production promotion, the group file must answer:

1. What exact theorem or counterexample is being promoted?
2. What stronger reading is explicitly not established?
3. Which existing declaration does it reuse or supersede?
4. What actual data supplies its hypotheses?
5. Which theorem consumes its conclusion?
6. Which positive and negative regressions protect the interface?
7. Is the result verification, bounded synthesis, or strategy-class coverage?

If questions 4 or 5 have no answer, a clean Lean theorem may still be useful,
but it remains infrastructure rather than closure progress.

## Maintenance rules

- [`INDEX.md`](INDEX.md) is the routing table; group files are the source of
  truth.
- Update a group when a claim changes verdict, a seal lands, its objective
  priority changes, or a falsifier redirects the producer.
- Correct factual errors at their source. Historical prose may remain only
  when clearly marked superseded or wrong.
- Questions under `questions/` remain self-contained; project cross-references
  belong in the group file and index.
- Experiments remain isolated. Production modules never import
  `ephemeral/experiments`.
- Do not scaffold speculative APIs. Promote the smallest theorem surface with
  a known consumer, then generalize when a second use makes the abstraction
  real.
