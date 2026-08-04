# The zero-loss projective-tail extraction is hypothetical

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `OPEN`, and the machinery is currently **unconsumable** |
| Objective priority | `P1` |
| Last audited | 2026-08-04, `7d518eb` |
| Central live claim | The zero-loss projective-tail extractors have no caller that can supply their loss hypothesis, and the naive per-step route to supplying it is expected false. The honest discharge is subsequence-level. |
| Next discriminant | Prove the subsequence-level discharge, or demote the extractors to a hypothetical interface with that fact recorded. |
| Production destination | `QuittingDynamicDebtProjectiveTail`, `QuittingDebtProjectiveTail` |
| Supersedes / superseded by | none |

## Claim ledger

| Claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- |
| The zero-loss projective-tail extractors have no caller discharging their loss hypothesis | `PROVED` | `M` `[reported, source-checked by the miner]` | both projective-tail modules | this claim |
| The positive-limit file's extraction never uses the calibrated loss bounds | `PROVED` | `M` `[reported]` | as above | as above |
| Per-step plateau rigidity transferred from the static lane is **false** | `OPEN`, expected false | `I` | dynamic debt | blocks the naive discharge |
| Plateau differences tending to zero, plus the calibrated argmax-loss bound, give zero first-edge loss **along a subsequence** | `OPEN` | `I` | the honest statement | the discharge to aim at |

## Why this is a defect and not a wish

This is not a missing enhancement. A lemma whose hypothesis no caller can
supply is machinery that looks available and is not: a future worker reads the
extractor's statement, assumes the loss hypothesis is routine, and builds on a
step that cannot be taken. The cost is paid later and by someone else.

The specific shape: the extractors take a zero-loss hypothesis on the
projective tail. The file that would use them — the positive-limit extraction —
never invokes the calibrated loss bounds that would establish it, so the
hypothesis is never discharged anywhere in the tree.

## Why the obvious repair fails

The static lane has a per-step plateau rigidity argument, and transferring it
verbatim is the natural first attempt. It is expected to fail, for a structural
reason worth recording: **dynamic debt does not factor multiplicatively**, and
minimizers at consecutive cutoffs are selected independently. So there is no
per-step transfer of rigidity from one cutoff's minimizer to the next.

## The honest statement to aim at

Subsequence-level rather than per-step: plateau differences tend to zero, and
the calibrated argmax-loss bound then gives zero first-edge loss **along a
subsequence**. That is weaker than the extractors currently assume, and any
consumer must be restated to accept a subsequence.

## Falsifiers and wrong turns

- If a caller *is* found that discharges the loss hypothesis, this claim is
  wrong and should be deleted rather than softened. The audit was a source
  read, not a proof.
- Do not repair by strengthening the extractors' conclusion; the gap is in the
  hypothesis, and a stronger conclusion makes it worse.
- Do not transfer per-step rigidity from the static lane without first checking
  multiplicative factorization — that is exactly the step expected to fail.

## Production map

Both projective-tail modules are in the import graph and build. Nothing is
unsound: the extractors are true statements. What is missing is any path from
the repository's actual data to their hypotheses. Until the subsequence-level
discharge lands, treat every downstream use as conditional and say so at the
use site.

## Exit conditions

`MINED` when the subsequence discharge is proved and a consumer is restated to
match, or when the extractors are explicitly demoted to a hypothetical
interface with this claim linked from their docstrings.
