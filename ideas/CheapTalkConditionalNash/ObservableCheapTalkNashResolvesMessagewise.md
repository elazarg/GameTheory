# Observable cheap-talk Nash resolves messagewise

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `OPEN`, maturity `I` | Proof-mining §41, extracted 2026-08-03 | Target: `Communication/CheapTalkPublicRandomness.lean` | `PENDING`; prove the localized deviation before promotion |

## Proposed theorem and proof obligation

The existing disintegration writes the outcome as a public message law and a
conditional independent mixed base profile `publicPlay τ m`. Fix a message
profile `m` of positive probability. If player `i` has a profitable pure
deviation from `publicPlay τ m`, push forward their distribution over cheap-
talk pure strategies so that the emitted message is unchanged and the action
plan changes only when the observed full message is `m`. The ex-ante gain
should equal `Pr(m)` times the positive conditional gain, contradicting Nash.

If the calculation lands, every mixed cheap-talk Nash law is a public mixture
of mixed-Nash laws, strengthening the current correlated-equilibrium output.

## Falsifiers and nonclaims

- This depends on simultaneous messages and observability of the full message
  profile before action. It is not a theorem about arbitrary protocols,
  private messages, sequential cheap talk, or commitment.
- Zero-probability messages impose no conditional Nash requirement.
- The key pushforward must be a legal unilateral deviation under the exact
  strategy timing. If it changes the message distribution or off-event plan in
  a payoff-relevant way, the proof fails.

Audience/value: communication games and formal protocol semantics. Novelty is
unassessed. Promote to `INDEPENDENT` only after the timing calculation is
machine-checked or independently proved.
