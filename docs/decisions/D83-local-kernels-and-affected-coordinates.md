# D83: retain local kernels and distinguish affected coordinates from consent

- **Status:** existing deviation interface retained; no broader arena or law-transformer API admitted.
- **Date:** 2026-11-11
- **Experiment:** EXP-178

## Question and alternatives

Does the validated responsive matching displacement require an unrestricted
law-transformer interface? Compare use of the existing local kernel with
distinct deviator labels and affected coordinates against a whole-law operator.
The tested family keeps the institutional consent facts from EXP-177.

The existing interface realizes this family. No stable definition, probability
carrier, engine, arena, or certificate structure is added.

## Positive realization without vacuous locality

The explicit signature has four coordinates: the original two doctors and
hospital, plus an unrelated Boolean spectator. Two agents consent to the
replacement, three assignment coordinates change, and the spectator remains
outside the affected set.

The Unit-labeled scheme stores exactly those three affected coordinates and
one local replacement. Its local input cannot contain the spectator. The
proof establishes equality of the local inputs for both spectator values,
hence equal responses for every kernel with that input type, not merely for
the concrete constant replacement.

The exact endpoint law is proved for each spectator bit. The canonical
`apply_bind` theorem then yields the exact random-target law for a fair
spectator. Both endpoints have positive mass, the output is not a point mass,
and projecting its spectator coordinate recovers the complete original
spectator distribution. The canonical nonmember frame theorem applies to a
proper subset of the four coordinates.

Consent-only rewrites still cannot realize the target in this same enlarged
encoding, because the displaced incumbent must change. Separating consent
from affected coordinates removes that obstruction without dropping the
local-input or bind invariant. Projection recovers the already validated
native matching assignments, consenter gains and incumbent loss.

This validates a fixed displacement family. The local replacement is
deterministic; the genuine randomness is in the preserved spectator/status-quo
law. It does not provide arbitrary matching move availability, feasibility
preservation for arbitrary profiles, a general matching compiler, or a
universal expressivity theorem.

## Rejection control for unrestricted law operations

A Boolean-law operator returns `pure true` on `pure false` and `pure false`
otherwise. It fails preservation of the half-and-half mixture of the two
point masses. Therefore no single outcome kernel realizes that operator by
bind for every input law.

The quantifiers matter: this does not rule out choosing a separate kernel
for each fixed input law. A law-dependent selection among permitted deviations
is different from replacing the fixed-move application operation with an
arbitrary law transformer. No concrete game client in this experiment asks for
the latter operator.

An unrestricted replacement of the current interface would therefore admit
operations lacking an invariant already used by equilibrium reasoning.
Broadening it needs a named requiring client and an explicit treatment of
locality and law-linearity, not the observation that some consenters differ
from the coordinates affected by an institutional move.

## Admission and validation

Retain `DeviationScheme` and its typed local action and bind lift. Judge or
deviator labels are already separate from its affected-coordinate field.
Existing singleton recommendation-spying and nonmember controls remain in
`Tests.Locality`. The two probes are retained under `Experimental/Exp178/`
and included in the complete axiom audit.

Baseline: `18559255`; implementation checkpoint: `51e5e60a`. Exact commands:

```text
lake --iofail build GameTheory.Experimental.Exp178.LocalRealization GameTheory.Experimental.Exp178.LawTransformerBoundary GameTheory.Tests.Locality
python scripts/audit.py
```

The focused strict build passes 3,771 jobs. The full audit passes 3,873 default
and 4,772 validation jobs, public lint, authored diagnostic checks and transitive
standard-axiom checks. Raw output is ignored
`.codex/scratch/exp178/integration-audit.log`. Independent semantic review
accepts the stated fixed-family and uniform-kernel limits.

No alternate broad arena was implemented or timed, and no performance claim
is made. The initial six-question investigation is complete; this result
retains the accepted baseline rather than claiming that no future client can
justify a different abstraction.
