# D81: guarded comparison is separate from numerical continuation contexts

- **Status:** adopted for local judgment and coverage; relation-valued Context record not selected.
- **Date:** 2026-11-11
- **Experiment:** EXP-176

## Question and alternatives

Can context-local optimality support nonnumeric comparisons without changing
the guarded expected-utility meaning of Protocol contexts? Compare a
probability-independent predicate taking admissibility and comparison as
separate arguments with a record storing outcome laws, a law-domain predicate,
and a preference over laws.

Both candidates compile the same numerical and stochastic belief/coverage
clients. Select the direct predicate. The record adds no needed capability in
this slice and remains experimental; it is not mathematically refuted.

## Selected owner and numerical specialization

`GameTheory.Math.IsOptimalOn`, owned by `Math.GuardedOptimality`, requires admissibility of the chosen
element, admissibility of every allowed alternative, and the chosen comparison
against every allowed alternative. No order laws, probability carrier, finite
enumeration or game data enter the predicate or its coverage theorem.
Mathlib's `IsMaxOn` uses an ordered score and does not carry these independent
domain guards; `IsGreatest` additionally requires candidate membership.

`Protocol.Context.IsLocallyOptimal` is a transparent specialization at
`HasValueAt` and extended-value comparison. The full original three-part
numerical shape is definitionally equal to this specialization, including the
incumbent guard for an empty allowed set. The context retains its outcome and
numerical continuation data. `ContextTransport` now consumes the mathematical
coverage theorem rather than owning a separate optimality argument.

A named numerical inequality projection handles the beta-reduction boundary
in backward induction. No theorem gains assumptions, and the local-to-global
or one-shot arguments still use the existing expected-utility hypotheses.
D64 terminal whole-policy rationality and the D72/D73 belief restrictions are
unchanged. This is not a generic SPE, PBE, or sequential-equilibrium API.

## Hostile evidence

A fair hidden state and one shared branch kernel induce a fair outcome law
for the chosen action and a sure successful outcome for the alternative. A
possibility preference accepts the chosen law, while the numerical 0/1 payoff
rejects it. The preference already has a proved absence of real expected-utility
representation. Optimality transfers to three target choices with two choices
sharing one source law; no choice equivalence or inverse is assumed.

Signed geometric tails yield an actual PMF whose expected gains and losses
are both infinite. The tests reject an undefined incumbent even when there
are no alternatives. They also reject local optimality with a defined incumbent
and an undefined allowed alternative, despite absence of a profitable deviation.
A separate negative-infinite law is admissible and nonintegrable, so replacing
definedness with finite-value integrability would lose this positive control.

The stable controls use the selected mathematical API. The measured record
alternative and its direct baseline are retained in
`Experimental/Exp176/Comparison.lean`.

## Measurements and limits

Three alternating serialized runs used identical imports and shared fixtures:

| Standalone comparison | Direct predicate | Record |
| --- | ---: | ---: |
| Nonblank code lines, including shared helpers and fixtures | 124 | 147 |
| Median whole-process seconds | 10.728 | 10.648 |

The record has 23 more lines in this comparison. The ratio is about 1.19;
this is not a failure of the two-times budget. Import-inclusive process times
do not isolate theorem elaboration and establish no speed advantage. The old
bespoke transport was not a separate timed candidate. The selected factor is
justified by useful nonnumeric judgment and independent guards, not by a claim
of reducing existing numerical client length or accelerating elaboration.

Reproduce with `python scripts/compare_context_judgment.py`. Raw generated
sources, source counts, per-run diagnostics and timings live in ignored
`.codex/scratch/exp176/`. The initial baseline is `13b85eb1`; the selected
implementation checkpoint is `20adafa2`.

## Validation and next boundary

The independent mathematical owner builds in 115 jobs. The focused strict
Protocol and control build passes 3,182 jobs, including terminal behavioral
contexts, subgame perfection and decision experiments. Source checks pass.
The full integration result is recorded in EXP-176 and the delivery ledger.

A future caller needing generic families of sequential comparisons must
supply a real consumer before changing the numerical context representation.
No new context or certificate hierarchy follows from this factorization.
Coalition judgment and broader deviation arenas remain separate gates.

`python scripts/audit.py` passes the default strict build (3,873 jobs), the
complete validation build (4,767 jobs), public lint, authored diagnostic checks
and transitive standard-axiom checks. The audit includes finite sequential,
weak-PBE and conditional-PBE consumers and the proper-subgame boundary tests.
Raw output is `.codex/scratch/exp176/integration-audit.log`. Independent semantic
review found no blocker within the stated local-judgment scope.
