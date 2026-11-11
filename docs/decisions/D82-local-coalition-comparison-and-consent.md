# D82: local coalition comparisons and the consent boundary

- **Status:** theorem-level extension adopted; no shared coalition structure admitted.
- **Date:** 2026-11-11
- **Experiment:** EXP-177

## Question and selected building block

Does strict unanimity provide a shared coalition interface for strong Nash and
responsive matching? The useful public factor is a theorem about local
comparability, rather than a new representation of coalition problems.

`Preference.coalition_iff_not_forall_strict_of_comparable` needs each member
to compare just the two supplied outcomes.
`isStrongNash_iff_not_all_gain_of_comparable` needs those comparisons only
at the actual incumbent and each nonempty coalition's joint replacement.
Preferences on other laws may remain partial. The former global-totality
theorems keep their signatures and specialize these local results.

Comparability is sufficient, not asserted necessary for every individual
instance of the equivalence. A weak rejection by one member can settle a
coalition even if another member's comparison is undefined or incomparable.
The statements preserve one joint replacement shared by all members; they do
not replace it with separate per-member witnesses.

## Semantic separation

Strict unanimity is irreflexive and transitive for a fixed nonempty coalition
when its members have transitive rankings. Its no-strict-gain relation need
not be transitive, even with total individual preorders. The explicit
three-outcome, two-member control demonstrates the failure.

Equality preferences give an actual game with no strictly gaining coalition
replacement, while the canonical weak-form strong-Nash predicate fails.
The alternative reading can already use `IsEquilibrium` with a different
lawless coalition relation and the existing deviation scheme. No new engine
is needed, and silently changing `IsStrongNash` would change its meaning.

Strict unanimity over the empty set is vacuous even for an unchanged outcome.
The existing nonempty-coalition subtype excludes this case. It remains part
of the semantic interface, rather than a convention in a module directory.

The stable two-player control has a partial-order preference on laws and a
fair law incomparable with the relevant point masses. All-false is ordinary
Nash but a joint replacement defeats strong Nash. All-true satisfies strong
Nash through the actual-law local comparison theorem, despite failure of
global totality. This is a genuine weakening of an over-global assumption,
not a new coalition solution concept.

## Matching consent is not the affected-coordinate set

The responsive matching control has two doctors and one capacity-one hospital.
A newcomer and the hospital strictly gain by replacing the incumbent.
Both assignments are feasible and individually rational, but the incumbent
is outside the consenting pair and strictly loses.

In the tested direct assignment-coordinate representation, no local kernel
whose affected coordinates are restricted to the consenting pair can produce
the target profile. The proof uses the existing nonmember-coordinate
invariant of `DeviationScheme`. This does not rule out other game encodings
or schemes with a different affected set.

A partial equality-ranking market is stable with no strict blocking pair,
yet neither party positively weakly rejects the hypothetical match. Thus the
native strict-blocking test also cannot be replaced unconditionally by weak
coalition rejection. The partner carriers are heterogeneous; no ranking over
arbitrary hospital teams or new shared outcome representation is assumed.

## Admission and validation

The two public comparison lemmas add no stable definitions, structures,
equilibrium engine or probability representation. Existing matching and
strong-Nash definitions are unchanged. Direct member comparisons and
`Rank.strict` already carry the tested strict-unanimity facts. A new coalition
problem record was not implemented or timed; no cold-cost or speed claim is
made for an unimplemented candidate.

Baseline: `ab6c61b9`; implementation checkpoint: `f03c9d65`. The focused
strict owner/control build passes 3,056 jobs, and source checks pass. Stable
controls are in `Tests.CoalitionComparison`; representation candidates and
rejections are retained under `Experimental/Exp177/`.

The full integration result is recorded in EXP-177 and the delivery ledger.
The remaining arena gate must distinguish affected coordinates from consenting
judges and test the existing interface before broadening law transformers.

`python scripts/audit.py` passes the default strict build (3,873 jobs), complete
validation build (4,770 jobs), public lint, authored diagnostic checks and
transitive standard-axiom checks. The audit includes native matching,
coalition-simulation and existing locality consumers. Raw output is
`.codex/scratch/exp177/integration-audit.log`. Independent semantic review
found no blocker within the stated theorem-level and representation scope.
