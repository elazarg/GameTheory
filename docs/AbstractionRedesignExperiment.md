# Abstraction building-block experiment

Status: items 01 and 02 accepted; item 03 collected as a refuting experiment.
Item 04 factors guarded local judgment without replacing numerical contexts.
Item 05 localizes coalition comparisons and separates consent from affected
coordinates. All five pass full integration audits. Item 06 remains gated.
No judgment hierarchy is adopted.

Item 01 selects direct preference-generic exact-law proofs after comparing the
existing coverage API on the same statements. See [D78](decisions/D78-preference-generic-exact-law-bridges.md)
and EXP-173 for measurements and limits.

Item 02 selects guarded relation-based response definitions and direct
finite-range improvement-rank hypotheses. The partial-preference and
singleton-strategy controls delimit the assumptions; numerical potential and
congestion consumers remain supported. See
[D79](decisions/D79-ordinal-response-and-improvement-ranks.md) and EXP-174.
No new ordinal-potential structure is admitted.

Item 03 refutes binary convexity as sufficient for arbitrary PMF mixture
closure, even for a total preorder. Its direct client prototypes retain
separate sources of expectation-definedness and remain experimental. See
[D80](decisions/D80-binary-and-countable-mixture-closure.md) and EXP-175.
Item 04 selects the independent `Math.GuardedOptimality` predicate and makes
numerical local optimality an exact specialization. A stochastic nonnumeric
consumer, nonbijective law coverage and concrete undefined/infinite-value
controls pass. The relation-valued Context record remains experimental;
higher sequential APIs keep their existing numerical semantics. See
[D81](decisions/D81-guarded-protocol-comparison.md) and EXP-176.
Item 05 selects actual-law, member-local comparison theorems while preserving
the existing strong-Nash and matching meanings. Fixed strict unanimity does
not turn its no-gain relation into a preorder; a valid responsive blocker can
harm a nonconsenting incumbent. See
[D82](decisions/D82-local-coalition-comparison-and-consent.md) and EXP-177.
No first-class coalition problem is admitted. Item 06 remains a question.

The question is which small building blocks make independently useful
generalizations cheap on the existing semantics. The starting evidence is
[Abstraction analysis](AbstractionAnalysis.md) and
[Survey evidence](SurveyEvidence.md). Their classifications are hypotheses to
test, not a target architecture to implement rung by rung. EXP-173 owns the
first comparison and its observations in [ExperimentLog.md](ExperimentLog.md).

## Constraints and alternatives

The accepted defaults remain [D5](decisions/D5-deviation-and-equilibrium.md),
[D7](decisions/D7-certificate-stratification.md),
[D8](decisions/D8-minimal-transformations.md), and
[D60](decisions/D60-noninvertible-strategic-transfer.md). In particular:

- `IsEquilibrium` owns equilibrium of a law; response and dominance keep their
  profile-quantified meanings.
- Locality and law-linearity remain enforced by `DeviationScheme`'s type and
  its `bind` construction. An arbitrary law transformer would lose both.
- Direct theorem hypotheses and existing coverage are the baseline. New
  records, probability interfaces, certificate hierarchies, or category
  instances must earn admission independently; none follows from naming levels.
- General PMF semantics and actual-law expectation-definedness survive every
  specialization. Finiteness belongs to operations requiring it.

Invariance under re-encoding is diagnostic evidence. It neither constructs a
generalized definition nor proves that a theorem descends to a proposed level.
The distinction between outcome utility and a relation on lottery laws matters:
mixed Nash can be defined for arbitrary lottery preferences even when a
particular existence or representation argument needs expected utility.

## Branch and integration discipline

The collecting branch is `codex/experiment-abstraction-building-blocks`.
Commit the two survey documents and this plan there. Each item starts from the
latest accepted collecting tip on
`codex/experiment-abstraction-item-NN-<subject>`. Preserve item branches as
evidence; merge successful, warning-clean slices back into the collecting
branch. A rejected design is a useful outcome: integrate its documented result
and necessary counterexample, without promoting its rejected API.

Use this checkout only, with no worktrees. Independent analysis or drafting may
run in parallel in disjoint files or ignored `.codex/scratch/` folders. Branch
switching, tracked integration edits, and compilation are serialized. Stop all
edits before each build. Commit and push small reviewable checkpoints, naming
unvalidated checkpoints explicitly; branch publication is not API admission.
Keep unrelated user changes out of experiment commits.

## Item 01: preference-independent bridge transfer

**Question.** Can law equalities and unilateral coverage generalize real
language bridges without a new transport structure or a deviation bijection?

Compare three concrete implementations of the same generalized statements:

1. Direct bridge-local proofs using the named honest and updated-law theorems.
2. Existing `IsNash.of_coverage`, supplying equality-induced comparison
   implications for the source and target preferences.
3. A direct generic law-coverage theorem, only if the first two expose repeated
   useful work. Its hypotheses must cover every target deviation; equality of
   honest laws alone is insufficient. Compare its total cost against (2).

The target clients are both directions of the EFG behavioral/mixed Kuhn Nash
transfer and a second bridge with different policy or outcome shape, initially
Bayesian-to-Protocol or native MAID compilation. The generalized statements
quantify over a `WeakPreference`; bridges changing outcome carriers use the
existing preference pullback along an outcome map. Existing expected-utility
consequences must follow as specializations, with their original mathematical
scope. Do not infer same-epsilon utility transfer from a generic ordinal
theorem without supplying its slack comparison.

Kuhn conversions need not be inverses as strategies: coverage of deviated laws
is the required property. Do not impose a deviation equivalence merely to fit
the survey sketch. No CE/CCE transport follows from profile-dependent Nash
coverage; those concepts require recommendation-local coverage.

**Hostile controls.** Use a genuinely mixed deviation and a nonconstant law
affected by the other player's strategy. Exercise different outcome carriers
in the second client where available. Preserve or reuse a negative control
where honest laws agree but an extra target deviation breaks equilibrium.
Demonstrate a non-expected-utility preference consumer so the new quantifier is
used. Existing Kuhn and bridge fixtures remain downstream consumers.

**Admission.** Choose the smallest implementation which preserves the
statements and passes the shared checks below. A successful result can be
"existing coverage is sufficient"; it need not add a generic theorem. Record
which bridge facts remain genuinely language-specific, and which surveyed
claims were narrowed or refuted.

## Item gates and outcomes

| Item | Question and target | Required evidence before admission |
| --- | --- | --- |
| 02: ordinal response (accepted, EXP-174/D79) | Can strict Nash, improvement paths, and an ordinal-potential existence theorem use `Ranking` and explicit order laws? | A nonnumeric preference consumer; expected-utility specialization with its definedness guard; partial-preference separation; finite maximization assumptions stated precisely. Generalize one dependency chain before adding adjacent concepts such as properness. |
| 03: mixture closure (binary-only refuted, EXP-175/D80) | Which law is sufficient for mixed dominance and pure-deviation reduction? | Separate binary mixing, finite iteration, and closure under arbitrary PMF `bind`. Test infinite-support mixtures and retain actual compared-law expectation premises. Compare named hypotheses with a proposed reusable law; do not call binary convexity countable betweenness. |
| 04: Protocol judgment (local comparison accepted, EXP-176/D81) | Can comparison of continuation laws be separated from numerical continuation evaluation? | Preserve candidate and alternative expectation-definedness in the numerical specialization; a nonnumeric local-optimality consumer; existing terminal rationality, Bayes consistency, and proper-subgame semantics preserved. Historywise one-shot results must retain their exact scope and the recorded SPE counterexamples. |
| 05: coalition judgment (local agreement accepted, EXP-177/D82) | Does strict unanimity provide useful shared transport for strong Nash and matching? | Incomparability example distinguishing absence of strict gain from weak equilibrium; nonempty-coalition policy; per-member quantifiers; agreement under explicit totality. Any change of meaning requires a decision, not a silent restatement. |
| 06: arena and deviations | Is a more general deviation carrier needed by a named client? | A client the current local scheme cannot express, plus explicit locality and law-linearity enforcement or a demonstrated boundary explaining why they do not apply. Re-run the recommendation-spying and nonmember-coordinate controls. Compare with a separate consumer-local interface before replacing the static core. |

These are investigation gates, not a promise to add six interfaces. Reorder or
stop after an item when its evidence changes the useful next question. Items
03–06 require fresh competing designs and an experiment reservation before
architecture-sensitive implementation begins. EXP-173 does not pre-approve
their APIs. Ordinal recovery needs a new design experiment only if it changes
accepted foundations rather than generalizing on the settled API.

## Measurements and validation contract

Before editing each slice, record its baseline commit and inspect the actual
declarations and Mathlib APIs. Keep alternative probes and raw diagnostics in
ignored `.codex/scratch/`, never in `.lake/`. Compile one definition or theorem
at a time after inspecting its goal. Rebuild changed imports before downstream
single-file checks.

Measure declaration, construction, and client nonblank lines separately;
charge shared infrastructure once and report cold and reused costs. Compare
equivalent statements, include actual-law guards equally, and retain failed
alternatives. Use at least three alternating serialized runs for elaboration
comparisons; distinguish import-inclusive process time from command time.
Record exact commands, dependency/toolchain identity, and medians.

The D7/D60 budgets are the initial rejection thresholds for new bundled
abstractions: declaration plus construction above twice the direct baseline,
or more than 25% elaboration overhead, rejects or narrows admission. A new
record also needs two independent consumers or checked composition and must
enable a theorem not already supplied by the existing concrete surface.
Theorem-only alternatives should demonstrate reduced duplication or genuinely
useful generality without importing an unused abstraction. Do not conceal a
failed cold-cost budget behind shorter client code.

Every accepted slice needs a positive canonical consumer, a nearby rejection,
preservation of the old specialization, no new trusted axioms or proof holes,
and no forbidden dependency or source-level transport plumbing. Run:

```text
lake --iofail build <changed-owner-and-consumer-targets>
python scripts/audit.py --source-only
```

When adding, moving, or deleting authored modules, update both lint and axiom
drivers, clear deleted modules' generated build artifacts, then rebuild the
lint driver before `lake lint`. Run the appropriate transitive axiom checks for
the changed scope. Full audit belongs at an integration gate or when imports
or package configuration change, rather than each proof iteration.

Record observations and outcomes in the owning EXP entry; synthesize adopted
architectural consequences in a decision record citing that entry. Update the
owning [delivery ledger](DeliveryLedger.md) row in the same integration commit
as the evidence. This plan tracks questions and gates; the ledger tracks
delivered capability. Keep experiment and decision identifiers out of stable
Lean docstrings.
