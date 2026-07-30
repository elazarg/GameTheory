# D5: one local, law-linear deviation predicate

- **Status:** accepted for the static core (Phase 2 gate); the interface is
  re-tested against sequential deviations in Phase 3
- **Date:** 2026-07-26
- **Experiment IDs:** EXP-005, EXP-008; stable stress evidence EXP-029

**Decision:** Equilibrium of a law is defined once, by `IsEquilibrium`, from a
`DeviationScheme` whose local action function receives only the deviating
group's own recommendation. Pure Nash, mixed Nash, CCE, CE, and strong Nash are
choices of status quo and scheme. Best response, dominance, and
rationalizability keep their own profile-quantified shape and are *not*
instances of `IsEquilibrium`.

## Competing designs

1. Separate primitive definitions per concept, as in the pinned v1 snapshot,
   which exposes `NFGGame.IsNashPure`, `KernelGame.IsNash`, `GameForm.IsNashFor`
   and `BayesianGame.BayesNash` as different logical surfaces.
2. One equilibrium predicate whose deviations receive the whole profile. This
   is expressible but cannot enforce recommendation locality.
3. One equilibrium predicate whose deviations receive only the affected
   subprofile. Selected.

## Representative examples

Four schemes (`unilateralConstant`, `recommendation`, `unilateralRandomized`,
`coalitionConstant`), three scheme morphisms, the five concepts, and the hostile
file `GameTheory/Tests/Locality.lean`.

## Measurements

Run:

```text
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

| Metric | Value |
|---|---:|
| Public `def`s per solution concept | 1 each, 11 concepts |
| Separate definitions of mixed Nash | 0 (`IsNash F.mixed`) |
| `Function.update` outside the profile module | 0 |
| Source-level transport tokens in Phase 2 source | 1 |
| Source-level transport in the designated profile module | 1 |
| `sorry` / `admit` / `native_decide` / custom axioms | 0 |

Proof sizes of the cross-concept theorems: `isNash_iff_isCoarseCorrelatedEq_pure`
is `Iff.rfl`; `IsCorrelatedEq.isCoarseCorrelatedEq` is one term;
`IsStrongNash.isNash` is four lines.

## Evidence that locality is enforced by types

`Subprofile.singletonEquiv` proves

```text
Subprofile sig {who} ≃ sig.Strategy who
```

so the argument of a unilateral `actLocal` carries exactly the deviator's own
strategy. A recommendation-spying CE deviation is therefore not expressible,
which is stronger than a checked compile failure. `Profile.override_of_not_mem`
proves nonmember coordinates survive, and
`DeviationScheme.exists_agree_off_members` lifts that to every profile in the
support of a deviated law.

Law-linearity is structural: `DeviationScheme.apply` is the only place a
deviation meets a status-quo law, it acts by `bind`, and `apply_bind` holds for
every scheme. `isCoarseCorrelatedEq_randomized` shows that under expected
utility a randomized replacement cannot beat all deterministic ones, so
defining CCE with deterministic deviations does not weaken it.

## Unexpected costs

The coalition scheme's deviator type is `{ members : Finset ι // members.Nonempty }`
rather than `Finset ι`, because the empty coalition would make the
"some member does not gain" preference unsatisfiable. The singleton-coalition
morphism needs `Subprofile.single`, which is the library's only transport.

`IsStrongNash` also inherits a genuine sensitivity to preference totality from
`Preference.coalition`: for a partial preference, "some member weakly prefers
the status quo" is strictly stronger than Aumann's "the members do not all
strictly gain". `isStrongNash_iff_not_all_gain` states the equivalence with
`Preference.Total` as an explicit hypothesis, and the unconditional direction is
`Preference.not_forall_strict_of_coalition`. The reasoning is recorded in
[`D4-form-preference-utility.md`](D4-form-preference-utility.md).

## Kill condition

Reject or extend the local-kernel design if a standard in-scope concept needs a
deviation depending on the full prior law or on information not expressible as
the affected subprofile. Reject the single equilibrium predicate if its
specializations need more boilerplate than direct definitions.

Neither fired. All five concepts are one line each on top of `IsEquilibrium`,
and the Bayesian probe (EXP-008) showed that an interim, type-dependent
deviation is also expressible without widening the interface.

EXP-029 promotes that result from a probe to stable API and compiles the same
game through `InformationModel`. The prior-weighted interim theorem is still an
equivalence with ordinary `IsNash`; the protocol-backed fair-bit endpoint uses
the same predicate after the policy/plan and outcome-law equalities. No
`BayesNash` definition or wrapper was introduced.

## Result

Accept for the static core. The decision is explicitly re-opened in Phase 3 for
sequential rationality, conditional beliefs, and one-shot deviations: those may
require an explicitly named observation-dependent deviation interface, which
D5 permits as a *new* named interface rather than a weakening of this one.

## Consequences for public API

`IsEquilibrium` is the only equilibrium-of-a-law predicate. New solution
concepts arrive as new `DeviationScheme` values plus a transparent definition.
Any concept quantifying over opponents' profiles belongs to
`GameTheory.Core.Response` instead. Executable checkers prove correctness
against these predicates and never introduce their own.
