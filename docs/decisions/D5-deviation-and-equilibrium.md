# D5: one local, law-linear deviation predicate

- **Status:** accepted for the static core
- **Date:** 2026-07-26
- **Experiment IDs:** EXP-005, EXP-008; stable stress evidence EXP-029

**Decision:** Equilibrium of a law is defined once, by `IsEquilibrium`, from a
`DeviationScheme` whose local action function receives only the deviating
group's own recommendation. Pure Nash, mixed Nash, CCE, CE, and strong Nash are
choices of status quo and scheme. Best response, dominance, and
rationalizability keep their own profile-quantified shape and are *not*
instances of `IsEquilibrium`.

## Competing designs

1. Separate primitive definitions per concept, as in the bootstrap snapshot,
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

## Cost of specialization

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
every scheme. Under expected utility, an integrable randomized replacement
cannot beat all deterministic ones. D62's general PMF semantics requires that
mixture integrability explicitly: integrability of each deterministic play
law alone does not establish it.

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

EXP-029 tests the same game through `InformationModel`. The prior-weighted
interim theorem is an
equivalence with ordinary `IsNash`; the protocol-backed fair-bit endpoint uses
the same predicate after the policy/plan and outcome-law equalities. No
`BayesNash` definition or wrapper was introduced.

## Result

Accept for the static core. Sequential rationality and conditional beliefs may
require a named observation-dependent deviation interface. Such an interface
must preserve this static interface's locality guarantee; its existence alone
does not justify widening the information available to a static deviation.

## Consequences for public API

`IsEquilibrium` is the only equilibrium-of-a-law predicate. New solution
concepts arrive as new `DeviationScheme` values plus a transparent definition.
Any concept quantifying over opponents' profiles belongs to
`GameTheory.Core.Response` instead. Executable checkers prove correctness
against these predicates and never introduce their own.
