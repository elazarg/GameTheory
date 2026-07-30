# D4: game form, preference, and utility are separate data

- **Status:** accepted
- **Date:** 2026-07-26
- **Experiment IDs:** EXP-006

**Decision:** The utility-free `GameForm` is canonical. A `WeakPreference` over
outcome laws is an explicit argument, never a typeclass instance. Expected
utility is a derived preference (`euPreference`), specialized to `ℝ`, and is not
a second definition of any solution concept.

## Argument orientation

`weaklyPrefers agent preferred alternative` means `agent` weakly prefers
`preferred` to `alternative`. Every public definition names its two law
arguments (`preferred`/`alternative`, `statusQuo`/`deviated`), so reversing them
is a visible error. Reflexivity is a named property
(`Preference.Reflexive`), required only where a theorem treats a no-op as an
allowed deviation; it is not baked into the relation type.

## Representative examples

- ordinal Nash under an arbitrary law preference: `IsNash F weaklyPrefers σ`;
- expected-utility Nash as the same predicate at `euPreference u`;
- positive-affine utility invariance: `euPreference_affine`;
- outcome relabeling with utility pullback: `isNash_mapOutcome`;
- Pareto dominance and efficiency: `ParetoDominates`, `IsParetoEfficient`;
- a downstream file that switches one Prisoner's Dilemma form from
  `euPreference` to a purely ordinal `bestCasePreference`.

## Measurements

| Metric | Value |
|---|---:|
| Public definitions of Nash | 1 |
| `IsNash_iff_IsNashFor_eu`-style bridging theorems | 0 |
| Casts in the outcome-relabeling statement | 0 |
| `show` needed in the outcome-relabeling *proof* | 1 |
| Preference-generic concepts reused at `euPreference` | 11 |

There is no rewrite pattern between an "ordinal" and an "expected utility"
predicate because there is only one predicate; the preference is an argument.
The one `show` in `isNash_mapOutcome` is a transparency artifact of D1's
bundled form, recorded there rather than here.

## Partial preferences and the coalition lift

`WeakPreference` is allowed to be partial; nothing in D4 assumes totality, and
the ordinal `bestCasePreference` used in the examples is not total. Exactly one
definition depends on that freedom, and the dependence is now explicit.

`Preference.coalition` says a coalition weakly prefers the status quo when
*some* member does. Aumann's usual phrasing, "the members do not all strictly
gain", is equivalent only under totality, because an *incomparable* member
neither weakly prefers the status quo nor strictly gains:

- `Preference.not_forall_strict_of_coalition` holds with no hypothesis, so the
  definition used here always implies Aumann's reading;
- `Preference.coalition_iff_not_forall_strict` and the concept-level
  `isStrongNash_iff_not_all_gain` take `Preference.Total` as a hypothesis.

The chosen definition is therefore the stricter of the two: a coalition's
deviation is refused only when some member is affirmatively not made worse off,
so fewer profiles are strong Nash under a partial preference. Under expected
utility, `euPreference_total` closes the gap and the two readings coincide with
the textbook concept.

## Rejected sub-proposal

The D4 validation spike proposed implementing the algebraic finite-expectation
lemmas once over the weakest practical ordered-field assumptions and
instantiating them at `ℚ` and `ℝ`, to be kept only if it removed genuine
duplication. It did not. Real expectation goes through `FinDist.expect`, which
is `ℝ`-valued by construction because the representation's weights are
`ENNReal`; the executable rational side computes `Finset.sum` over an explicit
table and never constructs a `FinDist`. The two paths share no lemma, so a
scalar-polymorphic layer would have added a parameter without removing a
theorem. No such layer was added.

## Kill condition

Revise the separation if basic expected-utility statements require pervasive
dependent projections or if type inference cannot recover the form from an
evaluation. Neither occurred: `UtilityGame` is a plain dependent pair and is
optional; every theorem above takes the form and preference explicitly.

## Result

Accept. Expected utility stays specialized to `ℝ`. Algebraic generalization of
the payoff scalar is deferred until a concrete second use case appears, and it
may not choose the probability representation or create a second mixed-game API.

## Consequences for public API

`euPreference` is a definition of *data*, not of a concept. Bundling a form with
a utility (`UtilityGame`) is an ergonomic option; generic theorems continue to
take the form and preference as separate arguments.

## Phase 5 stress refinement

[EXP-027](../ExperimentLog.md) proved Arrow's theorem against whole profiles of
linear rankings. The semantic split survived: the theorem uses the same
`Ranking`, `Rank.Linear`, and `Rank.strict` vocabulary, and the strict-order
pivotal construction is a private proof representation rather than a second
preference API.

The import split had not survived. Before EXP-027, `Core/SocialChoice.lean`
imported `Core/Preference.lean`, so `FinDist` was reachable even though no
social-choice declaration mentioned probability. The generic relation algebra
now lives in `Core/Rank.lean`; lottery-specific convexity and relabeling remain
in `Core/Preference.lean`, which imports `Rank` in the one allowed direction.
Negative reachability probes now keep `FinDist` out of both `SocialChoice` and
`Arrow`. This refines D4's physical boundary without changing any accepted
semantic declaration.
