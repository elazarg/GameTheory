# Phase 2 incentive vertical slice gate

Phase 2 of the RFC's dependency-gated spike is complete. Its gate condition is

> Phase 3 starts only after the single equilibrium predicate has expressed Nash,
> CCE, CE, and strong Nash without violating locality.

which is met, together with the remaining Phase 2 deliverables.

## What was built

| RFC Phase 2 item | Where | Status |
|---|---|---|
| form, preference, utility evaluation, profile operations | `GameTheory/Core/Signature.lean`, `Form.lean`, `Preference.lean`, `Utility.lean` | done |
| local deviation schemes and preference orientation | `GameTheory/Core/Deviation.lean`, `Preference.lean` | done |
| Nash, mixed Nash, CCE, CE, strong Nash | `GameTheory/Core/Equilibrium.lean` | done |
| best response, dominance, rationalizability as profile-quantified concepts | `GameTheory/Core/Response.lean` | done |
| Bayesian interim-deviation scope probe | `GameTheory/Experimental/Phase2/BayesianProbe.lean` | done |
| rational finite-table frontend and its first correctness theorem | `GameTheory/Finite/Algorithm.lean`, `Correctness.lean` | done |
| four executable examples and proof-semantic equivalence tests | `GameTheory/Examples/Classic.lean` | done |

RFC 7.2's vertical-slice list is satisfied for items 1, 2, 6 (mixed-extension
transport only), 7, and 11; item 12 is the Bayesian probe. Items 3, 4, 5, 8, 9,
and 10 are Phase 3 and Phase 4 work and are untouched. Player reindexing
(item 6's first half) belongs to D8's transformation taxonomy in Phase 4 and was
deliberately not built here.

## Decisions recorded

| Decision | Status after Phase 2 | Record |
|---|---|---|
| D4 form/preference/utility separation | accepted | [`decisions/D4-form-preference-utility.md`](decisions/D4-form-preference-utility.md) |
| D5 one local deviation predicate | accepted for the static core | [`decisions/D5-deviation-and-equilibrium.md`](decisions/D5-deviation-and-equilibrium.md) |
| D9 independent finiteness capabilities | accepted | [`decisions/D9-finiteness-capabilities.md`](decisions/D9-finiteness-capabilities.md) |
| D10 executable rational frontend | accepted | [`decisions/D10-executable-frontend.md`](decisions/D10-executable-frontend.md) |
| D1 signature ownership | still provisional, new negative evidence | [`decisions/D1-signature-ownership.md`](decisions/D1-signature-ownership.md) |
| D2 finite-law representation | adopted, two kill tests passed | [`decisions/D2-finite-law-representation.md`](decisions/D2-finite-law-representation.md) |

Raw evidence is EXP-005 through EXP-008 in [`ExperimentLog.md`](ExperimentLog.md).

## Gate commands

```text
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

`lake build` now covers every module, including examples, architecture tests,
and experiments, because the library target globs submodules. The audit ends in
`VERIFIED=1` or throws.

## Measured state

| Measure | Value |
|---|---:|
| `GameTheory/Probability` nonblank lines | 409 |
| `GameTheory/Core` nonblank lines | 1017 |
| `GameTheory/Finite` nonblank lines | 326 |
| `GameTheory/Examples` nonblank lines | 199 |
| `GameTheory/Tests` nonblank lines | 98 |
| Phase 2 Bayesian probe nonblank lines | 158 |
| Public definitions per solution concept | 1 each, 11 concepts |
| `Function.update` outside the profile module | 0 |
| Source-level transport tokens in Phase 2 source | 1 |
| Source-level transport in the designated profile module | 1 |
| `ENNReal`/`toReal`/`PMF`/`toPMF` outside the representation module | 0 |
| `sorry`, `admit`, `native_decide`, custom axioms | 0 |
| `Fintype.ofFinite` occurrences | 0 |
| Dependency-reachability probes passed | 6 / 6 |
| Prisoner's Dilemma definition, authored nonblank lines including doc comments (RFC 7.3 budget 25) | 20 |

Every row above is re-checked by `scripts/phase2-audit.ps1`. The Prisoner's
Dilemma row is enforced as a bound rather than an equality, because RFC 7.3
states a budget.

RFC 7.3's usability tests are met for: Prisoner's Dilemma under 25 lines; its
unique pure equilibrium proved semantically (`prisonersDilemma_isNash_iff`);
Matching Pennies with the supplied uniform mixed equilibrium both checked
(`#guard`) and proved (`matchingPennies_uniform_isNash`); switching one form
from expected utility to an ordinal preference
(`prisonersDilemma_bothDefect_isNash_ordinal`); and reusing one
signature-bound profile across two play laws
(`update_eq_self_serves_both_laws`). The two-stage compilation and
player-relabeling tests need Phase 3 and Phase 4 machinery and are not
attempted here.

## Findings worth carrying forward

1. **Locality is a type-level invariant, not a lint.**
   `Subprofile.singletonEquiv : Subprofile sig {who} ≃ sig.Strategy who` says a
   unilateral deviation's input carries exactly the deviator's own strategy, so
   a recommendation-spying correlated-equilibrium deviation is inexpressible.
   `DeviationScheme.exists_agree_off_members` extends the guarantee to the
   deviated law's support.

2. **Bundled forms need reducible transformers.** `F.mixed.sig` does not reduce
   to `F.sig.mixed` at `instances` transparency, so six transformer definitions
   had to be made `@[reducible]` and one theorem needed a `show`. This is new
   evidence against D1's provisional bundling that the Phase 1 miniature could
   not have produced.

3. **Kernel `decide` cannot do rational arithmetic.** `Rat.add` and `Rat.blt`
   do not reduce, so exact rational checks are run by compiled evaluation
   (`#guard`, `#eval`) and proved by `norm_num` over an explicit enumeration.
   `native_decide` stays excluded because it adds a compiler-trust axiom.

4. **Core's Mathlib closure is bounded but not clean.** Mathlib's `PMF` pulls
   `MeasureTheory.Measure.Dirac` and ENNReal topology into Core's transitive
   closure. Narrowing the import to the `PMF` monad layer removed `stdSimplex`
   and `Polynomial`. RFC 9.1.5 is therefore enforced as an authored-import rule
   plus reachability probes, and that reading is recorded in the D2 amendment
   rather than assumed.

5. **The D4 ordered-field factoring was rejected on evidence.** The real and
   rational expectation paths share no lemma, so a scalar-polymorphic layer
   would have added a parameter without removing a theorem.

6. **Strong Nash is sensitive to preference totality.** `Preference.coalition`
   uses "some member weakly prefers the status quo", which for a *partial*
   preference is strictly stronger than Aumann's "the members do not all
   strictly gain" — an incomparable member satisfies neither. The unconditional
   implication is `Preference.not_forall_strict_of_coalition`; the equivalence
   is `isStrongNash_iff_not_all_gain`, which takes `Preference.Total` as a
   hypothesis. Expected utility is total, so the textbook concept is recovered
   there. Since supporting partial, non-EU preferences is D4's point, this is
   recorded as a deliberate choice rather than left implicit.

## Not done in Phase 2, by design

- Player reindexing, form homomorphisms, and the rest of D8's taxonomy
  (Phase 4).
- Any sequential, execution, or information semantics (Phase 3).
- Any existence theorem or the `stdSimplex` Analysis bridge (Phase 4); the
  Phase 1 candidate's simplex development remains experimental evidence and is
  not part of Core.
- A mixed-equilibrium solver, which D10 explicitly does not require.
