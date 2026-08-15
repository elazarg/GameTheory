# D41: finite-law vNM representation stays in the preference waist

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment IDs:** EXP-074

## Decision

State von Neumann--Morgenstern mixture independence, mixture continuity, and
expected-utility representation directly on the canonical
`WeakPreference Agent Outcome` over `FinDist Outcome`.

- the public predicates are family-wide, like every existing
  `Preference.*` law;
- the representing utility has shape `Outcome → Agent → ℝ`, matching the
  established expected-utility orientation;
- the finite-outcome converse stores no finiteness and imposes no agent
  finiteness;
- compound substitution, standard lotteries, and certainty equivalents are
  private proof machinery;
- affine real utility and risk neutrality live in game-independent
  `GameTheory.Math`.

## Competing designs

1. Prove the finite converse through the public `FinDist` support and
   conditioning API. **Selected.**
2. Promote only representation-implies-axioms and defer the converse.
3. Expose PMF/ENNReal or a second public lottery carrier to port the baseline proof.
4. Route the theorem through simplex topology or the Analysis fixed-point
   boundary.
5. Export a reusable compound-indifference or standard-lottery certificate
   hierarchy.

Design 2 was the fallback if finite compound substitution failed.  Designs 3
and 4 violate the selected probability and analytic boundaries for a theorem
whose mathematics is finite and algebraic.  Design 5 would freeze proof
scaffolding without an independent consumer.

## Representative slice and measurements

EXP-074 conditions a law on the complement of one supported outcome, proves
that the original law is exactly a binary mixture of that point mass and the
conditioned tail, proves strict support decrease, and lifts pointwise
indifference through arbitrary finite `bind`.  The proof uses only public
`FinDist` operations and real probabilities.

The first draft exposed a useful falsification: permitting mixture weight zero
in independence makes both mixtures equal the common branch and therefore
forces every comparison for any reflexive preference.  The corrected axiom
requires `0 < t`, matching the representative theorem.  A supported head supplies a
positive weight, while a nonempty complement supplies weight strictly below
one, so the induction remains valid.

The stable proof constructs private best/worst standard lotteries, certainty
equivalents, and the expected-utility index.  It treats the empty outcome type
vacuously, so the public theorem needs only `[Finite Outcome]`.  The positive
fixture has three distinct utility levels and a genuine interior certainty
equivalent.  The negative fixture orders laws lexicographically by two
coordinate masses: it is total, transitive, and mixture-independent but not
mixture-continuous and has no expected-utility representation.

## Kill condition and result

Reject the full converse if it needs authored use of `PMF`, `toPMF`, `ENNReal`,
`toReal`, measurable or topological probability, `stdSimplex`,
`Fintype.ofFinite`, stored finiteness, a second preference/law abstraction, or
public decomposition machinery with no independent consumer.  Also reject an
axiom that cannot survive a nontrivial expected-utility order or a proof that
does not decrease support honestly.

No corrected kill condition fired.  The zero-weight draft was rejected and
preserved in the experiment record; the strict-positive formulation and full
converse compile over the canonical waist.

## Consequences

`GameTheory.Core.VNM` owns the three family-wide predicates, direct existence,
and the finite-outcome characterization.  `Rank.Indifferent` owns symmetric
weak comparison at the probability-free layer.  Generic mixture identities
are promoted to `FinDist`; representation-specific decomposition stays
private.  This completes the pinned 66-declaration VNM Basic file without
merging ordinal rankings back into lottery preferences.

Validation details are recorded in EXP-074 and the exact
`S-FOUND-vnm` coverage ledger.
