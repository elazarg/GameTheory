# D41: finite-outcome vNM representation stays in the preference layer

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment IDs:** EXP-074

[D62](D62-general-pmf-restoration.md) governs the general PMF carrier and guarded
expected-utility domain. This decision governs the algebraic finite-outcome
converse and its separation from game forms and analytic existence theory.

## Decision

State von Neumann--Morgenstern mixture independence, mixture continuity, and
expected-utility representation directly on the canonical
`WeakPreference Agent Outcome` over ordinary PMFs, with the guarded
expected-utility relation specified by D62.

- the public predicates are family-wide, like every existing
  `Preference.*` law;
- the representing utility has shape `Outcome → Agent → ℝ`, matching the
  established expected-utility orientation;
- the finite-outcome converse stores no finiteness and imposes no agent
  finiteness;
- finite compound indifference is a theorem about the existing preference and
  `PMF.bind`, with finite support required only of the outer lottery;
- support decomposition, standard lotteries, and certainty equivalents remain
  private proof machinery;
- affine real utility and risk neutrality live in game-independent
  `GameTheory.Math`.

## Competing designs

1. Prove the finite converse through the public support, mixture, expectation,
   and conditioning API. **Selected.** Finite outcomes provide finite support
   locally; general lottery semantics do not store it.
2. Promote only representation-implies-axioms and defer the converse.
3. Expose raw extended-real weight arithmetic or a second lottery carrier in
   the representation proof.
4. Route the theorem through simplex topology or the Analysis fixed-point
   boundary.
5. Export a reusable compound-indifference or standard-lottery certificate
   hierarchy.

Design 2 was the fallback if finite compound substitution failed. Designs 3
and 4 violate the selected numerical and analytic boundaries for a theorem
whose mathematics is finite and algebraic.  Design 5 would freeze proof
scaffolding without an independent consumer.

## Semantic evidence

EXP-074 conditions a law on the complement of one supported outcome, proves
that the original law is exactly a binary mixture of that point mass and the
conditioned tail, proves strict support decrease, and lifts pointwise
indifference through arbitrary finite `bind`.  The proof uses only public
finite-law operations and real probabilities in the historical experiment.
D62 replaces that carrier while preserving the finite algebraic argument.
The canonical compound-indifference consequence permits a separate outer
index type and arbitrary PMF branch laws. The experimental consumer uses that
theorem instead of defining another independence axiom or repeating the
support induction. It introduces no decomposition certificate hierarchy.

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

Reject the full converse if its representation proof needs raw `ENNReal` or
`toReal` arithmetic, measurable or topological probability, `stdSimplex`,
`Fintype.ofFinite`, stored finiteness, a second preference/law abstraction, or
public decomposition machinery with no independent consumer. Ordinary PMF
lotteries are the canonical carrier under D62, superseding the original
experiment's ban on their direct use. Also reject an
axiom that cannot survive a nontrivial expected-utility order or a proof that
does not decrease support honestly.

The zero-weight draft is refuted by the reflexive-preference control and is
preserved in EXP-074. Strictly positive mixture weights support the finite
algebraic converse without a topology or fixed-point dependency.

## Consequences

`GameTheory.Core.VNM` owns the three family-wide predicates, direct existence,
and the finite-outcome characterization.  `Rank.Indifferent` owns symmetric
weak comparison at the probability-free layer. Generic mixture identities
belong to the canonical probability modules; representation-specific
decomposition stays private. Representation is exact agreement with guarded
expected-utility preference. Transitivity and mixture solvability obtain
integration from their comparison premises; global totality and mixture
independence additionally require integration of the relevant lottery domain.
Ordinal rankings remain separate from lottery preferences.

Validation details are recorded in EXP-074 and the exact
`S-FOUND-vnm` coverage ledger.
