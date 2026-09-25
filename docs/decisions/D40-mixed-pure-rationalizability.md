# D40: distinguish correlated, independent, and pure rationalizability

- **Status:** accepted; general PMF integration boundary governed by D62
- **Date:** 2026-08-09
- **Experiment IDs:** EXP-073, EXP-076, EXP-080, EXP-132

## Decision

Name the existing joint-opponent mixed-dominator iteration for what it
represents:

- `GameTheory.correlatedSurvivors` and
  `GameTheory.IsCorrelatedRationalizable` eliminate a pure strategy when a
  PMF of surviving own strategies strictly improves against every
  surviving *joint* opponents' profile;
- `GameTheory.pureSurvivors` names the distinct pure-dominator iteration and
  `GameTheory.SurvivesAllPureEliminationRounds` names its all-round survivor
  property without overloading “rationalizability”; and
- `GameTheory.independentSurvivors` and
  `GameTheory.IsIndependentRationalizable` iterate best response to a profile
  of per-opponent PMF marginals, interpreted by the canonical mixed
  extension as an independent product law.

Do not provide an unqualified `IsRationalizable` alias.  In games with three
or more players it would hide the material distinction between arbitrary
beliefs over joint opponents' actions and products of per-opponent beliefs.
There are no source-compatibility aliases.

[D62](D62-general-pmf-restoration.md) governs the general PMF carrier and
integrability of the actual compared laws. The survivor predicates above mean
survival of every finite iteration. They do not assert a transfinite or greatest
fixed-point characterization on infinite strategy spaces. Interchanging a
product belief with a mixed dominator additionally requires integration of
their joint payoff law; separate conditional expectations do not supply it.
EXP-132 proves that this premise is necessary: an action survives every
independent round but is removed by correlated elimination in round one,
despite integration of every conditional row and column. Finite strategy
spaces recover the inclusion from integration of pure play, without requiring
finite outcome spaces.

## Competing designs

1. Keep calling joint-profile mixed elimination Bernheim--Pearce or standard
   rationalizability.
2. Rename it correlated rationalizability and leave independent
   rationalizability absent until its product-belief semantics exists.
   **Selected.**
3. Implement independent rationalizability immediately in the corrective
   change.
4. Collapse the API back to pure elimination.

Design 1 is false for three or more players.  Brandenburger and Dekel separate
correlated rationalizability, which allows correlated beliefs across
opponents, from the independent notion originally defined by Bernheim and
Pearce.  Design 3 would freeze a new product-distribution API without its own
hostile slice.  Design 4 would discard a valid and useful correlated-belief
operator.

The original staged choice of Design 2 remains the reason the terminology fix
landed first. EXP-080 later discharged Design 3's missing gate without adding a
new product-distribution type: an existing mixed profile supplies the marginal
laws and `GameForm.mixed` supplies their product.

Primary references:

- B. D. Bernheim, “Rationalizable Strategic Behavior,” *Econometrica* 52
  (1984), 1007–1028, DOI: 10.2307/1911196.
- A. Brandenburger and E. Dekel, “Rationalizability and Correlated
  Equilibria,” *Econometrica* 55 (1987), 1391–1402,
  DOI: 10.2307/1913562.

## Representative slice and measurements

The Core operator reuses `DeviationScheme.unilateralRandomized`,
`GameForm.outcomeLaw`, PMF, `Preference.strict`, and `Profile.update`.
It stores no finiteness and imports neither Analysis nor a domain root.  The
hostile three-action game still separates mixed and pure dominators in its
first round.

EXP-076 identifies the quantifier distinction: a belief on a joint opponents
profile may correlate different opponents' actions. The public names must
express that correlated interpretation rather than imply independent
opponent mixing.

## Kill condition and result

Reject the corrected name if the implementation enforces a product of
per-opponent beliefs, or if the correlated and independent notions coincide in
all finite multiplayer games.  Neither is true: the implementation has no
product restriction, and the primary literature gives a three-player strict
separation.

The correction therefore stands, and EXP-080 completes the named independent
surface. `Tests.Rationalizability` proves that one candidate survives every
correlated mixed-dominator round but is rejected in the first independent
best-response round. The inclusion theorem proves independent implies
correlated rationalizability under the joint-law integration premise above.
The symbolic converse counterexample quantifies
over every pair of opponent marginals; it is not a sampled or
definition-for-definition comparison.
