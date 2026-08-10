# D40: distinguish correlated, independent, and pure rationalizability

- **Status:** accepted, corrected 2026-08-10
- **Date:** 2026-08-09
- **Experiment IDs:** EXP-073, EXP-076

## Decision

Name the existing joint-opponent mixed-dominator iteration for what it
represents:

- `GameTheory.correlatedSurvivors` and
  `GameTheory.IsCorrelatedRationalizable` eliminate a pure strategy when a
  `FinDist` of surviving own strategies strictly improves against every
  surviving *joint* opponents' profile;
- `GameTheory.pureSurvivors` and `GameTheory.IsPureRationalizable` name the
  distinct pure-dominator iteration; and
- independent rationalizability has no public definition until a product of
  opponents' beliefs and its finite-game characterization are implemented and
  tested.

Do not provide an unqualified `IsRationalizable` alias.  In games with three
or more players it would hide the material distinction between arbitrary
beliefs over joint opponents' actions and products of per-opponent beliefs.
There are no source-compatibility aliases.

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

Primary references:

- B. D. Bernheim, “Rationalizable Strategic Behavior,” *Econometrica* 52
  (1984), 1007–1028, DOI: 10.2307/1911196.
- A. Brandenburger and E. Dekel, “Rationalizability and Correlated
  Equilibria,” *Econometrica* 55 (1987), 1391–1402,
  DOI: 10.2307/1913562.

## Representative slice and measurements

The Core operator reuses `DeviationScheme.unilateralRandomized`,
`GameForm.outcomeLaw`, `FinDist`, `Preference.strict`, and `Profile.update`.
It stores no finiteness and imports neither Analysis nor a domain root.  The
hostile three-action game still separates mixed and pure dominators in its
first round.

EXP-076 compared the implemented quantifiers with the primary definitions.
The implementation ranges over a single joint opponents' profile, so its
dual best-response belief may correlate different opponents' actions.  The
public API and all direct consumers were renamed without aliases.  A focused
Core/Finite/test/example build completed 1,757 jobs warning-free.

## Kill condition and result

Reject the corrected name if the implementation enforces a product of
per-opponent beliefs, or if the correlated and independent notions coincide in
all finite multiplayer games.  Neither is true: the implementation has no
product restriction, and the primary literature gives a three-player strict
separation.

The correction therefore stands.  A future independent-rationalizability
package must choose an explicit finite product-law representation, prove its
own elimination/best-response correspondence, and include a three-player
example separating it from `IsCorrelatedRationalizable`.
