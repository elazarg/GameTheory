# Assessment of the automated repository review

**Reviewed artifact:** automated `Review.html`, generated 2026-08-10 against
repository checkpoint `90a47784`.

This note records which recommendations were verified, which changed project
control, and which are deliberately deferred. The HTML is evidence, not an
authority: Lean source, kernel dependencies, primary literature, and the
current pipeline remain authoritative.

## Accepted and acted on

1. **Padding overclaim.** The conjecture and `StochasticGame.Act` docstrings
   falsely said naive state-dependent-action padding preserves approximate
   equilibria in both directions. `PaddedDuplicateLotterySeparation.lean`
   refutes that statement under raw-action perfect monitoring. Both docstrings
   now state the honest state-independent scope and the two viable repair
   routes.
2. **Axiom audit completeness.** The repository audit checked unexpected
   axioms but only required one parsable report. It now counts `#print axioms`
   directives and requires exactly the same number of parsed reports.
3. **CI coverage.** Full CI now runs on `uniform-existence` pushes and on a
   daily schedule, as well as on `main` pushes and manual dispatch.
4. **Instant-punishment status.** `FRONTIER.md` and the Simon clause map were
   stale. `InstantPunishment.lean` already defines the history-dependent
   stage-zero trigger, proves its exact scalar characterization, and compiles
   it to a uniform payoff. The open problem is producing its two conditions,
   not expressing the strategy.
5. **Three-player claim sealing.** The unconditional `Fin 3` theorem now has a
   dedicated claim, exact scope, kernel anchor, attribution to the known 1999
   result, and a separate formalization-novelty statement.
6. **P0 priority.** `MATH-P0-8` is the primary positive lane. `MATH-P0-12` is a
   grounding/supporting lane with a consequence-based stop rule.

## Accepted diagnosis, with calibrated wording

- Q161's abstract maximal inequality and unrestricted live-chain deviation
  cap are formalized, as is the honest truncation fold. The relaxed compiler is
  nevertheless incomplete: `RankOneCrossing.lean` still assumes the
  quitting-plan decision process, its live-crossing implication, and its
  variation budget. The previous `M [reported]` completion label was too
  strong and has been removed.
- The conditioned diffuse compiler is a real positive result but is
  conditional on singleton tightness, small uniform mesh, and every deleted
  clock being complete. “The branch compiles” must retain those hypotheses.
- The negative search needs a certificate format before larger candidate
  sweeps can carry theorem-level weight. Four-player generative search is a
  useful secondary task; an uncertified table is not a counterexample.

## Deferred deliberately

- A repository-wide `autoImplicit false` conversion and a production/archive
  lake split are large engineering migrations with no immediate mathematical
  return. They should be separately scoped, not mixed into P0.
- The Abel/Cesàro bridge between the repository's horizon-uniform notion and
  the standard patient-discount clause is important general infrastructure,
  but it does not gate the finite-quitting P0 compiler.
- A full re-audit of Vieille, Mertens--Neyman, and definable stochastic games
  belongs to the general lane. No unread source is credited as a theorem.

## Next mathematical checkpoint

Construct the game-specific rank-one decision-discrepancy object required by
`RankOneCrossing.lean`, or prove that the proposed per-tolerance chain supplies
an equivalent deterministic reach bound. The checkpoint is one theorem that
feeds Case 1 and Case 2 into the same terminal `ε`-Nash producer. More local
counterexample-carrier infrastructure is not a substitute.
