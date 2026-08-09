# D40: distinguish mixed and pure rationalizability

- **Status:** accepted
- **Date:** 2026-08-09
- **Experiment IDs:** EXP-073

## Decision

Use Bernheim--Pearce mixed-strategy elimination as the unqualified stable
notion:

- `GameTheory.survivors` and `GameTheory.IsRationalizable` eliminate a pure
  strategy when a `FinDist` of surviving own strategies strictly improves
  against every surviving opponents' profile;
- `GameTheory.pureSurvivors` and `GameTheory.IsPureRationalizable` name the
  weaker pure-dominator iteration;
- D10's executable frontend remains a pure-elimination checker, and its public
  procedures and correctness theorems say `pure` explicitly.

There are no source-compatibility aliases.  The earlier unqualified pure names
were provisional greenfield surface, not a semantics to preserve.

## Competing designs

1. Keep pure elimination as the only selected `IsRationalizable` notion.
2. Promote standard mixed elimination and rename the pure semantics and
   executable checker. **Selected.**
3. Add an exact rational mixed-elimination algorithm in the same change.
4. Defer mixed rationalizability and document the mismatch.

Design 1 misnames a strictly weaker solution concept and loses a mature v1
workflow.  Design 3 would confuse proof semantics (`FinDist` over real expected
utility) with a new rational-certificate algorithm whose representation and
completeness obligations were not requested.  Design 4 leaves an avoidable
semantic trap on the public surface.

## Representative slice and measurements

The Core definition reuses `DeviationScheme.unilateralRandomized`,
`GameForm.outcomeLaw`, `FinDist`, `Preference.strict`, and `Profile.update`.
It stores no finiteness and imports neither Analysis nor a domain root.  Nash
survival factors through the existing theorem that expected-utility CCE blocks
randomized unilateral replacements.

The hostile finite game has three row actions.  The third pays `3/4` against
every column; neither of the first two pure actions dominates it, while their
half/half mixture pays `1` against every column.  Consequently it survives pure
round one, the D10 checker certifies that fact, and standard mixed round one
removes it.  The focused Core/Finite/test build completed 1,754 jobs
warning-free.

## Kill condition and result

Reject the split if standard rationalizability needs `PMF`, measurable or
infinite-support probability, Analysis, stored `Fintype`, raw
`Function.update`, a second equilibrium/profile API, or cannot be separated
from pure elimination on a small game.  Also reject it if renaming the D10
checker breaks its proof/execution boundary.

No kill condition fired.  The mixed semantics are proof-only Core; the renamed
pure algorithm remains rational, finite, executable, and exactly connected to
`IsPureRationalizable`'s survivor iteration.  A future mixed checker is a
separate algorithm/certificate gate, not an implication of this decision.

The full reachability audit reached all six intended mixed/pure Core inputs and
rejected the finite frontend, Protocol, and analytic existence.  Representative
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; exact
coverage and the 3,531-job warning-clean default build are green.
