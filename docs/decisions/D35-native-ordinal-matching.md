# D35: stable matching uses native ordinal preferences

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment ID:** EXP-068

## Decision / question

Whether one-to-one matching should use the probability-free `Ranking`
foundation, preserve the comparison design's integer-score market with separate reservation
values, or be represented by an artificial strategic game whose Nash
equilibria encode assignments.

## Competing designs

1. Store two rankings over optional partners, represent an assignment directly,
   and require finite linear-ranking certificates only for deferred acceptance.
2. Store integer scores for partners and separate integer reservation values,
   using injectivity as the strict-preference hypothesis.
3. Invent strategies and payoffs so that stable assignments can be described
   through the general equilibrium predicate.

Design 1 is adopted.  Remaining unmatched is an alternative, not a second
numeric scale.  The semantic market stores only the two ordinal relations; it
does not store finiteness, decidability, linearity, probability, or strategic
structure.  A matching remains a left-to-optional-right function with an
explicit one-to-one certificate, preserving the lightweight and useful the baseline
representation.

## Representative hostile slice

The general slice proves termination of the inflationary rejection process,
preservation of the rejection invariant, stable matching existence on arbitrary
finite carriers, and perfectness in balanced completely acceptable markets.

The concrete three-by-three market has two left agents initially proposing to
the same right agent.  Its machine-checked first round rejects left zero; in the
exact reachable successor state, right one replaces left two by left zero.  A
separate assignment is refuted by the explicit blocking pair `(left one, right
zero)`.  The final contested assignment is both stable and perfect, and the
general perfect-stable theorem specializes to the fixture.

## Measurements

| Measure | EXP-068 result |
|---|---|
| semantic owner | native `GameTheory.Cooperative` branch over `Core.Rank` |
| stored capabilities | none |
| preference representation | two rankings over `Option` partners; no scores or reservation values |
| general result | finite ordinal deferred acceptance is stable; balanced complete acceptability implies perfectness |
| hostile dynamics | exact first-round rejection plus reachable holder replacement |
| negative control | concrete valid assignment with a named blocking pair |
| bounded accounting | all 74 Matching/GaleShapley/Perfect declarations classified; 11 optimality/symmetry rows deferred |
| boundary probes | 5 Cooperative inputs reached; Nash, finite probability, Protocol, and measurable theory rejected |
| trust | sampled flagships use only `propext`, `Classical.choice`, and `Quot.sound` |
| release gate | warning-clean 3,509-job build; Phase 1--3 and exact coverage `VERIFIED=1` |

## Kill condition

Reject native ordinal ownership if deferred acceptance needs stored finiteness,
a second cardinal preference encoding, dummy strategic players, probability,
Protocol, or Analysis; if its public proof exposes raw function updates or
equality transports; or if only a concrete score-valued theorem survives.

No semantic kill condition fired.  A general finite-set greatest-element lemma
was added at the game-independent ranking layer, allowing the algorithm to
select directly from total transitive relations.  The fixture exercises
nontrivial rejection dynamics and the general theorems remain carrier-generic.

## Consequences for the public API

`GameTheory.Cooperative` is an opt-in root and remains absent from the
lightweight `GameTheory` umbrella.  `MatchingMarket`, stability, deferred
acceptance, and perfectness are native market-design concepts.  Proposer
optimality, receiver pessimality, matching symmetry, rural hospitals, and
strategyproofness are subsequent P-MATCH breadth gates; none may introduce a
parallel preference or matching representation.
