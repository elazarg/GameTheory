# Every proved theorem constrains the hypothetical counterexample

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `PENDING` |
| Verdict | `OPEN` |
| Objective priority | `P1` |
| Last audited | 2026-08-04, `67ad767` |
| Central live claim | A hypothetical counterexample to the finite-quitting conjecture must satisfy *simultaneously* every constraint in the ledger below; accumulating constraints terminates either in a witness satisfying all of them, refuting the conjecture, or in a proof that the constraint set is empty, establishing it by exhaustion. |
| Next discriminant | Is the set of weights admitting an admissible absorbing cycle **semialgebraic** — equivalently, is there a bound `L(n)` such that a weight admitting one admits one of length at most `L(n)`? That single question decides whether the exhaustion is a computation at all. |
| Production destination | none yet |
| Supersedes / superseded by | none |

## What the method is

Do not search for a counterexample and do not search for a proof. Assume a
counterexample exists, and treat every theorem the program has proved as a
*constraint* on it. Each new theorem either shrinks the admissible region or is
revealed to be inert. Two terminations are possible:

- a weight satisfying every accumulated constraint is exhibited and checked —
  the conjecture is refuted; or
- the constraint set is shown empty — the conjecture follows, by exhaustion over
  the cases the constraints define.

The method's value is that it converts scattered partial results into a single
monotone object. Its risk, made concrete below, is that a constraint can be
perfectly valid and still cut nothing.

## Constraint ledger

| ID | Constraint on the counterexample | Seals | Status |
| --- | --- | --- | --- |
| K1 | `n ≥ 4` | `M [reported]` | pinned to Solan, *Three-player absorbing games*, Math. Oper. Res. **24**(3), 669–698 (1999) — recorded at [`ThreePlayerAbsorbingGamesHaveUniformEquilibria`](../UniformEquilibriumLiterature/ThreePlayerAbsorbingGamesHaveUniformEquilibria.md), itself `PRIMARY_FULLTEXT` on Solan's doctoral dissertation, MOR-typeset PDF unread |
| K2 | Some diagonal entry is strictly positive — indeed strictly exceeds the accuracy | `M+L` | machine-checked |
| K3 | No admissible absorbing cycle of any finite length | `M+L` | machine-checked as an *implication*: possessing one supplies a uniform-equilibrium payoff |
| K4 | **The algebraic screen.** For every `i` with `r_i({i}) ≥ 0` there is some `j ≠ i` with `r_j({i}) < r_j({i,j})` and `r_j({i}) ≤ r_j({j})` | `M [verified]` | verified by hand; the only constraint immediately runnable as a computation, and **of very low discriminating power** — see below |
| K5 | Every discounted limit degenerates, or isolates a coordinate of negative solo weight | `M [reported]` | reported; the same dichotomy carries seal `M` in [`../AbsorbingCycleCarrier/VanishingAbsorptionIsTheOnlyRemainingCase.md`](../AbsorbingCycleCarrier/VanishingAbsorptionIsTheOnlyRemainingCase.md) |
| K6 | Defect-vanishing families must fail | `I` | **open**, and the only constraint that is not about finitely much data |

Seal markers: `[reported]` means supplied externally and not audited here;
`[verified]` means checked by hand inside this repository.

`K1` is now pinned: `n ≥ 4` is exactly the open range left by Solan's
three-player absorbing-games theorem, which settles `n ≤ 3` and is what
`quittingGame`'s own external-status note (`QuittingConjecture.lean`) already
cites for the same fact. The literature axis is
[`../UniformEquilibriumLiterature/`](../UniformEquilibriumLiterature/README.md);
the recorded result carries its own source confidence
(`PRIMARY_FULLTEXT` on Solan's doctoral dissertation, MOR-typeset PDF
unread), which `K1` now inherits — pinning
narrows the exposure to that one upstream record rather than closing it.

`K2` and `K3` are the two constraints already in production. `K3` is a
constraint by contraposition: `exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle`
in `GameTheory/Concepts/Stochastic/QuittingZeroSoloDisjunct.lean` shows that a
weight possessing an admissible absorbing cyclic continuation block has a
uniform-equilibrium payoff, so a counterexample has none, at any finite length.

## The algebraic screen is necessary and nearly inert

`K4` is runnable — it is a finite conjunction of strict and weak inequalities in
the table entries, so a sweep over a grid of four-coordinate tables would
evaluate it directly. **That is not a reason to run it**, and the file states
the point plainly: the screen is a *necessary condition of very low
discriminating power*, not a search filter. A sweep would return a large region
almost none of whose members are counterexamples.

The witness is already in this repository. Take the
Flesch--Thuijsman--Vrieze three-player table, as carried by
`GameTheory/Concepts/Stochastic/FTVCyclicMinimality.lean`:

    r({0}) = (1, 3, 0)    r({1}) = (0, 1, 3)    r({2}) = (3, 0, 1)
    r({0,1}) = (1, 0, 1)  r({0,2}) = (0, 1, 1)  r({1,2}) = (1, 1, 0)

Every diagonal entry is `1 > 0`, so every coordinate must be blocked. Every
coordinate is:

- `2` blocks `0`: `r_2({0}) = 0 < r_2({0,2}) = 1` and `0 ≤ r_2({2}) = 1`;
- `0` blocks `1`: `r_0({1}) = 0 < r_0({0,1}) = 1` and `0 ≤ r_0({0}) = 1`;
- `1` blocks `2`: `r_1({2}) = 0 < r_1({1,2}) = 1` and `0 ≤ r_1({1}) = 1`.

So the screen's conjunction holds on this table. But the table has a
**machine-checked admissible absorbing cycle of length three** —
`hasAdmissibleAbsorbingQuittingCycle_ftvReward` and
`isUniformEquilibriumPayoff_namedTarget` in
`GameTheory/Concepts/Stochastic/FTVCyclicAdmissibleCycle.lean` — so it is
emphatically not a counterexample. Two consequences, both `[verified]`: the
arithmetic above was re-checked by hand against the Lean table, and the cycle is
machine-checked.

1. **The screen is satisfiable at three coordinates.** It yields no exhaustion
   proof there, so it cannot be expected to yield one at four.
2. **`K4` does not imply `K3`.** The screen was derived only from the
   length-one solo case; it rules out exactly the solo-solvable weights and
   passes everything else, including the canonical hard table. Any argument
   that treats screen-passing as evidence of cycle-freeness is wrong, and the
   FTV table is its counterexample.

The general lesson, and the method's characteristic failure mode: a valid
necessary condition adds nothing unless it *cuts*. The ledger should record, for
each constraint, not only that it holds but what it excludes.

## Why the finitisation question is the discriminant

`K1`--`K5` are all statements about finitely much data — table entries, a
finite sign pattern, a finite cycle length once a length bound is available.
`K6` is not: "defect-vanishing families must fail" quantifies over families of
unbounded period, and by
[`../AbsorbingCycleCarrier/FiniteCyclesAreRefutedTheCarrierIsAMassPath.md`](../AbsorbingCycleCarrier/FiniteCyclesAreRefutedTheCarrierIsAMassPath.md)
the minimum period provably diverges as the defect tends to zero. So `K6`
cannot be finitised by bounding the period of the family.

`K3` is the one that decides the method's character. As stated it quantifies
over all finite lengths, so it is not obviously a semialgebraic condition on the
table. It becomes one if there is a bound `L(n)` such that a weight admitting an
admissible absorbing cycle admits one of length at most `L(n)`: the condition
"admits an admissible absorbing cycle" would then be an existential over a
bounded-dimensional real parameter space, hence semialgebraic, hence in
principle decidable, and the exhaustion would be a computation.

**A caution that has already caused confusion in this corpus.** This is *not*
settled by the known weight that has no absorbing complementary cycle of any
finite length. That weight says: some weights have none. The finitisation
question asks: among the weights that have one, is the length bounded? Those are
different statements and neither implies the other.

**A second caution.** [`../AbsorbingCycleCarrier/README.md`](../AbsorbingCycleCarrier/README.md)
states, correctly, that no bound on the length is required and that
"of length at most `L(n)`" should not be asked for. That is about the
*soundness of the reduction*: the formalized conditional quantifies over the
period with no bound, so a bound would be dead weight there. The bound is asked
for here for an entirely different purpose — **finitisation of a constraint**,
not soundness of an implication. The two asks are compatible; the file records
the distinction so the apparent contradiction is not read as one.

## Falsifiers and wrong turns

- **The method is refuted as a program** if the constraint set is shown
  non-finitisable and no witness is found — that is, if `K3` is not
  semialgebraic and `K6` stays open. The inverted search would then be a
  bookkeeping device, not a decision procedure, and should be demoted.
- **`K4` is refuted as a filter** — this has already happened, above. Preserved
  as a regression: any future claim that the screen narrows the search must
  explain why the FTV table passes it.
- **`K1` falls** if the pinned literature result (Solan, *Three-Player
  Absorbing Games*, MOR 24(3):669–698 (1999), recorded at
  [`ThreePlayerAbsorbingGamesHaveUniformEquilibria`](../UniformEquilibriumLiterature/ThreePlayerAbsorbingGamesHaveUniformEquilibria.md))
  is misquoted or narrower in scope than used, or if the MOR-typeset text
  (still unread; the record is `PRIMARY_FULLTEXT` on Solan's doctoral
  dissertation, not the journal PDF) turns out to disagree with the
  dissertation. It is the constraint doing the most work in cutting the
  dimension of the search — nothing below four coordinates need be examined
  *only* because of it.
- **`K5` falls** with the dichotomy it restates. It is `[reported]` here and
  `M` in the companion file; if the companion's discounted-family argument
  fails, both go.
- **`K3` is not weakened to "no cycle of small length".** A counterexample must
  fail at *every* finite length; a computation that checks lengths up to some
  cutoff and finds nothing has proved nothing about the constraint.
- **Do not add a constraint without recording what it excludes.** The screen is
  the standing demonstration that a valid, machine-runnable, hand-verified
  necessary condition can have essentially no discriminating power. A ledger of
  inert constraints is indistinguishable from progress and is not progress.
- **Do not treat the constraint set as a specification of a witness.** Satisfying
  every constraint is necessary, not sufficient; a candidate weight passing all
  six still has to be checked directly against the conjecture.

## Production map

```text
Solan 1999 (pinned)                    ->  K1
QuittingZeroSoloDisjunct.lean          ->  K2, K3   (landed, by contraposition)
hand verification                      ->  K4       (no production surface)
discounted-limit dichotomy (reported)  ->  K5       (no production analogue)
defect-vanishing families              ->  K6       (open; not finitary)
                                            |
                                            v
                     [MISSING] a decision procedure, or an emptiness proof
```

Landed declarations backing the ledger:
`exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle` and
`IsQuittingZeroSolo` in
`GameTheory/Concepts/Stochastic/QuittingZeroSoloDisjunct.lean`;
`hasAdmissibleAbsorbingQuittingCycle_ftvReward` and
`isUniformEquilibriumPayoff_namedTarget` in
`GameTheory/Concepts/Stochastic/FTVCyclicAdmissibleCycle.lean` (the screen's
counterexample); the open premise `quitting_zeroSolo_or_admissibleCycle` in
`GameTheory/Concepts/Stochastic/QuittingConjecture.lean` (what emptiness of the
constraint set would discharge).

Missing arrows, in order of value: (1) the finitisation question for `K3`;
(2) MOR-typeset-text verification of the `K1` attribution (Solan 1999 is now
`PRIMARY_FULLTEXT` on Solan's own doctoral dissertation, see
[`ThreePlayerAbsorbingGamesHaveUniformEquilibria`](../UniformEquilibriumLiterature/ThreePlayerAbsorbingGamesHaveUniformEquilibria.md),
but the MOR journal PDF itself is still unread); (3) for each constraint, an
explicit statement of what it excludes, so inertness is visible at a glance.

## Exit conditions

- `ACTIVE` when the finitisation question is assigned, or when a seventh
  constraint with demonstrated cutting power lands.
- `MINED` if a witness satisfying every constraint is exhibited and checked, or
  if the constraint set is proved empty.
- `PARKED` if `K3` is shown non-semialgebraic and no alternative finitisation is
  available; the ledger would remain as a citable summary of what a
  counterexample must look like.
- Constraint `K4` is already recorded as inert rather than `WRONG`: it is a true
  necessary condition, it just does not cut.
