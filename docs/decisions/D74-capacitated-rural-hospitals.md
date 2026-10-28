# D74: one responsive capacity semantics with a sorted slot reduction

- **Status:** adopted and promoted
- **Date:** 2026-10-28
- **Experiment ID:** [EXP-168](../ExperimentLog.md)

## Target and delivered scope

`CapacitatedMarket.ruralHospitals` proves the full finite rural hospitals
result under strict individual rankings and responsive acceptance. For two
stable assignments of the same market it proves separately:

1. exactly the same doctors are unmatched;
2. every hospital employs the same number of doctors; and
3. a hospital below quota has exactly the same doctor cohort in both assignments.

The third conclusion is equality of sets, not just their cardinalities. This
is the distinction established by Roth's
[*On the Allocation of Residents to Rural Hospitals* (1986)](
https://stanford.edu/~alroth/papers/1986_E_On_the_Allocation.pdf).

Zero quotas, unacceptable partners, unmatched doctors, unequal market sizes
and nonempty undersubscribed hospitals are included. Neither positive quotas
nor complete acceptability is assumed. Finite-carrier and ranking-law
assumptions are parameters of the operations and theorems, not market data or
additional conjuncts of stability. Ties, couples, contracts, distributional
constraints, endogenous quotas and arbitrary team preferences are outside
this package.

## Shared semantic owner

`Matching.Basic` owns individual `MatchingMarket` rankings, optional
assignments, cohort fibers, injectivity and individual rationality.
`Matching.Capacitated` owns `CapacitatedMarket`: the existing rankings plus
one intrinsic quota function `Hospital → ℕ`. No finite instances, ordering
certificates, utility representation or second assignment map are stored.

Every cohort is the actual fiber of the doctor-to-optional-hospital
assignment. Feasibility bounds its `Set.encard` by the finite quota. This
simultaneously bounds its size and certifies finiteness, even for infinite
doctor carriers. An unguarded `ncard` check is rejected by a proved infinite
constant-fiber counterexample: natural cardinality passes the quota-one
bound while extended cardinality rejects it.

The single responsive blocking rule says that the doctor strictly prefers
the hospital and either the hospital has a vacancy and finds that doctor
acceptable, or it prefers the doctor to an incumbent. Stability combines
feasibility, existing individual rationality and absence of such pairs.
Responsiveness is encoded by these local acceptance operations. There is no
free ranking over teams with an unenforced responsiveness annotation.

Ordinary `MatchingMarket.IsStable` and `IsBlockingPair` are transparent
unit-quota specializations of this owner. Injectivity is recovered by the
unit-capacity feasibility theorem. The pairwise characterization agrees with
the former blocking formula on valid one-to-one assignments without extra
ranking laws; stability preservation needs no separate validity premise,
because feasibility supplies it. Existing algorithms and fixtures consume
these mathematical characterizations rather than compatibility aliases or a
parallel stability definition.

## Competing designs and measured corrections

The experiment compared native quota assignments, ordered hospital-slot
cloning and a broader hospital-choice framework. Native assignments are the
semantic owner; slots are a proved backend. General choice functions were
scoped out, not disproved. A later extension must specify and validate its
own substitutability, consistency and size laws.

The initial native prototype required outside-option acceptability for both
vacancy and replacement. Both guard placements agree under individual
rationality and hospital transitivity, at every quota. But a raw cyclic-ranking
counterexample refutes assumption-free equivalence. Requiring acceptability
only for vacancy preserves the existing raw-ranking unit-capacity behavior,
so that is the promoted shared rule. EXP-168 retains both prototypes and the
counterexample instead of rewriting away the unsuccessful stronger claim.

An arbitrary reverse slot lift is also refuted. Assigning one doctor to the
later of two copies of the same hospital creates an earlier-slot blocking
pair, although both lifts collapse to the identical stable native assignment.
The reverse reduction therefore sorts each hospital's doctors into an initial
segment. This sorting requirement is enforced by the construction and proved
occupancy properties, not by a comment or an assumed lifting witness.

## Established proof dependency path

`Matching.Slots` derives the hospital-slot market from the existing rankings.
Different hospitals retain their native order; lower indices refine positions
of the same hospital. Every slot inherits the hospital's ranking of doctors.
The slot refinement preserves strict linearity. A valid slot assignment has
an exact bijection between each collapsed cohort and its occupied slots.
Stable slot assignments collapse to native stability, without requiring
finite doctor or hospital carriers.

`Matching.SortedLift` uses Mathlib finite sorting and list indices to place
each hospital's doctors best first into its initial occupied segment. It
proves injectivity, exact collapse and reverse stability. Earlier occupied
slots exclude artificial within-hospital blockers; genuine hospital moves
would block the native assignment. The reverse lift requires finite doctors
only, with no finite-hospital premise. The final theorem uses this actual
construction, never an assumed stable lift.

`Matching.RuralHospitals` then:

1. applies the existing one-to-one unmatched-agent theorem to the stable lifts;
2. transfers unmatched doctors and pointwise occupied-slot equality, obtaining
   equal headcounts at every hospital;
3. projects existing one-to-one DA and proposer optimality to a stable,
   doctor-optimal native assignment; and
4. compares any undersubscribed hospital with that optimal assignment. A
   doctor in the optimal cohort but absent from the other cohort would prefer
   that hospital and block its vacancy. Cohort inclusion and equal finite
   headcounts give set equality. Comparing both stable assignments to the
   same optimal assignment proves the exact-cohort conclusion.

There is one DA algorithm and one responsive stability semantics. Slot
priorities are auxiliary to the reduction; the public native preference
comparisons concern physical hospitals and the outside option.

## Validation and admission

The initial prototypes and refutations remain under
`GameTheory/Experimental/Exp168/`. Stable modules import none of them.
`Tests.RuralHospitals` independently constructs a four-doctor, three-hospital
market with quotas `1,1,2`, two distinct stable outcomes, an unmatched doctor,
unacceptable pairs and a nonempty underfilled hospital. Its public consumer
uses all three general conclusions. Further controls prove that full hospitals
can change their cohorts, that equal headcounts alone need not mean equal
cohorts, that zero quotas work with an empty slot carrier, and that infinite
fibers fail finite quotas.

The focused strict build of the complete new theorem, native controls, all
migrated one-to-one fixtures and experimental evidence passes 1,079 jobs.
Independent semantic reviews accept the sorted lift, shared semantic owner,
unit-capacity preservation and exact-cohort argument. The full
`python scripts/audit.py` run passes the public build (3,872 jobs), complete
validation (4,691 jobs), public lint, source boundaries and transitive
standard-axiom checks, with no authored warnings or info diagnostics. The
native theorem-leaf declaration probe reaches the full theorem and sorted
reverse lift while rejecting Nash, Protocol, project expectation and PMF.
EXP-168 records the commands and preserves the earlier failed candidates.

The rejected conditions remain: default-zero counts admitting infinite
cohorts, stored finite capabilities, arbitrary team preferences without laws,
arbitrary reverse slot lifts, duplicate one-to-one semantics, or advertising
headcount equality as the full theorem. All passed admission conditions are
backed by the artifacts and commands recorded in EXP-168.
