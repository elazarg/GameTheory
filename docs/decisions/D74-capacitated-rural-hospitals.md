# D74: native capacitated matching with a separate slot reduction

- **Status:** provisional; no stable capacitated API is frozen
- **Date:** 2026-10-28
- **Experiment ID:** [EXP-168](../ExperimentLog.md)

## Target and scope

The target is the full finite rural hospitals theorem under strict individual
rankings and responsive hospital behavior. For two stable assignments of the
same market, prove separately that:

1. exactly the same doctors are unmatched;
2. each hospital employs the same number of doctors; and
3. a hospital below quota has exactly the same doctor cohort in both assignments.

The third statement is equality of sets, not just their cardinalities. This
is the distinction established by Roth's
[*On the Allocation of Residents to Rural Hospitals* (1986)](
https://stanford.edu/~alroth/papers/1986_E_On_the_Allocation.pdf).

The first slice excludes ties, couples, contracts, distributional constraints,
endogenous capacities and arbitrary preferences over teams. Zero quotas,
unacceptable partners, unmatched doctors, unequal market sizes and nonempty
undersubscribed hospitals are included. Finite-carrier and ranking-law
assumptions belong on operations and theorems, not market data.

## Candidate semantic owner

The experimental direct model stores the existing two individual preference
families as a `MatchingMarket Doctor Hospital` and adds only the quota function
`Hospital → ℕ`. An assignment remains the existing doctor-to-optional-hospital
function. Each hospital's cohort is its fiber; no second hospital assignment
map is stored or maintained.

Capacity feasibility compares a fiber's `Set.encard` with the finite quota.
This both bounds its size and certifies finiteness. An unconstrained `ncard`
bound is rejected: infinite sets default to cardinality zero there and could
silently pass every quota. Explicit finite enumeration may enter later at the
execution or finite-proof layer.

Responsive willingness is determined by the individual ranking and quota.
The proposed shared rule says a pair blocks when the doctor strictly prefers
the hospital and either the hospital has a vacancy and finds the doctor
acceptable, or it prefers that doctor to an incumbent. Stability combines
assignment feasibility, the existing individual rationality predicate, and
absence of such pairs. All three are conditions on the assignment. Linearity
is a separate theorem hypothesis.

The first direct prototype instead required acceptability in both branches.
`BlockingComparison` proves the two rules equivalent under individual
rationality and hospital transitivity, at every quota. It also proves a genuine
difference on raw cyclic rankings. The vacancy-or-replacement rule recovers
existing one-to-one blocking and stability at unit quotas without extra
preference laws; the original placement needs hospital transitivity. Prefer
the vacancy-or-replacement rule when promoting the shared semantic primitive.
This preserves the existing raw-ranking API instead of quietly narrowing it.
The experimental files retain both candidates as evidence, not as permanent
parallel public definitions.

This models responsive acceptance by construction. It does not store a free
ranking over cohorts and assert that it is responsive in prose. If a later
consumer needs arbitrary hospital choice functions, that extension must
specify and validate its own substitutability, consistency and size laws.

## Competing designs and roles

| Design | Role under consideration | Risk to test |
|---|---|---|
| Native optional-hospital assignment with quotas | Canonical semantics | Wrong vacancy or cardinality semantics; duplication of the unit-capacity case |
| Ordered copies of hospital positions | Derived theorem backend using existing one-to-one matching | Artificial slot priorities; invalid reverse lifting; equality of totals mistaken for equality of cohorts |
| General hospital choice functions | Possible later generalization | Stronger semantic machinery than the classical theorem needs; missing certificate laws |

Native assignments and slots need not be competing public representations.
The preferred direction is native semantics with a proved slot reduction as
an implementation detail of the proof. Slot indices must not become semantic
preferences over physical hospital places.

## Measured slice

Artifacts live only in `GameTheory/Experimental/Exp168/` and are not exported.
The direct-model checkpoint passes 987 jobs. It proves that feasible fibers
are finite, zero quotas exclude every doctor, unit quotas recover the existing
`IsMatching`, and unit-quota stability is equivalent to canonical one-to-one
stability. The last equivalence needs only transitivity of hospital rankings.
An infinite constant assignment to one quota-one hospital is refuted; the same
fiber provably passes the competing natural-cardinality bound.

The required finite control has two distinct stable outcomes on four doctors
and three hospitals, with quotas `1, 1, 2`. The first two hospitals exchange
their doctors; the third has a nonempty singleton cohort below quota in both
outcomes. An additional doctor is unmatched and unacceptable. A nonstable
assignment with the same headcounts but a different cohort guards the stronger
third conclusion.

The slot prototype proves strict-linearity preservation, exact equality of a
hospital's cohort cardinality with its occupied-slot cardinality, and
clone-stable-to-native-stable projection. These projection results need no
finite doctor or hospital carrier. With finite carriers, it constructs a
native stable assignment through the existing one-to-one DA theorem. Zero
quotas work even when the entire slot type is empty.

A one-doctor/two-slot control refutes stability of an arbitrary reverse lift:
assigning the doctor to the later slot leaves an earlier slot as a blocking
partner, although collapse yields the same stable native assignment as the
early-slot lift. Thus the reverse bridge must choose an ordering; collapse
alone is not a stability equivalence.

The integrated `python scripts/audit.py` run passes the public build (3,872
jobs), complete validation (4,685 jobs), public lint, source boundaries and
transitive standard-axiom checks. The slot-leaf declaration probe reaches
`exists_stable_via_slots` while rejecting Nash, Protocol, project expectation
and PMF declarations. The experimental sources contain no visible equality
transport plumbing. Independent cross-reviews accept the measured semantic
and proof statements. They do not certify the still-unproved reverse bridge.

## Proposed proof dependency path

1. Prove that a stable slot assignment collapses to native stability, with
   exact correspondence between a hospital cohort and its occupied slots.
2. Prove that every native stable assignment has a stable slot lift. An
   arbitrary lift is insufficient: within each hospital, doctors must be
   sorted by its ranking into the ordered positions. Vacant positions follow
   occupied ones. This is the next required adequacy gate.
3. Apply the existing unmatched-agent theorem to stable lifts. Doctor
   unmatchedness is preserved by collapse; equality of occupied status for
   every slot gives each hospital's headcount invariant.
4. Project slot deferred acceptance and use the lift theorem plus proposer
   optimality to obtain a doctor-optimal native stable assignment.
5. Compare that assignment with any stable assignment at an undersubscribed
   hospital. A doctor in the optimal cohort but absent from the other cohort
   would prefer that hospital and block its vacancy. Cohort inclusion plus
   equal finite headcounts gives set equality. Compare both assignments with
   the same doctor-optimal allocation to finish the full theorem.

This path reuses one-to-one deferred acceptance and its proved invariants.
It introduces neither a second rejection process nor a separate equilibrium
predicate. The sorted reverse lift must compile before this path is treated
as established rather than a proof plan.

## Admission conditions and remaining work

Reject an implementation that lets infinite cohorts pass finite quotas,
requires stored finite instances, permits arbitrary team preferences without
laws, treats arbitrary slot lifts as stable, or proves only occupancy counts
while advertising the full theorem. Preserve any counterexample in EXP-168.

Before promotion, extract the shared vacancy-or-replacement primitive and
refactor the existing one-to-one definitions as unit-capacity specializations,
preserving their raw-ranking behavior. Do not retain a second one-to-one
definition behind an equivalence or compatibility adapter. Measure the
dependency cost of the shared owner; finite quotas and extended cardinality
must not introduce probability, Protocol or Analysis into native matching.

Promote a stable native API only after the slot correspondence (or a competing
direct proof) reaches the general theorem and the nonempty-underfill control.
The present branch records measured representation evidence and a precise
dependency path, not a completed rural hospitals theorem. General choice,
many-to-many matching and strategyproofness with hospital reports remain
separate work.
