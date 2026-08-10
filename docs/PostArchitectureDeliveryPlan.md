# Post-architecture delivery plan

Status: active successor-native queue.

The architecture is settled. Delivery now proceeds by dependency depth and
compiled theorem evidence. The authoritative status index is
[`DeliveryLedger.md`](DeliveryLedger.md); recognizable public workflows are in
[`CapabilityMatrix.md`](CapabilityMatrix.md); discriminating examples are in
[`SupportEvidenceMatrix.md`](SupportEvidenceMatrix.md).

## 1. Admission rules

A work package enters the stable library only when it has:

1. one semantic owner at the lowest sufficient layer;
2. a hostile example capable of falsifying the intended theorem;
3. a positive consumer through the canonical API;
4. explicit assumptions on the operation or theorem that needs them;
5. a focused warning-clean build and relevant structural checks; and
6. an updated delivery row in the same change as the evidence.

Architecture-sensitive choices require a measured experiment and decision
record before their public API freezes. Routine theorem recovery after a gate
passes needs no new experiment.

### Review-to-delivery rules

The two repository-wide reviews sharpen how those admission rules are applied:

- treat a reported missing theorem as a falsifiable hypothesis, not an API
  specification; build the smallest hostile model before queueing the theorem;
- measure coverage by a useful canonical workflow with a positive witness, a
  nearby rejection, and a downstream consumer—not declaration-for-declaration
  ancestry or names alone;
- state the exact mathematical and bibliographic scope of standard names;
  familiar terminology does not license a stronger theorem or attribution;
- distinguish correctness corrections from optional breadth in the ledger, so
  an absent but false or unused bridge cannot keep a sound family `partial`;
  and
- keep implementation-loop checks source-level and narrow; run deep
  reachability and full-library audits only at integration or release gates.

## 2. Active dependency queue

### A. Proper-subgame semantics boundary — resolved

EXP-075/D42 corrected textbook SPE to quantify whole-policy deviations only at
information-set-closed roots. EXP-078 then machine-refuted the proposed
single-information-state one-shot characterization, even for finite,
well-founded, perfect-recall play with no information-state revisit. The
initial history can be the only proper-subgame root while profitable policy
changes require complementary changes at two information states.

No duplicate one-shot SPE predicate will be added. Historywise one-shot
optimality, finite assessment-local optimality, and proper-subgame SPE retain
their distinct scopes. A future restricted theorem needs a named consumer and
a premise that explicitly excludes the EXP-078 counterexample.

### B. Unilateral Kuhn realization and Nash transfer

Priority: highest active sequential transfer package.

Goal: for one deviating player, realize the behavioral or mixed policy while
fixing every nondeviator's induced behavior, then transport Nash inequalities.

The current whole-profile law equivalence is not sufficient. The new theorem
must quantify the deviator explicitly and prove equality of the relevant
updated outcome laws. It must retain perfect recall as the public premise;
no-revisit remains an internal consequence.

### C. Repeated public-monitoring breadth

Priority: next mature dynamic family after A/B boundaries are fixed.

Recover, in order:

1. monitoring rank and its finite-prefix laws;
2. self-generation/decomposition over the existing continuation-value API;
3. public randomization only if it has a concrete signal-law consumer; and
4. monitored uniform results without introducing an infinite finite-support
   path law.

PPE remains canonical discounted Nash after every public history. Any new
one-shot theorem must reuse that predicate.

### D. FOSG strategic and counterfactual analysis

Priority: after B fixes the strategic-transfer boundary.

Separate packages:

- strategic/utility transfer through explicit-order serialization;
- terminal and continuation support laws;
- counterfactual reach and continuation coefficients; and
- CFR only after a regret theorem consumes those coefficients.

Do not merge these packages into the FOSG syntax root or hide serialization
order behind choice.

### E. MAID strategic relevance

The promoted MAID compiler now has a multi-player, multi-site deviation and
Nash witness.  The next same-language package is the Koller--Milch
strategic-relevance/requisite-graph analysis: define relevance without storing
utility or equilibrium in syntax, prove it invariant under the accepted
serialization, and give a diagram where pruning changes the strategic policy
domain while preserving the compiled outcome law.  Do not report MAID as
strategic-relevance complete before that slice passes.

### F. Static mature-family rotation

These packages may proceed independently once their owner imports remain
fixed:

- independent rationalizability, secure equilibrium, and remaining
  dominance/elimination results;
- weighted-potential theory;
- general security and constant-sum correlation;
- Sen and median-voter social choice;
- convex-game Shapley-in-core and the balancedness converse;
- matching optimality/strategyproofness; and
- egalitarian and Kalai–Smorodinsky bargaining.

Each package needs its own theorem-level consumer. Shared general mathematics
belongs in Mathlib when available, otherwise in `GameTheoryMath` only after a
live game-theoretic consumer exists.

### G. Mechanism and algorithm extensions

Independent packages:

- analytic envelope identities above the stable single-parameter algebra;
- monotonicity and critical payments for any truthful knapsack approximation;
- move general Groves theory out of the auction namespace and document the
  tie-breaking distinction among the remaining second-price presentations;
- envy-cycle and maximin-share fair division; and
- richer contract or information-design timing only with a typed consumer.

The present greedy knapsack approximation is not a mechanism. All-pay support
is arithmetic, not an auction model.

## 3. Stable boundaries

- `GameTheory.Core` owns static forms, preferences, deviations, equilibrium,
  and the smallest shared foundations.
- `GameTheory.Protocol` owns execution, histories, information, policies,
  assessments, and strategic extraction.
- `GameTheory.Languages` owns syntax and named compilers; syntax imports no
  solution concepts.
- `GameTheory.Finite` owns executable finite algorithms; correctness connects
  them to real-valued proof semantics.
- `GameTheory.Repeated` and `GameTheory.Stochastic` use finite histories and
  finite-support transitions without claiming an infinite path law.
- `GameTheory.Analysis` imports stable semantic roots in one direction for
  topology, convexity, fixed points, and convergence.
- `GameTheoryMath` contains independently reusable mathematics justified by a
  live consumer.
- Frontier may import stable modules; stable modules never import Frontier or
  Challenges.

## 4. Verification policy

During iteration, run the narrowest relevant Lean file or Lake target. Run a
full warning-clean build when imports, package configuration, public roots, or
a delivery gate changes. The Phase 2 and Phase 3 audits default to fast
source-level checks; their `-DeepReachability` mode is reserved for CI and
release gates because it launches many independent Lean processes.

Every completed package records:

- exact files and theorems changed;
- positive and falsifying evidence;
- the focused and full commands run where applicable;
- any axiom check required by the trust surface; and
- the updated row in `DeliveryLedger.md`.

Support claims must never rest only on `True`, `Iff.rfl`, an impossible
premise, an elaboration-only declaration, or Experimental evidence.
