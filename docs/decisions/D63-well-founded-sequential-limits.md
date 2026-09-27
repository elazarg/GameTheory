# D63: well-founded sequential limits and tight assessment extraction

- **Status:** adopted
- **Date:** 2026-09-27
- **Evidence:** [EXP-142/143](../ExperimentLog.md)

## Decision

Use well-founded recursion to evaluate terminal outcomes of randomized play.
Pure history-dependent terminal execution is its point-mass specialization.
The same canonical transition law governs both terminal and bounded runners;
a sufficient-horizon theorem identifies their outcomes. No uniform horizon
is stored in protocol or assessment data.

Form terminal continuation contexts using the existing context and rationality
predicates. Every alternative remains a whole information-local policy.
Require integration on the actual compared terminal laws. Bounds on terminal
payoffs suffice; values at nonterminal histories need not constrain terminal
utility.

Derive a common pointwise assessment subsequence from finite-set uniform
tightness at each coordinate and countably many coordinates. Ambient action
and history carriers need not be countable: PMF supports provide the countable
sets needed by the extraction proof. Keep this discrete compactness theorem
in independent mathematics.

Terminal continuation reads strategies only at actual decision sites.
Inactive players have forced choices, and unused information values do not
affect execution. The terminal existence criterion therefore counts actual
decision sites, not all raw information values. Total policies can use a
supplied sequence member's laws at unused values.

Permit approximating whole-policy inequalities with errors tending to zero.
The resulting limit is exactly rational. Requiring exact maximizers at each
approximation would exclude otherwise useful infinite-space applications.

## Alternatives and mathematical limits

Finite-fuel evaluation remains useful for finite-prefix questions, but a
rolling truncation can change continuation incentives (EXP-121). Choosing
larger fuel cannot replace a terminal law when finite durations are unbounded.

Well-founded induction follows the same bind structure as randomized
execution. A uniform termination-tail assumption would be an extra restriction
for this class. Cyclic almost-sure termination requires a separate construction
and continuity argument; well-foundedness does not cover it.

Finite simplices give compactness automatically. Infinite discrete carriers
need control of escaping probability mass; finite-set tightness provides it.
General weak measure convergence does not imply pointwise atom convergence,
so a general Prokhorov interface is not the appropriate first owner here.

Extraction and rationality closure do not construct optimal perturbed
assessments. Any existence theorem must either establish those assessments
for its game class or state that input explicitly. Bounded payoffs alone do
not guarantee existence of a best response on an infinite action space.

## Admission and rejection criteria

The terminal slice must handle infinite-support chance, unbounded finite play
lengths, and an actual strategic choice. It must identify pure execution and
sufficient bounded execution without duplicate semantics. The compactness
slice must include countably many coordinates with infinite carriers, plus a
mass-escape counterexample when tightness is absent.

Reject hidden finite carriers or horizons, assumed convergence in the
extraction result, missing payoff integration, omitted whole-policy
deviations, or infinite-game existence inferred solely from compactness.
The experiment log owns commands and measurements; the delivery ledger owns
implementation status.

## Evidence and result

EXP-142 realizes a Boolean decision followed by an infinite-support random
countdown. Legal play is well-founded and has no uniform horizon. Constructed
fully mixed Bayes assessments have terminal value approaching one and
vanishing regret against every repaired whole policy. Their terminal
equilibrium follows from the combined criterion. The information carrier is
uncountable, while the actual decision-site carrier is a singleton.

EXP-143 extracts a common subsequence for countably many oscillating
infinite-support laws on the real carrier. Escaping natural-number point
masses prove the need for a no-mass-loss hypothesis. A finite regression
identifies terminal rationality with sufficient-fuel rationality while
retaining the insufficient-fuel counterexample. These results support the
decision within its stated well-founded and tightness hypotheses.
