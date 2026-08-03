# Wild ideas: computability and complexity

This file separates three questions that are easy to conflate:

1. does a uniform equilibrium exist;
2. can a witness be computed from finite game data;
3. how large or expensive must a witness and its certificate be?

The general conjecture asks the first question.  A constructive proof may also
answer the second and third, but existence alone does not automatically do so.
Conversely, a negative complexity result would not refute existence.

## 1. Fix the representation before asking for computability

For rational or real-algebraic transition and payoff data, finite polynomial
conditions have an effective exact representation.  For arbitrary unnamed real
numbers, the phrase “compute from the game” has no invariant meaning.

There are also several distinct outputs:

- a uniform equilibrium payoff;
- an accuracy-indexed strategy;
- a threshold horizon or convergence modulus;
- a finite public controller implementing the strategy;
- a proof-carrying recursive certificate checked by Lean.

One output may be computable while another is not.  For example, a payoff may
be algebraic while every known implementation uses an unbounded-memory limit;
or a strategy may be computable without a computable rate at which its finite
horizon guarantees become valid.

## 2. The quantifier pattern is the first warning

A schematic uniform-equilibrium assertion has the form

\[
 \forall \varepsilon>0\;\exists \sigma_\varepsilon\;\exists N_\varepsilon\;
 \forall N\ge N_\varepsilon\;\forall i\;\forall\tau_i:\quad
 \operatorname{Gain}_{i,N}(\tau_i,\sigma_{-i}^\varepsilon)\le\varepsilon.
\]

For a fixed finite-memory controller, the universal deviation quantifier often
collapses to a finite MDP or mean-payoff verification problem.  The dangerous
step is selecting a controller, memory size, target, and modulus uniformly from
unbounded strategy space.

This suggests treating the program as a hierarchy:

\[
\text{fixed witness checking}
\;<\;
\text{fixed-template synthesis}
\;<\;
\text{bounded-template synthesis}
\;<\;
\text{unbounded witness existence}.
\]

The first three may be decidable even when no effective bound is known for the
last passage.

## 3. Fixed templates are tame—but only relatively

After fixing finite controller modes, support cells, stopping rules, and a
finite recursive tree, the remaining conditions are typically linear,
polynomial, or semialgebraic:

- unilateral deviation checking becomes an MDP, cycle, or occupation-measure
  problem;
- target transport becomes linear programming once realization data are fixed;
- algebraic feasibility is decidable by real quantifier elimination;
- strict failure may admit Farkas or Positivstellensatz certificates.

“Decidable” is not “practical.”  Quantifier elimination can be doubly
exponential, algebraic sample points can have large degree and height, and a
finite public tree may itself be enormous.

The correct complexity parameters include

\[
(|S|,|I|,|A|,L,1/\varepsilon,M,D,B,\Delta),
\]

where \(L\) is input bit size, \(M\) controller memory, \(D\) recursive depth,
\(B\) branching, and \(\Delta\) polynomial degree.  Bounds stated only in the
number of game states can hide exponential dependence on denominators or
algebraic height.

## 4. The missing effective compactness theorem

Suppose every game has some sustainable certificate, but the required number
of phases or child nodes is unbounded.  To turn template enumeration into a
decision or synthesis algorithm one needs at least one of:

1. a computable a priori template bound;
2. a normal form that compresses every witness to bounded size;
3. a proof-carrying certificate language whose successful instances can be
   enumerated, together with an independent reason that one must occur;
4. a compactness theorem with an effective modulus.

Without such a result, dovetailing finite templates is only a semidecision
procedure for positive instances.  Failure of the search says nothing in
finite time.

Question 93 isolates much of this issue.  Question 77 shows why arbitrary
semantic side conditions cannot simply be declared “auditable”: unrestricted
certificate languages can encode nonhalting.

A sharper negative calibration is now available for semialgebraic barrier
languages.  Compact semialgebraic local data, polynomial deterministic flows,
transversal guards, and even positive unit dwell time do not by themselves
yield a generic effective complete barrier calculus: a compact hybrid system
can encode an unbounded counter machine at successively finer spatial scales.
A semantic theorem does hold if the exact compact semialgebraic duration-one
relation is taken as a trusted object: nonviability then has a finite
semialgebraic rank.  But semialgebraicity of the local dynamics does not supply
an effective exact formula for that relation.  The distinction between
“semantic macrostep relation exists” and “macrostep relation is effectively
presented” must remain visible.

This weakens the case for exact finite quotients as the universal compactness
mechanism.  An accuracy-dependent predictive quotient is a better target: it
may ignore distinctions whose cumulative effect on prescribed payoffs and all
unilateral gains is (o(N)).  Such an approximation theorem still needs an
effective modulus on a clearly bounded class; otherwise “compressible” merely
renames the desired conclusion.

## 5. Verification versus synthesis

Finite-controller verification and controller synthesis have sharply different
complexities.  If the controller is given, a deviator faces a finite product
system.  In deterministic products, a positive asymptotic deviation exists
exactly when a reachable directed cycle has positive mean.  A cycle is a short
countercertificate, while absence of positive cycles admits a potential bound.

If the controller is not given, selecting one action for every public context
can already encode Boolean satisfiability: each clause is a cycle, and one
large negative literal reward makes its cycle nonpositive exactly when the
clause is satisfied.  Thus a locally easy verifier can sit behind a
combinatorially hard synthesis problem.

This distinction should guide Lean interfaces.  Concrete children, selectors,
and accounts should be data checked by small theorems.  The global producer of
that data is the research bottleneck.

## 6. Controller size can be exponential in input bit size

If a deterministic cyclic controller must generate a reduced exact rate
\(a/b\), its recurrent cycle length is a multiple of \(b\).  The denominator
needs only \(O(\log b)\) input bits, but the explicit phase controller needs at
least \(b\) states.  Randomization or approximate realization may compress the
controller, but an exact phase-lifted certificate cannot ignore this blow-up.

This is a small model of a broader issue: a theorem that produces a finite
controller need not produce a polynomial-size controller.

## 7. Complexity-theoretic imports

Several mature theories appear directly relevant:

- **mean-payoff and energy games:** deviation verification, bounded accounts,
  positional witnesses, and NP/intersection-coNP frontiers;
- **automata theory:** predictive quotients, synchronization, minimization,
  and exponential observer constructions;
- **real algebraic geometry:** analytic-germ cells, target feasibility,
  algebraic samples, and Positivstellensatz refutations;
- **parameterized complexity:** separate state count from player count, support
  rank, number of owners, memory, and algebraic degree;
- **proof complexity:** minimal Farkas support, Positivstellensatz degree,
  recursive-tree size, and Lean proof-term size;
- **computable analysis:** effective selection from compact strategy spaces and
  the distinction between a computable limit and a computable convergence
  modulus.

The project has used pieces of all but the last two systematically.

## 8. Falsifier fences

- A finite case split does not imply a computable global constructor if leaf
  outputs contain unrestricted semantic propositions.
- Decidability for every fixed template does not imply decidability of the
  union over all templates.
- An existence proof by classical choice need not yield executable strategy
  data or a computable modulus.
- Polynomial-time verification does not imply polynomial-time synthesis.
- “Finite memory exists” does not bound memory polynomially—or computably—by
  the obvious syntactic parameters.
- A high worst-case complexity result may reflect a chosen certificate format,
  not the intrinsic difficulty of uniform equilibrium.

## 9. Concrete research questions

1. For rational finite games, is there a computable function bounding the
   public memory and recursive-tree size of an all-accuracy sustainable
   certificate, assuming such a certificate always exists?
2. Is the existence of a finite-memory \(\varepsilon\)-uniform equilibrium
   decidable when \(\varepsilon\) is rational and part of the input?
3. Can fixed-controller verification be reduced uniformly to one finite MDP
   whose size is polynomial in the explicit controller?
4. Which synthesis fragments are polynomial, mean-payoff-game equivalent,
   NP-hard, or complete for a real-algebraic complexity class?
5. Can the analytic germ and retargeting steps be made effective with explicit
   degree, height, and Puiseux-order bounds?
6. Does every computable rational game possessing a uniform equilibrium possess
   one with a computable strategy and computable convergence modulus?
7. Is there a family with polynomial game description but necessarily
   exponential certificate tree or controller memory?
8. Can proof certificates be normalized so their checking is polynomial even
   when discovering them is not?

## 10. Experiments

- **E28:** exact finite-product cycle verification and potential certificates;
- **E29:** denominator-driven state blow-up for exact deterministic rates;
- **E30:** a 3-SAT reduction to contextual cycle-safe selector synthesis.

These do not settle computability of the conjecture.  They validate the local
verification/synthesis split and exhibit two concrete sources of unavoidable
complexity.
