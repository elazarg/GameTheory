# SSProve-Inspired Proposals

This roadmap records ideas suggested by SSProve that fit GameTheory's existing
semantics-first architecture. Each proposal is developed on its own branch,
reviewed before merge, and only then followed by the next proposal.

## 1. Quantitative law distance and approximate transport

Promote finite-PMF total variation from a duality helper into a compositional
distance API: identity, symmetry, triangle inequality, deterministic
data-processing, and finite hybrid chains. Use it to define approximate
realizations and deviation backtranslations, with errors adding under
composition. Connect the resulting approximate transport to bounded-utility
approximate equilibrium.

Status: merged in commit `1372308`.

## 2. Contextual distinguishing advantage

Define observer-relative distinguishing advantage through `ViewFamily`. Prove
that deterministic garbling cannot increase advantage and relate finite Boolean
tests, bounded tests, and total variation. This should remain an observational
layer rather than introduce cryptographic adversaries into `KernelGame`.

Status: merged.

## 3. Preserve the raw-semantics / structured-concepts split

Audit standard constructors and keep protocol transformations at `GameForm`
level whenever utilities are irrelevant. Lift them to `KernelGame` only for
utility-aware statements. Record and enforce the dependency direction from
core semantic laws to solution-concept corollaries.

Status: merged.

## 4. Algebraic APIs for game transformations

Complete identity, composition, congruence, and normalization laws for
transports and standard game constructors. In the quantitative setting,
composition should expose additive error bounds so multi-step reductions can be
proved as short algebraic calculations.

Status: merged in commit `388315e`.

## 5. A separate interactive-game layer

If adaptive protocols become a project goal, introduce a new stateful,
procedure-based semantic layer with explicit composition. Do not enlarge
`KernelGame` with state or calls. Model failure or nontermination with
subprobability semantics rather than silently turning it into an ordinary
outcome.

Status: deferred pending a concrete adaptive-protocol use case.

## 6. Relational rules over probabilistic kernels

Build on `Math.Coupling` with relational kernel judgments and compositional
rules for sequencing, sampling, iteration, and invariants. Apply this first to
repeated or stochastic games, where a program-logic layer has concrete value.

Status: consolidation implemented on `feature/relational-kernel-rules`;
awaiting review. Game-specific applications remain follow-up work.

## 7. Paper-to-library traceability

Add lightweight documentation mapping named paper claims to Lean declarations,
along with dependency and axiom audits for headline results. Keep these maps
close to the relevant terminal theorem modules so they remain reviewable.
