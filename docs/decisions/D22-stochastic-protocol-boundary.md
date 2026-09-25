# D22: stochastic games are native data with a named Protocol bridge

- **Status:** adopted and promoted
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-050; EXP-108 (infinite-play boundary),
  EXP-116 (bounded Kuhn specialization), EXP-117
  (infinite-product policy law), EXP-118 (reverse arbitrary-policy-law
  conditioning), EXP-127/136/138 (general PMF and policy-measure boundaries)

## Decision / question

Where native stochastic-game data, finite-horizon behavioral play, and
uniform equilibrium belong relative to the accepted discrete probability, static
equilibrium, Protocol, Repeated, and Analysis boundaries.

Transition laws are ordinary PMFs. State and action carriers remain unrestricted
in the native data; independent simultaneous sampling requires finitely many
players at the relevant operation. Expected horizon payoffs carry integration
certificates for the actual compared laws. [D62](D62-general-pmf-restoration.md)
supersedes the original finite-support carrier restriction while preserving
this data/bridge boundary.

The source experiments audited the sibling `uniform-existence` branch without
importing it. Its placeholder-dependent general existence claim is excluded;
the independent deviation-cap certificate calculus is retained. Revision and
trust evidence is recorded in EXP-050 and the historical measurements below.

## Competing designs

1. Store native state/action/transition/utility data and expose a named bridge
   to the canonical Protocol execution, information, and behavioral runner.
2. Define a stochastic game as a transparent specialization carrying an
   `ExecutionProtocol` and information model.
3. Treat a stochastic game as a repeated-game extension.
4. Retain a separate probability API, independent finite-history runner,
   `KernelGame` horizon wrapper, stored discount, and raw profile updates.

Design 1 is adopted. A stochastic transition kernel is meaningful without an
initial state or information model, so design 2 stores downstream choices too
early. Stochastic state evolution is not repetition of a fixed stage game, so
design 3 forgets native data. Design 4 duplicates accepted probability,
Protocol, and equilibrium semantics.

## Representative hostile slice

Two Boolean players act simultaneously in two public states. Agreement flips
the state deterministically; disagreement reaches both states with positive
probability; stage utility depends on the current state and the player's
action. A fixed initial state compiles to a nonterminating all-active
`ExecutionProtocol` with perfect public monitoring.

One Protocol behavioral profile feeds every finite horizon. The horizon form
is exactly `InformationModel.toBehavioralGameForm`; expected average payoff is
ordinary `expectedUtility`; epsilon-horizon Nash is an abbreviation of the
canonical `IsεNash`; and uniformity adds only the quantifier over all horizons
past one threshold. Horizon zero has the explicit empty-average value zero.

## Measurements

| Measure | EXP-050 result |
|---|---|
| source revision | active sibling branch `uniform-existence` at `e7730a1`; four relevant files unchanged from `d35c1d8` |
| source follow-up | active branch `81f4a98af8f9eb05c3c13d0657e81505b24e5487`; 52 stochastic files / roughly 34.6k added lines; no additional foundational definition required |
| certificate follow-up | moving branch audited at `dba3b7a1356581d676d0f432bd1cb39ade41afb5`; deviation-cap calculus last changed at `81c60ec813348b9805b3ae26b96a3b767b9e05f9`; existence placeholder excluded |
| source license | MIT, Copyright (c) 2025 Elazar Gershuni |
| source trust hazards | the general uniform-existence constructor contains `sorry`; excluded identically with every theorem depending on it |
| native object | state, player-indexed action, `FinDist` transition, and stage utility only |
| stored capabilities | zero; initial state, action nonemptiness, player finiteness, and decidable equality are operation-local |
| promoted split | `Basic`, `PerfectMonitoring`, `FiniteHorizon`, `Uniform`, plus opt-in root and hostile Example |
| authored import closure | 17 modules; no Analysis, Repeated, Frontier, or Challenges import |

The first experimental presentation exposed Protocol's proof-carrying
`StepEvent` as the policy information state. The audit rejected that public
shape. The promoted bridge maps each event to a proof-free `StageRecord` and
proves source, target, and every pure joint-action coordinate are retained.
Only proposition-valued legality and support evidence remains internal to
Protocol.

## Original experiment rejection conditions

Reject the design if the hostile slice needs `PMF` or a law on infinite paths,
duplicates the Protocol history runner or behavioral-policy type, defines a
second equilibrium predicate, stores discount or finiteness irrelevant to the
native data, requires raw `Function.update` or user-visible transport, imports
the source conjecture, or leaks Analysis/Repeated dependencies into the new
root.

No kill condition fired. The proof-carrying information-state pressure
narrowed the bridge before promotion rather than changing the native object.
These are the recorded EXP-050 conditions. D62 replaces the restriction on
PMF use; the remaining ownership, trust, and dependency restrictions survive.

## Result

`GameTheory.Stochastic.Basic` owns the native game and proof-free public stage
records. `Stochastic.PerfectMonitoring` supplies the selected-initial-state
Protocol execution and information model. `Stochastic.FiniteHorizon` owns the
average-payoff evaluation of the canonical history law. `Stochastic.Uniform`
owns transparent horizon and uniform solution concepts through
`Core.Approximate`. Its post-gate proof surface also exposes finite-horizon
epsilon monotonicity and `HasUniformDeviationCapConstructor`: for every positive
accuracy, one eventual profile is close to a proposed value and caps every
unilateral deviation. Applying the certificate at half accuracy is exactly
equivalent to `IsUniformEquilibriumPayoff`; this is a checked construction
waist, not an existence assertion.

`Stochastic.Kuhn` uses the same bridge boundary. Perfect monitoring supplies
perfect recall. Discrete PMF predrawing requires an actual finite cover of the
relevant public-history sites; finite actions and a bounded horizon alone do
not provide one when chance has infinite support. Given the cover, generic
Protocol predrawing yields exact whole-profile, unilateral updated-law, and
Nash transfers without finite states or a `Fintype PublicHistory` assumption.

The forward policy-measure construction in D57 uses Mathlib's ordinary
infinite product to give one ex-ante probability law over total pure Protocol
policies, independent of horizon. Its finite marginals agree with the
corresponding PMF products. The sole Protocol runner yields every finite-prefix
law and preserves behavioral unilateral replacement without a global finite
site cover (EXP-127/136). Regularity and measurability assumptions belong to the
measure construction. Payoff consequences require actual stage integration and
summability of the discounted expected-payoff series; bounded utility is one
sufficient condition. An infinite-play outcome measure is a separate object.

The reverse construction in D58 conditions independent arbitrary probability
measures over total pure Protocol policies only on finite measurable own-record
cylinders, yielding one behavioral profile before the horizon quantifier.
Perfect monitoring supplies perfect recall; countable measurable local choices
and target-local finite marginals suffice for all finite-prefix and unilateral
replacement laws (EXP-136). No global finite site cover is required. The
generic result does not require regularity, and it does not represent a
correlated joint player law or define an infinite-path outcome measure.

The umbrella `GameTheory.Stochastic` is public and opt-in. At this decision it
remained provisional until the Shapley gate; EXP-051/D23 subsequently closed
that gate through a one-way normalized Analysis bridge. The main `GameTheory` root does not
import it. Positive probes ensure the umbrella
reaches all four layers and canonical approximate Nash; negative probes reject
Repeated theory and the fixed-point dependency.

## Consequences and scope

This decision ports the source branch's basic semantic waist, not its research
claim. There is no theorem asserting general uniform-equilibrium-payoff
existence and no placeholder standing in for it. Future known-case existence
theorems belong above this root, with Analysis used only when their proof
actually needs it.

The adopted data/bridge API is stable. D23 subsequently proved the mature
finite discounted two-player zero-sum slice: its normalized operator is a
contraction with a unique value and stationary statewise saddle selectors. General
uniform-equilibrium existence remains a separate mathematical question.
Its statement layer supports special cases and research-facing certificates
without asserting that general existence follows from the discounted result.
