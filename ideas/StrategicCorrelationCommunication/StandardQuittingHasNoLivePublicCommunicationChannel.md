# Standard quitting has no live public communication channel

## Lifecycle card

| Field | Value |
|---|---|
| Lifecycle | `ACTIVE` |
| Status | `PROVED (M+L), model-local` |
| Priority | `P2` |
| Provenance | Repository audit of `QuittingGame`, `QuittingFirstStageAdapter`, `QuittingLiveMass`, `QuittingRootContinuation`, and `QuittingBehaviorStoppingLaw` |
| Audited | 2026-08-03 |
| Consumer | Question 100's communication-resource audit and any proposed standard-quitting compiler |
| Formalization destination | Core theorem already distributed across the modules above; an optional convenience corollary could be added beside `QuittingLiveMass` |
| Formalization status | The mathematical implication is already derivable from landed Lean theorems; the communication interpretation remains documentation |
| Reactivation / exit | Exit after the interpretation is cross-linked from the stochastic README; reactivate only for a proposed protocol claiming a live public transcript in this exact model |

## Claim ledger

| ID | Claim | Status |
|---|---|---|
| SQ-COMM-1 | Every supported history whose current state is live is the canonical all-Continue history. | `PROVED (M+L)` |
| SQ-COMM-2 | Any live action profile other than all-Continue has a nonempty quitter set and causes absorption. | `PROVED (M+L)` |
| SQ-COMM-3 | Therefore realized public actions cannot carry a nontrivial message while the standard quitting game remains live. | `PROVED consequence, model-local` |
| SQ-COMM-4 | No private or more general endogenous protocol can work in a standard quitting game. | `NOT CLAIMED` |

## Intuition

In the repository's standard quitting game, each player has exactly two actions: Continue and Quit. While the state is live, the only joint action that preserves the live state is the unique all-Continue profile. Thus a public observer who sees that play remains live learns only that the all-Continue profile occurred. Any different public action profile contains a quitter and irreversibly selects an absorbing state.

This is a structural statement about the public action alphabet available **before absorption**. It does not erase the public clock, private randomization, mixed stopping hazards, or strategic information carried by the event of absorption.

## Mathematical statement

Let `a` be a joint Boolean action profile in a live state, with `true` interpreted as Quit. Write

\[
Q(a)=\{i:a_i=\mathrm{Quit}\},
\qquad
c=(\mathrm{Continue},\ldots,\mathrm{Continue}).
\]

The landed interfaces give

\[
Q(a)=\varnothing \iff a=c,
\]

and, from the live state,

\[
\Pr(s_{t+1}=\operatorname{absorbed}(Q(a))\mid s_t=\operatorname{live},a_t=a)=1
\quad\text{when }Q(a)\ne\varnothing.
\]

Moreover, if a history in the support of play has live current state, it equals the canonical history consisting solely of live states and all-Continue actions. Consequently, conditional on remaining live, the realized public action transcript has only one branch at every date.

The exact communication conclusion is:

> There is no nonconstant message encoded by distinct realized public joint-action profiles while preserving the live state of this standard model.

## Evidence

- [`QuittingGame.lean`](../../GameTheory/Concepts/Stochastic/QuittingGame.lean) defines Boolean Continue/Quit actions, the live state `none`, absorption at a nonempty quitter set, zero live payoff, and repeated absorbing payoff.
- [`QuittingFirstStageAdapter.lean`](../../GameTheory/Concepts/Stochastic/QuittingFirstStageAdapter.lean) provides the all-Continue profile and identifies it from emptiness of the quitter set.
- [`QuittingRootContinuation.lean`](../../GameTheory/Concepts/Stochastic/QuittingRootContinuation.lean) gives the live-state transition formula and the quitter-set nonemptiness interface.
- [`QuittingLiveMass.lean`](../../GameTheory/Concepts/Stochastic/QuittingLiveMass.lean) defines the canonical live history and proves that every supported live history equals it.
- [`QuittingBehaviorStoppingLaw.lean`](../../GameTheory/Concepts/Stochastic/QuittingBehaviorStoppingLaw.lean) reduces behavior on the live spine to stopping hazards / quit-time laws, confirming that the surviving public history has no additional action branch.

## Falsifiers and nonclaims

This claim would be falsified for the stated model by any legal pair of distinct joint actions that both preserve the live state and are publicly distinguishable. No such pair exists in the current definition.

It does not cover:

- general quitting games with multiple Continue actions;
- an exogenous public signal, cheap-talk round, mediator, or recommendation device;
- private messages or hidden actions;
- communication that occurs simultaneously with irreversible absorption;
- information in calendar time or in the stopping event;
- a universal impossibility theorem for equilibrium construction.

In particular, the result is not a claim that all histories or arbitrary strategies are trivial. It is the narrower fact that the standard live public-action transcript has a singleton continuation branch.

## Production map

```text
Boolean standard-quitting actions
        |
        +-- empty quitter set <=> all Continue
        |
        +-- nonempty quitter set --> absorbing transition
        |
        `-- supported live history --> canonical all-Continue history
                                      |
                                      `-- no nontrivial live public-action message
```

## Exit condition

Treat SQ-COMM-1 through SQ-COMM-3 as closed for the current model. A future positive communication proposal must either add a resource, move to a general-quitting action space with multiple safe Continue actions, or explain how its message survives an irreversible transition. A future negative proposal must state what it proves beyond this singleton-live-transcript observation.
