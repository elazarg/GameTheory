# Safe signaling actions may compile sunspot randomness

## Lifecycle card

| Field | Value |
|---|---|
| Lifecycle | `ACTIVE` |
| Status | `CONDITIONAL (M+L interfaces)` |
| Priority | `P2` |
| Provenance | Joint public XOR, deviation-safe public-coin selectors, stopped-expectation accounting, and primary literature boundaries |
| Audited | 2026-08-03 |
| Consumer | Positive endogenous-public-randomness constructions, especially general quitting games with multiple Continue actions |
| Formalization destination | A compiler theorem parameterized by a safe signaling phase, disclosure model, continuation splice, and incentive certificate |
| Formalization status | Local robustness and accounting components are landed; the full strategic compiler is not |
| Reactivation / exit | Promote only when a concrete game class supplies all compiler hypotheses; exit if the interfaces are absorbed into such a theorem or a structural impossibility result |

## Claim ledger

| ID | Claim | Status |
|---|---|---|
| SAFE-SIG-1 | Two controlled actions can generate a public XOR bit whose marginal is uniform despite unilateral replacement of either controller's action. | `PROVED (M+L)` |
| SAFE-SIG-2 | The same robust signal marginal induces a robust next-state law only when the physical transition factors through that signal, or under a stronger action-independence hypothesis. | `PROVED (M+L), with obstruction` |
| SAFE-SIG-3 | An action-independent finite stopping kernel can select terminal children with a law independent of the action profile, including unilateral deviations. | `PROVED (M+L)` |
| SAFE-SIG-4 | These ingredients automatically compile every sunspot or private-recommendation equilibrium into an ordinary equilibrium. | `OPEN / NOT CLAIMED` |

## Intuition

Multiple payoff- and transition-safe actions can function as a communication alphabet. If at least two players jointly control the public signal, a unilateral deviator may be unable to bias its distribution. Repeating such stages can sample a finite public child and then splice into a continuation strategy.

The word “safe” does substantial work. A usable signaling action must not trigger an irreversible state change, expose information that destroys obedience, or create a profitable deviation through the cost and timing of the sampling phase. Robustness of the visible bit alone is insufficient.

## Three separate interfaces

| Resource | Information pattern | What is and is not supplied |
|---|---|---|
| Public sunspot | One exogenous public signal observed by all | Public correlation only; no private contingent advice. |
| Solan--Vieille autonomous device | Private, history-dependent current recommendations plus delayed public disclosure | Private obedience information; not an ordinary public coin. |
| Jointly controlled lottery (JCL) | Endogenous public sampling from multiple safe actions, robust to one controller | A route to de-correlation under extra hypotheses; not a generic private-device compiler. |

## Mathematical compiler interface

A positive theorem should make the following hypotheses explicit.

| Interface | Required content |
|---|---|
| Safe action alphabet | At least two publicly distinguishable actions can be used without an unwanted absorbing or state-changing transition. |
| Deviation-robust sampler | Replacing one player's prescribed signaling action does not bias the selected public child law beyond the allowed error. |
| Transition compatibility | The physical next-state kernel factors through the sampled signal, or is action-independent throughout the signaling phase. |
| Payoff accounting | The finite or sublinear signaling charge vanishes in long-run averages, uniformly at the demanded accuracy. |
| Terminal splice | After sampling, play reaches the intended child strategy with the promised state and public memory. |
| Information / obedience | The target needs only public correlation, or a separate argument preserves the private posteriors and obedience inequalities it uses. |
| Recovery | Off-path actions and failed phases have credible continuations; repeated invocation does not accumulate positive-density cost. |

Under these hypotheses, a schematic public compiler has the form

\[
\text{safe signaling phase}
\longrightarrow Z\sim\lambda
\longrightarrow \text{continuation indexed by }Z.
\]

This is deliberately a public-child selector. It is not, without more structure, a private-recommendation compiler.

## Landed mathematical evidence

- [`JointlyControlledPublicXor.lean`](../../GameTheory/Concepts/Stochastic/JointlyControlledPublicXor.lean) proves that XOR of two controlled Boolean actions is uniform under unilateral replacement of either coordinate. It also proves robustness of the next-state law when the transition factors through the signal.
- The same module contains `PublicXorTransitionObstruction`: equal uniform signal laws can coexist with unequal next-state laws when the transition retains the controllers' underlying action profile. This is a permanent warning against lifting signal robustness for free.
- [`DeviationSafePublicCoinSelection.lean`](../../GameTheory/Concepts/Stochastic/DeviationSafePublicCoinSelection.lean) defines a finite public-coin stopping region and proves that an action-independent stopped kernel yields a terminal-child law independent of the profile, including deviations.
- [`OneStepDeviationSafePublicCoinSelector.lean`](../../GameTheory/Concepts/Stochastic/OneStepDeviationSafePublicCoinSelector.lean) compiles an action-independent one-step public transition to absorbing selector states into an adaptive certificate.
- [`FinitePublicCoinStoppedExpectation.lean`](../../GameTheory/Concepts/Stochastic/FinitePublicCoinStoppedExpectation.lean) and [`PublicCoinSelectionPhase.lean`](../../GameTheory/Concepts/Stochastic/PublicCoinSelectionPhase.lean) supply exact stopped-expectation and finite-prefix charge accounting.

## Literature boundary

- The primary arXiv record for Eilon Solan, Omri Nisan Solan, and Ron Solan, [“Jointly Controlled Lotteries with Biased Coins”](https://arxiv.org/abs/1803.00802), states an ordinary undiscounted epsilon-equilibrium application for **positive-recursive general quitting games in which at least two players each have at least two Continue actions**. That de-correlation result depends on a safe-action alphabet absent from the repository's standard binary one-Continue-action quitting model. This pass verified the primary metadata and abstract; it did not line-audit every proof in the paper.
- Eilon Solan and Omri Nisan Solan, [“Sunspot Equilibrium in General Quitting Games”](https://arxiv.org/abs/1803.00878), proves a sunspot epsilon-equilibrium result for positive recursive general quitting games, whose players may have multiple Continue actions. The local [literature audit](../../docs/uniform-equilibrium/references/20-nonzero-sum-equilibrium.md) records that the paper's uniform-equilibrium upgrade is an authorial assertion not independently checked there.
- Heller, Solan, and Tomala, [“Communication, correlation and cheap-talk in games with public information”](https://doi.org/10.1016/j.geb.2011.05.002), studies an explicit cheap-talk extension. Such an extra communication layer is not automatically a legal action channel in the original standard quitting game.

These results motivate the interface; none licenses replacing private current recommendations with a public bit without checking information and obedience.

## Falsifiers

The conditional route fails for a proposed game or phase if any of the following occurs:

- all publicly distinct live actions change the physical state or can absorb;
- a unilateral deviation biases the selected child law;
- the public signal is robust but the next-state law still depends on the hidden controller profile;
- the target's incentive inequalities rely on private recommendations revealed by the compiler;
- signaling costs occur at positive asymptotic density or grow too fast with requested accuracy;
- the protocol lacks a credible terminal or off-path splice.

A theorem establishing all interfaces for a nontrivial game class would confirm the route and should replace this conditional claim. A proof that one interface is structurally impossible in a class would turn it into a negative classification theorem.

## Exit condition

Do not promote a raw “players can exchange `k` bits” lemma. Promote only a theorem whose statement exposes the signal law, transition law, deviation quantifier, information structure, payoff charge, and continuation splice. Until then, use this file as a checklist rather than an existence claim.
