# Source corrections: quitting absorption paths

Date: 2026-08-02

This note keeps four logically distinct issues separate. None should be used
as shorthand for another.

## 1. The launched Q107 plateau axiom was transcribed incorrectly

Question 107 deliberately asked about the condition

\[
\widehat\pi\text{ is constant on each component of }[0,1]\setminus T(\pi).
\]

That condition is not the published absorption-path axiom. Definition 4.3
(A.2) of Ashkenazi-Golan--Krasikov--Rainer--Solan removes both the jump set and
the continuous-time set:

\[
(u,v)\text{ a component of }
[0,1]\setminus\bigl(S(\pi)\cup T(\pi)\bigr)
\quad\Longrightarrow\quad
\widehat\pi\equiv v\text{ on }(u,v).
\]

Omitting \(S(\pi)\) excludes ordinary repeated-jump paths. Q107's rational
three-player counterexample correctly refutes only the mistranscribed bridge;
it is not a counterexample to the published plateau axiom.

Primary source: [Absorption paths and equilibria in quitting games,
Definition 4.3](https://doi.org/10.1007/s10107-022-01807-6).

## 2. The published terminal-jump endpoint is underconstrained

Definition 4.13 (SP.1) in the same paper tests a jump only when
\(\widehat\pi_t<1\). A jump that consumes all residual mass is therefore not
tested against any continuation game. This is a genuine endpoint issue, not
the plateau transcription issue above.

In particular, the residual-payoff convention after sure absorption cannot
encode what happens after the off-path all-continue event. A player who is
supposed to quit surely can make that event occur unilaterally, so the
continuation strategy and its best-response value are strategically
load-bearing. Q107 repairs the bridge by separating:

- a **proper** path, whose every jump leaves positive residual survival mass;
  and
- a **First** profile, whose sure first-stage absorption is tested together
  with the prescribed shifted continuation.

The terminal-jump branch in a necessity limit must therefore be transferred
to First using the actual approximating profiles. Jump localization gives
stages with \(p_k\to1\); forcing one near-sure quitter to quit surely while
retaining the shifted continuation gives the quantitative profile transfer.
It is not valid to set the residual payoff to zero and declare the terminal
jump locally perfect.

## 3. The stationary fallback was dropped in a later restatement

Solan--Vieille (2001), Proposition 2.4, restated as Proposition 2.6, proves
the alternative

\[
\text{absorbing sequentially perfect profile is globally approximately
optimal}
\quad\lor\quad
\text{a stationary approximate equilibrium exists}.
\]

Theorem 3.5 of the 2024 absorption-path paper states the first conclusion
without the stationary alternative. The stronger statement is false.

Here is the exact two-player regression. Let

\[
r(Q_1,C_2)=(-1,0),\qquad
r(C_1,Q_2)=(0,0),\qquad
r(Q_1,Q_2)=(-1,0),
\]

and give nonabsorption payoff \(0\). At every stage let player 1 quit with a
fixed probability \(h\in(0,1)\), while player 2 always continues. Every tail
absorbs almost surely. Its continuation payoff is \((-1,0)\), and at every
stage both of player 1's current actions give \(-1\), while both of player 2's
actions give \(0\). The profile is therefore exactly sequentially perfect.
It is not a terminal equilibrium: player 1 can always continue and obtain
\(0\) instead of \(-1\). The missing alternative is present, since the
all-continue stationary profile is an exact equilibrium.

The corrected local-to-global theorem used by Q107 is thus the 2001
alternative, not the stronger 2024 restatement.

The concrete two-player regression is now machine-checked in direct-checked
commits `1217074` and `e7730a1`: exact root indifference, terminal regret one,
and the all-continue stationary fallback are all formalized. The general 2001
alternative is not thereby formalized.

Primary source: [Solan--Vieille, *Quitting Games*, Propositions 2.4 and
2.6](https://www.math.tau.ac.il/~eilons/quitting19.pdf).

## 4. Terminal approximate equilibrium already implies common-horizon uniformity

Solan--Vieille (2001), Proposition 2.13, proves a separate positive bridge:
if one fixed profile is a terminal \(\varepsilon\)-equilibrium, then it is a
common-horizon uniform \(\varepsilon'\)-equilibrium for every strict
\(\varepsilon'>\varepsilon\). The horizon threshold is common to all
unilateral deviations.

Consequently, in a finite quitting game,

\[
\text{terminal approximate equilibria exist at every accuracy}
\quad\Longleftrightarrow\quad
\text{common-horizon uniform approximate equilibria exist at every accuracy}.
\]

There is also a fixed payoff version. Choose terminal
\(\varepsilon_k\)-equilibria with \(\varepsilon_k\downarrow0\), extract a
convergent subsequence of their payoff vectors in the compact box
\([-M,M]^I\), and call the limit \(v\). Given target error \(\delta\), choose
one member with terminal error and payoff distance both below
\(\delta/3\), apply Proposition 2.13 with a strict intermediate error below
\(\delta/3\), and then use convergence of that fixed profile's finite averages
to its terminal payoff. The resulting profile works for every sufficiently
large common horizon, delivers \(v\) within \(\delta\), and has regret below
\(\delta\).

This uniformization theorem does not repair a wrong path certificate. Q107's
path equivalence remains terminal internally; Proposition 2.13 is applied
only after a terminal approximate equilibrium has been produced.

The current Lean boundary matches the mathematical statement:
`333d9c5` formalizes a generic one-sided deviation-approximation interface and
its strict-margin equilibrium transfer, `00c6c73` formalizes the unique
live history and live mass of a quitting profile, and the quitting-specific
proof that Proposition 2.13 satisfies that interface has landed as
`quittingGame_hasUniformDeviationUpperApproximation` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`.
