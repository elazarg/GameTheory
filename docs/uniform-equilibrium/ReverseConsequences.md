# Reverse consequences of uniform equilibrium

This note asks the reverse question:

> Assume a uniform-equilibrium payoff exists. What algebraic, analytic,
> computational, or dynamical structure must then exist?

The point is not to replace the constructive program. It is to identify
necessary consequences that can be attacked contrapositively. A sufficiently
strong, explicitly falsified consequence would produce a counterexample to
uniform-equilibrium existence.

The note is deliberately status-aware. It separates machine-checked Lean,
complete mathematics whose Lean formalization is still pending, conditional
statements, and false claims.

## Status legend

- **Lean-checked**: proved by a declaration imported by the production library.
- **Lean in this PR**: implemented in the accompanying branch and subject to
  the PR's CI result.
- **Mathematical theorem**: a complete proof is given here, but no production
  Lean declaration is claimed.
- **Conditional theorem**: correct under the displayed additional hypothesis.
- **Open interface**: a precise object or implication is proposed, but no proof
  is claimed.
- **False**: an explicit counterexample is given or referenced.

The semantic waist is always the repository's definition. For every accuracy
`ε > 0`, one behavior profile and one threshold must work for every later
finite horizon, against replacement by an arbitrary history-dependent
behavior strategy. The profile may depend on `ε`; it may not depend on the
horizon eventually chosen.

---

# 1. What is already machine-checked

## 1.1 Reward perturbations are uniformly harmless

**Status: Lean-checked.**

For a fixed game skeleton, let `G'` replace only the stage-payoff table of `G`.
If

\[
\sup_{s,a,i}|g_i'(s,a)-g_i(s,a)|\le \rho,
\]

then every behavior profile, including every unilateral behavioral deviation,
satisfies

\[
|u_{i,T}^{G'}(\sigma)-u_{i,T}^{G}(\sigma)|\le \rho
\quad\text{for every }T.
\]

Consequently an `ε`-Nash profile for `G'` is an `(ε+2ρ)`-Nash profile for `G`,
with the same horizon threshold. The two copies of `ρ` pay for the prescribed
and deviating sides of the Nash inequality.

The relevant declarations are in
`GameTheory/Concepts/Stochastic/Uniform.lean`:

- `StochasticGame.withStagePayoff`;
- `histDist_withStagePayoff`;
- `abs_finiteAveragePayoff_withStagePayoff_sub_le`;
- `IsεHorizonNash.of_withStagePayoff`;
- `IsUniformεEquilibrium.of_withStagePayoff`;
- `isUniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs`;
- `isUniformEquilibriumPayoff_of_uniform_stagePayoff_limit`.

The proof reuses the nearby game's profile directly. No strategy is passed to
a limit.

## 1.2 Existence is closed under reward-table limits

**Status: Lean-checked.**

On a fixed finite skeleton, suppose reward tables `g_n` converge uniformly to
`g`, and every approximating game has some uniform-equilibrium payoff. Then the
limit game has some uniform-equilibrium payoff.

The extra step beyond target-preserving closure is finite-dimensional only.
All approximating equilibrium targets lie in one bounded payoff cube. A
convergent subsequence of targets is selected, and the reward-transfer theorem
is applied along that subsequence. Behavior profiles are still chosen afresh
at each requested accuracy.

See
`GameTheory/Concepts/Stochastic/UniformPayoffExistenceClosure.lean`:

- `exists_stagePayoff_nonneg_abs_bound`;
- `IsUniformEquilibriumPayoff.mem_payoffCube_of_abs_stagePayoff_le`;
- `exists_uniformEquilibriumPayoff_of_uniform_stagePayoff_limit`;
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs`.

### Consequences

For every fixed finite skeleton:

1. the set of reward tables admitting a uniform-equilibrium payoff is closed;
2. the set of counterexample reward tables is open;
3. existence on a dense class of reward tables implies existence on all reward
   tables on that skeleton;
4. if a finite quitting-game counterexample exists, then a rational payoff
   table is also a counterexample, because rational tables are dense;
5. a counterexample cannot depend only on an isolated tie, exact zero, or other
   lower-dimensional payoff degeneracy.

Items 1 and 3 are direct readings of the Lean theorem. Items 2, 4, and 5 are
ordinary finite-dimensional topological consequences.

## 1.3 Abstract path budgets are exactly bounded potentials

**Status: Lean-checked.**

`Math/ChargedPathBudget.lean` proves that a nonnegative charged relation has a
uniform finite path budget if and only if it admits a bounded potential whose
decrement pays every edge charge. Its budget-to-go function is the least
nonnegative supersolution, and the path budget equals the minimum potential
oscillation.

This is an exact ledger theorem, but it is abstract. A game proof must still
construct the right charged relation and show that its budget is uniformly
finite under every deviation-induced history law.

`Math/ChargedPathBudgetCounterexamples.lean` records two load-bearing limits:

- **Towers**: every individual state has finite budget-to-go and every path is
  finite, but there is no common finite budget and no bounded potential;
- **Interpolation**: a bounded potential exists on a compact geometric carrier,
  but every valid potential is discontinuous at one accumulation point.

These examples prohibit replacing uniform boundedness by pointwise finiteness,
or demanding continuity of a semantic storage function without additional
structure.

---

# 2. Arbitrarily thin tail intervals

## 2.1 Definition

**Status: Lean in this PR.**

For a profile `σ` and payoff vectors `lower`, `upper`, say that
`[lower, upper]` is a **uniform tail interval** when one threshold `T₀`
satisfies, for every `T ≥ T₀`,

\[
\mathrm{lower}_i\le u_{i,T}(\sigma)
\]

and

\[
u_{i,T}(\tau_i,\sigma_{-i})\le \mathrm{upper}_i
\quad\text{for every player }i\text{ and behavior deviation }\tau_i.
\]

Following `σ_i` is one admissible deviation, so prescribed play also lies below
`upper`.

The game has **arbitrarily thin tail intervals** if, for every `δ>0`, one can
choose `σ`, `lower`, and `upper` with

\[
\mathrm{upper}_i-\mathrm{lower}_i\le\delta
\quad\text{for every }i.
\]

## 2.2 Characterization

**Status: Lean in this PR.**

`GameTheory/Concepts/Stochastic/UniformTailWidth.lean` proves

\[
\boxed{
\exists v\;\mathrm{UEPayoff}(v)
\quad\Longleftrightarrow\quad
\text{arbitrarily thin uniform tail intervals}.
}
\]

### Forward direction

A uniform `δ/3`-equilibrium delivering `v` gives the interval

\[
[v_i-\delta/3,\;v_i+2\delta/3].
\]

The on-path approximation supplies the lower endpoint. The Nash inequality and
on-path upper approximation supply the deviation endpoint.

### Reverse direction

Take intervals of widths `δ_n = 1/(n+1)` and let

\[
m_i^n=\frac{\mathrm{lower}_i^n+\mathrm{upper}_i^n}{2}.
\]

Stage-payoff boundedness places all midpoint vectors in one compact cube.
Choose a convergent subsequence `m^{n_k} → v`. For a requested accuracy, take
one sufficiently late interval. Its profile is already uniformly credible for
all large horizons, its prescribed payoff is close to its midpoint, and that
midpoint is close to `v`.

Again, only payoff vectors are compactified.

## 2.3 Contrapositive form

**Status: mathematical corollary; a direct Lean corollary is planned.**

If no uniform-equilibrium payoff exists, there is a fixed `δ>0` such that no
profile can eventually trap prescribed play and every unilateral deviation in
coordinatewise intervals of width `δ`.

This is already a quantitative negative target. A counterexample proof need not
identify one particular deviation at all horizons. It may prove that every
profile leaves a permanent width somewhere.

---

# 3. Classical spectral width

The tail-interval theorem avoids suprema over behavior strategies and
`limsup`/`liminf`, which makes it a better Lean interface. The familiar scalar
form is nevertheless useful for analysis and numerical search.

## 3.1 Definition

**Status: mathematical theorem.**

Assume a nonempty finite player set and bounded rewards. For a profile `σ`, set

\[
u_i^T(\sigma)=u_{i,T}(\sigma),
\qquad
b_i^T(\sigma)=\sup_{\tau_i}u_{i,T}(\tau_i,\sigma_{-i}).
\]

Define

\[
L_i(\sigma)=\liminf_{T\to\infty}u_i^T(\sigma),
\qquad
B_i(\sigma)=\limsup_{T\to\infty}b_i^T(\sigma),
\]

\[
W(\sigma)=\max_i\bigl(B_i(\sigma)-L_i(\sigma)\bigr),
\qquad
\Gamma(G,s_0)=\inf_\sigma W(\sigma).
\]

Because following `σ_i` is an admissible deviation,

\[
b_i^T(\sigma)\ge u_i^T(\sigma),
\]

so `B_i ≥ L_i` and `Γ ≥ 0`.

## 3.2 Spectral-width theorem

**Status: mathematical theorem.**

\[
\boxed{
G\text{ has a uniform-equilibrium payoff from }s_0
\quad\Longleftrightarrow\quad
\Gamma(G,s_0)=0.
}
\]

### Proof: uniform equilibrium implies zero width

Let `v` be a uniform-equilibrium payoff. For every `ε>0`, choose a profile
that is uniformly `ε`-Nash and delivers `v` within `ε`. For all sufficiently
large `T`,

\[
v_i-\varepsilon\le u_i^T(\sigma)\le v_i+\varepsilon
\]

and

\[
b_i^T(\sigma)\le u_i^T(\sigma)+\varepsilon
\le v_i+2\varepsilon.
\]

Hence

\[
B_i(\sigma)-L_i(\sigma)\le 3\varepsilon.
\]

Taking the infimum over profiles and then `ε ↓ 0` gives `Γ=0`.

### Proof: zero width implies uniform equilibrium

Choose profiles `σ_n` with `W(σ_n)→0`, and midpoint targets

\[
m_i^n=\frac{B_i(\sigma_n)+L_i(\sigma_n)}2.
\]

Bounded rewards place `m^n` in a compact payoff cube. Pass to a subsequence
with `m^n→v`.

Fix an accuracy. Choose one sufficiently late subsequence member and a small
auxiliary `η>0`. The definitions of `limsup` and `liminf` provide a common
horizon threshold after which

\[
b_i^T(\sigma_n)\le B_i(\sigma_n)+\eta,
\qquad
u_i^T(\sigma_n)\ge L_i(\sigma_n)-\eta.
\]

Since `u_i^T≤b_i^T`, prescribed play is trapped around `m_i^n`, while

\[
b_i^T(\sigma_n)-u_i^T(\sigma_n)
\le B_i(\sigma_n)-L_i(\sigma_n)+2\eta.
\]

Choose `n`, `η`, and the midpoint error small enough. The selected profile then
satisfies the uniform-equilibrium inequalities and delivers `v`.

## 3.3 Regret-or-oscillation obstruction

Write

\[
U_i(\sigma)=\limsup_Tu_i^T(\sigma).
\]

Then

\[
B_i-L_i=(B_i-U_i)+(U_i-L_i).
\]

The first summand measures asymptotic best-response pressure; the second is
horizon oscillation. Therefore nonexistence implies a fixed `δ>0` such that
every profile has some player with either persistent exploitability or
persistent horizon oscillation of order `δ`.

This is useful when candidate profiles use longer punishment blocks or rotating
phases: eliminating regret by moving the phase may merely move the obstruction
into horizon dependence.

## 3.4 Reward-Lipschitz defect

**Status: mathematical theorem.**

If two games have the same skeleton and their rewards differ by at most `ρ`,
then, for every fixed profile,

\[
|B_i^G(\sigma)-B_i^{G'}(\sigma)|\le\rho,
\qquad
|L_i^G(\sigma)-L_i^{G'}(\sigma)|\le\rho.
\]

Hence

\[
|W_G(\sigma)-W_{G'}(\sigma)|\le2\rho
\]

and taking infima gives

\[
\boxed{|\Gamma(G)-\Gamma(G')|\le2\rho.}
\]

Thus a counterexample with `Γ(G)=γ>0` remains a counterexample throughout the
reward ball `ρ<γ/2`. This is the quantitative version of openness.

---

# 4. Bounded work and available storage

## 4.1 Root-level bounded work

**Status: Lean in this PR.**

Fix a target `v` and a positive penalty `η`. Define deviating excess work
schematically by

\[
T\bigl(u_{i,T}(\tau_i,\sigma_{-i})-v_i-\eta\bigr),
\]

and obedient deficit work by

\[
T\bigl(v_i-u_{i,T}(\sigma)-\eta\bigr).
\]

A bounded-work certificate consists of one profile and one nonnegative constant
`B` bounding both expressions for every horizon, player, and unilateral
behavior deviation.

`GameTheory/Concepts/Stochastic/UniformBoundedWork.lean` proves

\[
\boxed{
\mathrm{UEPayoff}(v)
\quad\Longleftrightarrow\quad
v\text{ has bounded-work certificates for every }\eta>0.
}
\]

### Forward direction

Use a uniform `η/2`-equilibrium delivering `v`. At all late horizons, both
penalized work expressions are nonpositive. At the finitely many early
horizons, bounded stage rewards and bounded target coordinates give one common
finite bound.

### Reverse direction

Choose a certificate at penalty `ε/4`. For all sufficiently large `T`,

\[
B/T<\varepsilon/4.
\]

The two work inequalities then give prescribed payoff approximation and the
unilateral Nash bound.

## 4.2 Causal distribution lift

**Status: mathematical theorem; not yet formalized.**

The root-level budget has a canonical dynamic-programming refinement.
Fix `σ`, player `i`, and target `v`. At date `t`, let `μ` be a distribution on
length-`t` public histories reachable by some unilateral deviation. A causal
one-stage control `u` assigns the deviator's mixed action at every history in
that distribution. Opponents use `σ_{-i}`. This determines a next history
distribution

\[
K_i^\sigma(\mu,u).
\]

Let the one-stage expected excess supply be

\[
c_i^v(\mu,u)
=\mathbb E_{\mu,u,\sigma_{-i}}[g_i]-v_i.
\]

Define available storage

\[
P_i(\mu)
=
\sup_{N,u_0,\ldots,u_{N-1}}
\sum_{k<N}\bigl(c_i^v(\mu_k,u_k)-\eta\bigr).
\]

The empty continuation makes `P_i≥0`. A finite root work budget implies
`P_i` is finite at every distribution reachable from the root: otherwise a
finite prefix followed by arbitrarily profitable continuation would make the
root budget infinite.

Prepending one control gives the Bellman inequality

\[
\boxed{
c_i^v(\mu,u)-\eta
+P_i(K_i^\sigma(\mu,u))
\le P_i(\mu).
}
\]

Summing along any unilateral behavior deviation telescopes:

\[
\sum_{t<T}(c_i^v-\eta)
\le P_i(\mu_0)-P_i(\mu_T)
\le P_i(\mu_0).
\]

An analogous storage for obedient deficit work supplies the lower payoff
bound.

### What this proves—and what it does not

It proves that every uniform-equilibrium payoff has an exact causal ledger on
the full distributional deviation system. It does **not** prove that this
storage is:

- uniformly bounded over every reachable continuation state;
- continuous;
- semialgebraic;
- finite-memory;
- publicly observable in a small state;
- strategically implementable by the other players.

Those are compression and credibility problems, not existence of the semantic
storage itself. The Towers and Interpolation examples explain why uniform
boundedness and continuity cannot be inserted for free.

---

# 5. Potentials, currents, and escape

## 5.1 Finite current duality

**Status: mathematical theorem; finite-dimensional Lean formalization is
available in principle through Farkas duality.**

Let a finite directed graph carry a signed incentive charge `c(e)`. Fix a
threshold `η`. Exactly one of the following occurs:

1. there is a potential `P` such that
   \[
   c(e)+P(\operatorname{tgt}e)-P(\operatorname{src}e)\le\eta
   \quad\text{for every edge};
   \]
2. there is a normalized nonnegative circulation `m` with
   \[
   \operatorname{div}m=0,
   \qquad
   \sum_e m_e\bigl(c(e)-\eta\bigr)>0.
   \]

One proof is finite-dimensional Farkas separation. Another is the maximum
cycle-mean theorem: a potential exists exactly when every directed cycle has
mean charge at most `η`; a violating cycle is already a positive circulation.

This is the clean finite anti-ledger. The circulation annihilates every
potential coboundary.

## 5.2 Current-only duality is false in infinite systems

**Status: false; machine-checked counterexample available.**

The unrestricted causal history/distribution system is infinite. There,
failure of a bounded potential need not produce a recurrent positive current.
It may be caused by escape through longer and longer acyclic towers.

The machine-checked `Towers` relation has:

- no infinite path inside any one component;
- finite budget-to-go from every individual state;
- arbitrarily long finite positive-charge paths;
- no directed cycle at all;
- no common finite budget and no bounded potential.

Therefore the alternative

\[
\text{bounded potential}\quad\lor\quad\text{positive invariant current}
\]

is false without compactness or tightness.

Any complete dual must have at least the shape

\[
\boxed{
\text{potential}
\quad\lor\quad
\text{positive recurrent current}
\quad\lor\quad
\text{positive escape/tower}.
}
\]

Compactification may turn an escape object into a boundary current, but that is
an additional theorem, not a consequence of finite Farkas duality.

## 5.3 Gauge invariance

**Status: mathematical theorem.**

Let `F_i` be a bounded state potential and modify expected stage rewards by

\[
g_i'(s,a)
=
g_i(s,a)
+\mathbb E_{Q(\cdot\mid s,a)}F_i(s')-F_i(s).
\]

For any behavior profile, the expected total payoff difference through horizon
`T` telescopes to

\[
\mathbb E[F_i(s_T)]-F_i(s_0).
\]

Hence the average difference is at most `2\|F_i\|_\infty/T`, uniformly over all
profiles and deviations. The two games have exactly the same
uniform-equilibrium payoff set.

A genuine asymptotic obstruction must therefore be invariant under bounded
coboundary shaping. Circulation and current certificates have precisely this
invariance.

---

# 6. Transition perturbations: a sharp falsifier

## 6.1 The natural continuity statement is false

**Status: Lean in this PR.**

Consider a one-player, one-action, two-state game. State `0` pays `0`. State
`1` pays `1` and is absorbing. From state `0`, move to state `1` with
probability `p` and otherwise remain at `0`.

For `p>0`, the probability of still being in state `0` after `t` transitions is

\[
(1-p)^t.
\]

Thus expected stage payoff at date `t` is

\[
1-(1-p)^t,
\]

and the `T`-stage average is

\[
A_T(p)
=1-\frac{1-(1-p)^T}{Tp}.
\]

Therefore `A_T(p)→1` for every `p>0`. With only one action, payoff `1` is the
unique uniform-equilibrium payoff.

At `p=0`, the process remains forever in state `0`, so every finite-horizon
payoff is `0`; target `1` is not a uniform-equilibrium payoff.

Taking `p_n↓0`, the transition kernels converge pointwise—and uniformly on the
finite state-action domain—to the `p=0` kernel, but the uniform-equilibrium
targets remain equal to `1`.

The file
`GameTheory/Concepts/Stochastic/TransitionPerturbationDiscontinuity.lean`
formalizes the game, geometric survival formula, convergence for `p>0`, and
failure of target `1` at `p=0`.

## 6.2 Intuition: the limits do not commute

For every fixed horizon `T`,

\[
A_T(p)\longrightarrow0
\quad\text{as }p\downarrow0.
\]

For every fixed `p>0`,

\[
A_T(p)\longrightarrow1
\quad\text{as }T\to\infty.
\]

So

\[
\lim_{p\downarrow0}\lim_{T\to\infty}A_T(p)=1,
\qquad
\lim_{T\to\infty}\lim_{p\downarrow0}A_T(p)=0.
\]

Reward perturbations commute with horizon averaging because their error is
pointwise additive. Transition perturbations can alter recurrent-class entry,
and an arbitrarily small one-step probability can have order-one eventual
effect.

Any positive transition-continuity theorem needs additional uniform mixing,
common hitting-time, or resolvent-control hypotheses.

---

# 7. Tensor products and complete strategic passivity

## 7.1 Additive tensor closure

**Status: mathematical theorem; not yet formalized.**

Let `G` and `H` have the same players. Form their independent product:

- product state space;
- player `i` chooses a pair of component actions;
- component transitions are conditionally independent;
- stage payoffs add.

If `v` is a uniform-equilibrium payoff of `G` and `w` one of `H`, then

\[
\boxed{v+w\text{ is a uniform-equilibrium payoff of }G\otimes H.}
\]

### Proof

For a requested accuracy, choose component profiles at half the error and take
their product. On-path payoff delivery adds.

A unilateral product-game deviation may correlate its two component actions
and may condition on the complete joint history. Project the resulting play law
to the `G` component. At every projected `G` history, condition on that history
and marginalize over compatible `H` histories and the deviator's `H` action.
This gives a legitimate history-dependent mixed action in `G`. Because the
opponents' `G` strategies depend only on the `G` history and transitions are
independent across components, the projected law is exactly the law generated
by this induced unilateral deviation in `G`. Do the same for `H`.

Apply both component deviation caps and add them.

The missing Lean engineering is finite conditional disintegration on projected
history fibres and equality of the projected history laws.

## 7.2 Ancilla test

If `H` is any game with a known uniform equilibrium, then

\[
G\otimes H\text{ has no uniform equilibrium}
\quad\Longrightarrow\quad
G\text{ has no uniform equilibrium}.
\]

An auxiliary clock, signal, or diagnostic game can therefore expose timing or
cross-copy obstructions. This is analogous to testing passivity after adjoining
an ancilla. The product nonexistence proof must still quantify over every
product-game behavior profile; excluding product-form strategies is
insufficient.

Repeated tensor powers give

\[
v\in\operatorname{UE}(G)
\quad\Longrightarrow\quad
m v\in\operatorname{UE}(G^{\otimes m}).
\]

---

# 8. Robustness to patient evaluations

## 8.1 Discounted payoffs are mixtures of finite averages

**Status: mathematical theorem.**

For a bounded payoff sequence `g_t`, let

\[
A_T=\frac1T\sum_{t<T}g_t.
\]

For discount factor `β∈[0,1)`, Abel summation gives

\[
(1-\beta)\sum_{t\ge0}\beta^t g_t
=
\sum_{T\ge1}T(1-\beta)^2\beta^{T-1}A_T.
\]

The coefficients are nonnegative and sum to one.

More generally, for a nonincreasing evaluation `θ_t≥0` with
`\sum_tθ_t=1` and `θ_t→0`,

\[
\sum_t\theta_tg_t
=
\sum_{T\ge1}T(\theta_{T-1}-\theta_T)A_T.
\]

## 8.2 Consequence for uniform equilibrium

A profile that is uniformly credible for every horizon `T≥T₀` is also
approximately credible for all sufficiently patient discounted evaluations.
The tail mixture uses only averages already controlled by the uniform profile;
the total coefficient on `T<T₀` tends to zero as `β↑1`.

The same argument gives on-path payoff delivery. No convergence uniform over
all deviations is needed beyond the original uniform horizon inequality,
because the mixture identity is applied to each fixed deviation and the same
horizon bounds hold for all of them.

A negative strategy can therefore compare incompatible patient evaluations:
prove that every profile which is nearly credible for one very patient
evaluation is detectably exploitable for another. Two discount scales may
expose phase switching that either scale alone smooths away.

---

# 9. The stationary shadow of arbitrary behavior

**Status: mathematical construction; no completeness claim.**

An arbitrary behavior profile can be represented as a rooted continuation
tree. The root records the current state and mixed action kernel; every public
action/state successor points to its continuation tree. Shifting to the
realized child is a time-homogeneous transition on the space of rooted trees.

Thus history-dependent play becomes stationary after enlarging the state to
its complete continuation object. Long empirical measures of these rooted
objects have invariant subsequential shadows under compact product topology.

A necessary shadow of uniform equilibrium should carry:

- an invariant measure on rooted strategy trees;
- conditional product action kernels;
- the payoff integral;
- unilateral deviation shadows whose payoff integral is capped;
- chronology sufficient to identify which continuation promise follows each
  public successor.

This does not prove a finite-memory theorem. The rooted-tree state is generally
infinite-dimensional. Its value is diagnostic: physical-state stationarity is
too small, while full continuation-tree stationarity loses no behavioral
information.

---

# 10. Quitting games and multiscale absorption currents

## 10.1 Why ordinary occupation is too coarse

**Status: source-backed open interface.**

In the positive-debt quitting-game branch, finite middle blocks are understood
with exact payoff, stopping, anchor, debt, and marked-packet data, but their
calendar lengths can diverge. A long low-hazard interval may contain many
nearly inert stages. Its strategic effect is carried by absorption mass, not by
literal stage count.

With survival `s_t` and conditional absorption hazard `q_t`, define

\[
a_t=s_tq_t.
\]

The ordinary absorption measure

\[
\Lambda=\sum_t a_t\,\delta_{z_t}
\]

compresses inert calendar time while retaining where absorption occurs. But it
is not sufficient for the repository's all-behavior consumer.

## 10.2 Finite enriched-cylinder target

**Status: precise finite formalization target; not claimed proved here.**

Every calibrated finite block should map to a marked absorption cylinder
carrying at least:

1. entry root, exit continuation, and chronological splice data;
2. terminal subprobability measure and residual-survival exit port;
3. conditional marked simultaneous-quitter packet, not merely its remote
   unconditional mass;
4. each player's full quit-time payoff graph and Snell envelope, including
   Never;
5. owner and opponent deleted clocks;
6. promised payoff path and root-measured debt;
7. exact concatenation and rebasing identities.

The first responsible theorem is finite: define this map and prove that the
coordinates recover the existing finite-block semantics exactly. Topology
should be chosen only afterward.

## 10.3 Infinite compactification and decoders

**Status: open.**

An infinite enriched object would need:

- sequential compactness;
- closed payoff, obstacle, mark, and splice semantics;
- a valid-path compiler producing actual accuracy-indexed behavior profiles;
- a failed-path surgery producing a bounded finite modification with a
  cutoff-independent root-debt decrement.

Ordinary absorption-path compactness does not imply these properties after the
strategic coordinates are added.

A decisive falsification experiment is to construct two finite families with
the same ordinary absorption-path limit but incompatible limiting stopping
obstacles, conditional marks, or splice behavior. Such a pair would identify a
missing coordinate or refute that compactification shape.

## 10.4 Current versus concentration

A calendar occupation measure may converge to an inert live phase and discard
rare but decisive absorption events. The correct limit may require several
simultaneous measures:

\[
\Lambda=\sum_t s_tq_t\,\delta_{z_t},
\qquad
\Lambda_i=\sum_t s_{-i,t}q_{-i,t}\,\delta_{z_t},
\]

plus conditional blow-ups at marked packets. This resembles a generalized
Young-measure split between ordinary mass, oscillation, and concentration.

For a negative proof, decoding is unnecessary: sound necessary balance and
obstacle constraints followed by infeasibility would suffice. For a positive
proof, an executable decoder remains indispensable.

---

# 11. A semigroup endpoint heuristic

**Status: conditional theorem and research heuristic.**

Suppose complete finite-block semantics—payoff transport, stopping obstacle,
marks, and splice identity—embed continuously into a compact
right-topological semigroup. Ellis-type compact-semigroup theory then supplies
idempotents. An escaping middle would admit recurrent endpoint factors
schematically satisfying

\[
p^2=p,
\qquad q^2=q,
\qquad ph=h=hq.
\]

For a scalar affine transfer `F(z)=a+cz`, idempotence gives only

\[
c=0
\quad\text{or}\quad
(c=1\text{ and }a=0).
\]

So recurrent affine factors are either constant projectors or inert identities;
a strict contraction `0<c<1` cannot itself be idempotent.

This becomes a valid obstruction only after the compact semigroup is proved to
retain complete strategic semantics. At present that premise is open, so the
idempotent sandwich is a target, not a conclusion about every equilibrium.

---

# 12. Computational consequences

## 12.1 Test density before exact coverage

**Status: rigorous program consequence of reward closure.**

For a semialgebraic catalogue of positive mechanisms, the first question is
not whether every table belongs to the catalogue. It is whether the catalogue
is dense.

- If its closure is the whole payoff-table space, target-free reward closure
  proves existence everywhere.
- If the uncovered set has nonempty interior, choose a rational interior point
  and search for a strict width or bounded-work obstruction there.
- A lower-dimensional unresolved residue does not need its own exact finite
  mechanism if nearby positively solved tables are dense around it.

This can materially reduce the three-player terminal residue problem.

## 12.2 Search for width, not only a best deviation

The tail-width and spectral formulations suggest optimization problems of the
form

\[
\inf_\sigma\max_i\bigl(B_i(\sigma)-L_i(\sigma)\bigr).
\]

A certified positive lower bound is a counterexample. Numerically, the gap can
be decomposed into exploitability and horizon oscillation, which helps diagnose
whether a candidate profile fails strategically or temporally.

Finite-controller restrictions give finite or semialgebraic lower bounds, but
failure in one restricted class is not a global barrier unless a completeness
theorem is supplied.

## 12.3 Search for current-or-escape certificates

On a finite abstraction, Farkas or maximum-cycle-mean duality can search for a
positive incentive circulation. On an unbounded abstraction, one must also
search for tower witnesses: arbitrarily long finite paths whose positive work
escapes every bounded region without recurrent mass.

A finite-level infeasibility certificate for a sound outer approximation is a
valid negative theorem. Feasibility of an outer approximation is merely
diagnostic.

---

# 13. Exact claims that are false

The following tempting strengthenings must not appear as unqualified targets.

1. **False:** uniform-equilibrium payoffs are closed under arbitrary transition
   kernel perturbations. The rare-transition game refutes this.
2. **False:** failure of a bounded potential on an infinite causal system
   always yields a positive countably additive invariant current. Towers refute
   this; escape is a separate branch.
3. **False:** pointwise finite budget-to-go implies one uniform bounded ledger.
   Towers refute this.
4. **False:** a bounded semantic potential can always be chosen continuous on
   a compact carrier. Interpolation refutes this.
5. **Unsupported:** ordinary occupation or absorption measures determine
   all-behavior stopping incentives. Continuation identity, quit-time obstacle,
   and conditional marks can be lost.
6. **Unsupported:** tensor-product closure follows by checking only product-form
   deviations. Arbitrary joint deviations require conditional disintegration.
7. **Unsupported:** a compact coefficient limit is already an executable
   strategy. A compiler or bounded surgery theorem remains necessary.

---

# 14. The proof and refutation fork

The reverse program leaves two clean routes.

## Positive route: density and compression

1. Prove positive mechanisms on a dense payoff-table class.
2. Invoke target-free reward closure to settle degenerate boundary tables.
3. Use bounded work to obtain the canonical full causal ledger.
4. Prove a game-specific compression theorem turning that ledger into public
   phases, finite or compact continuation state, observable charges, and
   credible punishments.

## Negative route: robust width or current-or-escape

1. Find an open payoff cell on which every profile has positive tail width.
2. Equivalently, establish a positive spectral defect `Γ`.
3. Extract either a finite positive incentive current or an escaping tower of
   positive work.
4. Preserve conditional product structure, stopping obstacles, and chronology;
   convex occupation alone may create false correlated witnesses.
5. Use reward-Lipschitz robustness to move to a rational interior table.

The central methodological change is:

> Do not begin by compactifying strategies. First test whether positively solved
> games are dense. If they are not, compactify or dualize deviation work—and
> retain an explicit escape branch.

---

# 15. Lean theorem map for this PR

Subject to the PR's CI result, the branch adds:

## `UniformTailWidth.lean`

- `HasUniformTailInterval`;
- `HasArbitrarilyThinTailIntervals`;
- `IsUniformEquilibriumPayoff.hasArbitrarilyThinTailIntervals`;
- `exists_uniformEquilibriumPayoff_of_hasArbitrarilyThinTailIntervals`;
- `exists_uniformEquilibriumPayoff_iff_hasArbitrarilyThinTailIntervals`.

## `UniformBoundedWork.lean`

- `HasBoundedWorkCertificate`;
- `IsUniformEquilibriumPayoff.hasBoundedWorkCertificate`;
- `isUniformEquilibriumPayoff_of_hasBoundedWorkCertificate`;
- `isUniformEquilibriumPayoff_iff_hasBoundedWorkCertificate`.

## `TransitionPerturbationDiscontinuity.lean`

- the two-state rare-transition game;
- geometric bad-state mass;
- convergence of expected stages and finite averages to one for `p>0`;
- uniform-equilibrium payoff one for every `p>0`;
- failure of target one at `p=0`.

The mathematical sections on classical spectral suprema, causal distribution
storage, finite circulation duality, tensor products, patient evaluations,
rooted-tree stationary shadows, and enriched absorption currents are recorded
here without pretending that their Lean interfaces have landed.
