# Wild ideas: uniform equilibrium as dynamic signal processing

## Purpose

This file records cross-field hypotheses that are precise enough to falsify or
develop.  The governing conjecture is not being identified with an engineering
problem by analogy alone.  The claim is that several of its proof obligations
have exact reformulations as causal filtering, dissipativity, fault recovery,
online rate conversion, or decentralized realization problems.

Experiments live in `experiments/`.  Passing an experiment proves
only the finite statement named there.  It does not close an analytic endpoint
leaf or produce a uniform equilibrium for an arbitrary game.

## The signal-processing dictionary

For player (i), write

\[
e_t^i=g_i(s_t,a_t)-v_i.
\]

The game is a finite stochastic plant.  A behavior strategy is a causal
randomized transducer from public and private histories to actions.  Public
history is the observation signal, a unilateral deviation is an adversarial
input on one controller channel, and (e_t^i) is a tracking or regulation
error.

A certificate inequality of the form

\[
e_t^i+
\mathbb E[\Phi_{t+1}^i-\Phi_t^i\mid\mathcal F_t]
\leq \varepsilon+\Delta C_t^i
\]

is a controlled dissipativity inequality.  The potential is stored energy;
the charge is an external supply or reset ledger.  Telescoping shows that
bounded storage and (C_T^i=o(T)) imply vanishing average tracking error.
Uniformity in the horizon is therefore a prefix-stability demand, not merely a
limit under one evaluation.

The normalized discounted evaluation is an exponential moving-average filter,
whereas the finite-horizon evaluation is a boxcar filter.  An analytic
discounted germ describes behavior as the cutoff frequency tends to zero.
Sorin-type retargeting examples show that agreement of low-frequency values
does not produce a single realizable time-domain controller: a boundary layer
whose time scale is (1/\lambda) retains positive Abel mass but vanishing
Cesaro mass.

## Research directions

### 1. Decentralized dissipativity

Seek a finite family of owner-compatible storage functions and switching
inequalities such that every prescribed transition is approximately harmonic
and every unilateral transition is superharmonic in the deviator's coordinate.
Exceptional switches must have a sublinear realized supply.

This is the path-complete Lyapunov interpretation of the account calculus.  The
nontrivial issue is synthesis under decentralized ownership, not telescoping.
Owner holonomy measures failure of structured realizability even when an
untyped global potential exists.

Q121 Part H now gives one exact scalar descendant. For an exceptional
opponent clock, the relevant supply is not the absolute Snell residual but the
tail-relative bill

\[
\frac{[T_i(w_i)-w_i]_+}{1-\sigma_i}.
\]

The promotion trigger is a causal prefix selector or credible fallback that
makes this bill vanish. The exact prefix-reset regression falsifies any rule
that controls only an unnormalized one-block residual.

Relevant experiments: E03, E06, E09, and E13.

### 2. Approximate predictive-state compression

Exact public beliefs can occupy infinitely many predictive classes.  Uniform
equilibrium nevertheless permits a different finite strategy for every
accuracy.  A plausible route is to split belief dynamics into:

- contracting directions, which admit finite quantization with controlled
  cumulative prediction error;
- neutral or recurrent directions, which must remain exact and may determine
  the rank invariant.

The desired theorem is not ordinary one-step filter approximation.  It must
remain valid under every unilateral law and must translate prediction error
into a sublinear strategic bill.

This direction now has priority over exact finite quotients.  An exact quotient
can fail merely because a continuum of beliefs has distinct future laws, while
uniform equilibrium needs only accuracy-dependent control of continuation
payoffs and unilateral gains.  The right compression target is therefore a
finite public predictor whose accumulated strategic error is (o(N)), uniformly
over the prescribed law and every one-player deviation.  Contractivity under
the prescribed law alone is insufficient.

The Q118 common-box proposal is a finite, table-specific test of the same
geometry: a continuation-value box is a causal invariant tube only if every
decoded predecessor branch maps it back into itself with one common
contraction norm and preserves all inactive and opponent-clock constraints.
Exact interval containment is the promotion trigger; one branch escape or a
mixed-word constraint failure is a decisive falsifier. Passing this test would
not establish general approximate predictive compression.

Relevant experiments: E08 and E14.

### 3. Deviation-robust sigma-delta realization

Analytic germs prescribe small mixed-action or transition rates.  Sigma-delta
modulation suggests converting a fractional rate stream (p_t) into discrete
pulses (u_t\in\{0,1\}) while keeping

\[
\sup_T\left|\sum_{t<T}(u_t-p_t)\right|
\]

bounded.  A random phase generated by a jointly controlled lottery can give
the correct one-time marginals and bounded prefix discrepancy simultaneously
for a fixed rational rate.

For a finite rational circulation with fixed support, the offline existential
part is now understood: a reachable zero-charge closed walk, a nonnegative
integer circulation, a rational circulation, and an eventually periodic
bounded-discrepancy realization are equivalent formulations.  This removes the
purely arithmetical obstruction.  It does not provide one causal public rule
whose guarantee survives the conditional laws induced by an adaptive
unilateral deviation.

The remaining strategic fence is predictability: once a public phase is known, future
pulses may be exploitable.  Fresh independent dithering repairs predictability
but normally destroys bounded pathwise discrepancy.  The real question is
whether causal jointly controlled dither and an error-feedback account can
provide both properties against unilateral deviations.  A satisfactory
statement must quantify over deviation-adapted conditional laws, preserve the
required conditional marginals (or a stated payoff-sufficient projection), and
bound discrepancy on the same realized public history.

Relevant experiments: E01 and E15.

### 4. Detection, isolation, and recovery

Monitoring is sequential fault detection.  Punishment is a recovery controller.
The two must not be conflated.  For a Bernoulli perturbation of size (p), the
best expected log-likelihood growth is (O(p^2)).  A payoff debt of order (p)
cannot be paid from evidence alone.

A useful classification would separate deviations into directly harmless,
linearly observable, quadratically harmless, credibly recoverable, and
information-deficient classes.  The target inequality would bound strategic
damage by conditional information production plus recoverable storage drift.

Relevant experiment: E07.

### 5. Retargeting as terminal-set design

A discounted equilibrium germ resembles a family of model-predictive
controllers.  Its endpoint can lie outside the sustainable Cesaro target set,
just as a finite-horizon controller can have an invalid terminal target.

The natural replacement is an all-accuracy controlled-invariant payoff
correspondence.  Analytic data should select or approach a sustainable target
inside that correspondence, perhaps after discarding an Abel boundary layer.
Turnpike behavior would say that all but a sublinear part of a long play lies
near a recurrent sustainable occupation face.

Relevant experiments: E05, E11, and E16.

The quitting-game exact-debt lane now supplies a literal instance. A
zero-boundary finite-horizon controller can retain a fixed positive terminal
debt although the game has a sustainable stationary payoff off that backward
orbit. Certified boundary reinsertion is exact, and an endpoint mismatch of
size \(\kappa\) costs at most \(\kappa\), independent of prefix length. Thus
the live problem is target selection: extract an actual sustainable relative
boundary from the positive-debt limit instead of preserving the invalid zero
endpoint. Q125 is the mandatory positive regression and Q128's nonsustainable
barycenter is the mandatory warning that value convergence alone does not
select the terminal set.

### 6. Multiscale filter banks

Different analytic obligations occur at different powers of the germ
parameter.  A single phase length may amplify one hazard while underfunding
another.  A filter-bank view assigns scale-specific accounts or epochs, then
controls leakage and reset cost between them.

For finitely many polynomial orders, logarithmically slow scales provide a
universal diagonal calendar: every required access count diverges while every
fixed inverse-power monitoring bill is sublinear.  Superpolynomially rare
events require a separate assumption or adaptive scale discovery.

Relevant experiment: E17.

Q130 gives this direction a concrete rare-hazard front. Its finite exact
chains carry a terminal fence at a scale escaping every fixed rooted window;
ordinary projective limits erase the raw marks, while rescaling recovers a
geometric profile. Any proposed filter bank should first reconstruct this
front and then produce its separate credible-First fallback. Q127's sharper
linear terminal-packet bound prevents the total boundary signal from being
discarded merely because each fixed-time mark vanishes.

### 7. Endogenous robust public randomness

Finite-group addition is a distributed randomness extractor: one honest
uniform controller makes the sum uniform against a unilateral change by the
other.  The continuation inherits this protection only if it factors through
the protected signal.  Raw-action-sensitive transitions reintroduce the
deviator's influence.

The open integration problem is to identify atlas branches whose strategic
continuations are signal-measurable after a legal public phase.

Relevant experiment: E01.

### 8. Continuous-time generator reduction

For first-order transition germs (P_\lambda=I+\lambda A), the reduced Abel
operator converges to the rate-one continuous-time resolvent

\[
(I-A)^{-1}.
\]

This may make slow transition geometry and recurrent faces cleaner.  It does
not transport equilibrium incentives automatically; a useful theorem must
carry unilateral superharmonic inequalities and target selection through the
discretization.

Relevant experiment: E11.

### 9. Causal-state and synchronization complexity

Predictive equivalence of public histories is the causal-state construction
from computational mechanics.  Exact memory can be infinite, while finite
observer quotients can still have exponential size and long synchronization
words.  These phenomena should be treated as lower bounds on public strategy
memory, not as failures of existence.

Relevant experiment: E08.

### 10. Potentials as collateral

A bounded pathwise potential is finite escrow: its oscillation bounds the
maximum prefix drawdown.  This gives a literal financial interpretation to
credible punishment accounts.  Expected-drift potentials are weaker and need
probabilistic collateral, default, or high-probability solvency rules.

Relevant experiment: E12.

## Highest-value standalone questions

1. **Signed stopped dissipativity.** Prove a causal optional-stopping and splice
   theorem from prescribed signed target delivery and unilateral target upper
   bounds, allowing predictable storage switching and a sublinear reset ledger.

2. **Robust sigma-delta.** Characterize rational public circulation streams
   that admit one jointly controlled causal rounding rule with uniformly
   bounded prefix discrepancy and the required conditional law after every
   public history, under every unilateral deviation; otherwise identify the
   smallest finite counterexample.

3. **Approximate predictive quotient.** Give finite-state conditions ensuring
   an ε-predictive public filter whose strategic error is uniformly
   sublinear under all unilateral laws.

4. **Structured storage alternative.** Characterize when owner-typed local
   dissipativity inequalities glue to a path-complete public storage system;
   classify a nonzero obstruction as harmful or occupation-inert.

5. **Invariant target correspondence.** Construct the minimal sustainable
   all-accuracy payoff correspondence and relate analytic germ arcs to it
   without forcing endpoint preservation.

6. **Universal multiscale scheduler.** Diagonalize finitely or countably many
   access, monitoring, switching, and regeneration requirements while retaining
   a single horizon-independent strategy.

## Priority assessment

The least metaphorical and most immediately useful directions are signed
dissipativity, approximate predictive compression, and adversarial
sigma-delta realization.  The rational offline realization problem is a landed
special case; causal conditional-law robustness is the unresolved part.
The continuous-time and filter-bank views are valuable organizing languages.
The collateral interpretation is exact pathwise but becomes speculative for
expectation-only certificates.  No direction should be promoted to the proof
frontier until its experiment has been replaced by a theorem with the correct
deviation and public-history quantifiers.
