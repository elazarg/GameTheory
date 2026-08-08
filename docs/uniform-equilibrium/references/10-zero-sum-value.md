# Zero-sum: the uniform value

Two players, zero sum. The object is the **uniform value**, not an equilibrium.
Everything here is settled mathematics; the interest for this program is which
proof ingredients are available and which of them are load-bearing.

Markers: see [README](README.md). Evidence from the 2026-08-02 research pass.

## The definition actually used

`[secondary]` — Renault, *A Tutorial on Zero-sum Stochastic Games*
(arXiv:1905.06577), Definition 1.7:

> `v` is uniformly guaranteed by player 1 if for every `ε > 0` there exist a
> strategy `σ` and `n₀` such that `γₙ(σ, τ) ≥ v − ε` for every `n ≥ n₀` and
> every `τ`; symmetrically for player 2 with `≤ v + ε`. `v` is the **uniform
> value** if both players can uniformly guarantee it.

This is the zero-sum shadow of our `HasUniformDeviationCapConstructor`
(`GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean:169`): one strategy per accuracy,
one horizon threshold, and the guarantee holds at **every** horizon past it.
Note the quantifier order — the threshold may depend on `ε` but not on the
opponent. Getting this order wrong is the standard way to accidentally prove
the (weaker) asymptotic-value statement.

---

## MERTENS–NEYMAN 1981 — stochastic games have a uniform value

**Statement.** `[secondary, primary-blocked]` Every zero-sum stochastic game
with finitely many states and finitely many actions has a uniform value.

**Citation.** J.-F. Mertens and A. Neyman, *Stochastic games*, International
Journal of Game Theory **10**(2), 53–66 (June 1981),
DOI [`10.1007/BF01769259`](https://doi.org/10.1007/BF01769259). Companion
announcement: PNAS **79**(6), 2145–2146 (1982),
DOI [`10.1073/pnas.79.6.2145`](https://doi.org/10.1073/pnas.79.6.2145).

**Source caveat.** The Springer abstract is the single sentence "Stochastic
Games have a value." and the full text is paywalled; Semantic Scholar reports
the PDF closed, and Crossref carries no abstract. The formal statement above
was verified verbatim against Renault's tutorial (Theorem 1.10), **not** the
original. In-paper theorem numbering is unknown to us.

**Proof architecture** (as restated by Renault, and the reason this matters to
us): a random, payoff-adapted *fictitious discount factor*

```text
d_{t+1} = max{ d₁, d_t + g_t − v_{λ_t}(k_{t+1}) + 4ε },   λ_{t+1} = D⁻¹(d_{t+1})
```

together with the submartingale `Z_t = v_{λ_t}(k_t) − φ(λ_t)`
(Renault Prop. 1.16: `E(Z_t) ≥ 2ε·E(Σ_{s<t} λ_s) + Z₁`).

**Dependency structure** — verification insisted on this split, and it is the
one that matters for formalization order:

- Bewley–Kohlberg's **bounded variation** of `λ ↦ v_λ` is *consumed* as an
  input;
- Blackwell–Ferguson (Big Match) and Kohlberg (absorbing games) are
  *methodological precursors* whose construction is generalized, not logical
  dependencies.

Crossref reproduces the paper's complete 7-item bibliography: Bewley–Kohlberg
1976, Blackwell–Ferguson 1968, Gillette 1957, Kohlberg 1974, Mertens–Neyman
CORE DP 8001 (1980), Monash 1980, Shapley 1953.

**Formalization note.** Renault's tutorial proof is complete as exposition but
imports the Bewley–Kohlberg bounded-variation estimate as given and leaves
Lemma 1.12 and parts of Lemma 1.14 to the reader. Anyone formalizing from the
tutorial inherits those gaps.

**Repo status.** `L~` — `UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Criterion.lean:1619`
(`uniformValue_of_rowColumnTrackingCertificates`) is a **conditional**
Mertens–Neyman theorem: it reduces the zero-sum uniform value to two named
hypotheses. The account machinery is in `UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Account.lean` and
`UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/AccountStrategy.lean`; `UniformEquilibrium/Examples/BigMatch/DeficitIndexNoGo.lean` proves the
linear running-deficit index is *not* a universal MN constructor. The
unconditional theorem is not formalized here or anywhere (see
[`50-formalization-status.md`](50-formalization-status.md)).

---

## BEWLEY–KOHLBERG 1976 — asymptotic value and the Puiseux expansion

**Statement.** `[primary]` For finite two-person zero-sum stochastic games:

1. `lim_{n→∞} Vₙ/n = lim_{r→0} r·V(r)`, where `Vₙ` is the value of the
   `n`-stage game and `V(r)` the value of the infinite game discounted at
   **interest rate** `r > 0` — the *asymptotic value* theorem;
2. `V(r)` admits a Laurent expansion in a fractional power of `r`, valid for
   small `r > 0`, with a similar expansion for the optimal strategies.

The main proof is an application of **Tarski's principle for real closed
fields**.

**This is strictly weaker than uniform-value existence.** It asserts
convergence of value sequences and contains no uniform ε-optimal strategies.

**Citation.** T. Bewley and E. Kohlberg, *The asymptotic theory of stochastic
games*, Mathematics of Operations Research **1**(3), 197–208 (1976),
DOI [`10.1287/moor.1.3.197`](https://doi.org/10.1287/moor.1.3.197).

**Attribution trap.** The companion 1976 paper — *The Asymptotic Solution of a
Recursion Equation Occurring in Stochastic Games*, MOR **1**(4), 321–336,
DOI [`10.1287/moor.1.4.321`](https://doi.org/10.1287/moor.1.4.321) — is where
the `n`-stage expansion (approximating `Vₙ` up to `log n`) lives. Cite them
separately.

**Modern form** `[secondary]` (Renault Thm 1.5, Cor. 1.6): there exist
`λ₀ > 0`, an integer `M ≥ 1` and coefficients `r_m ∈ ℝ^K` with
`v_λ(k) = Σ_{m≥0} r_m(k)·λ^{m/M}` for all `λ ∈ (0, λ₀]` and all `k`, because
`{(λ, optimal stationary strategies, value)}` is semi-algebraic and
Tarski–Seidenberg preserves semi-algebraicity under projection. Consequently
`v_λ` converges as `λ → 0`, has **bounded variation** at `0`, and
`lim vₙ = lim v_λ`.

**Sharpness.** Bewley–Kohlberg's own example has `vₙ ~ (ln n)/n`, so `(vₙ)`
need **not** have a Puiseux development in `n`. Finiteness of the action sets
is load-bearing: the conclusion fails for compact action sets (Vigeral 2013).

**Later re-proofs, not corrections.** Szczechla–Connell–Filar–Vrieze, SIAM J.
Control Optim. (1997), DOI `10.1137/S0363012995284138` (complex-analytic,
avoids Tarski's principle); Oliu-Barton, MOR (2014),
DOI `10.1287/moor.2013.0642` (elementary tools).

**Repo status.** `T` / `L~`. The manuscript cites it. The Lean tree has a large
homegrown semi-algebraic and Puiseux apparatus built for this purpose
(`Math/CurveSelection/` — 45 files including `Puiseux.lean`,
`Math/AlgebraicSelection.lean`, `Math/PolynomialSignCell.lean`,
`GameTheory/Concepts/Stochastic/UniformEquilibrium/VanishingDiscount/Bellman/Variety.lean`,
`DiscountedShapleyAlgebraic.lean`), but the Bewley–Kohlberg theorem itself is
not stated or proved.

---

## KOHLBERG 1974 — absorbing games

**Statement.** `[abstract]` For zero-sum two-person repeated games with
absorbing payoffs: `lim vₙ` **always** exists. When the information structure
is **symmetric**, the value `v_∞` of the infinitely-repeated game also exists
and `v_∞ = lim vₙ`.

Verbatim from the Project Euclid abstract:

> A zero-sum two person game is repeatedly played. Some of the payoffs are
> absorbing in the sense that, once any of them is reached, all future payoffs
> remain unchanged. Let `v_n` denote the value of the `n`-times repeated game,
> and let `v_∞` denote the value of the infinitely-repeated game. It is shown
> that `lim v_n` always exists. When the information structure is symmetric,
> `v_∞` also exists and `v_∞ = lim v_n`.

**Citation.** E. Kohlberg, *Repeated Games with Absorbing States*, Annals of
Statistics **2**(4), 724–738 (July 1974),
DOI [`10.1214/aos/1176342760`](https://doi.org/10.1214/aos/1176342760).

**Source caveat.** The PDF is a scanned image with no text layer; JSTOR and
zbMATH return 403. Only the abstract is confirmed; in-paper theorem numbers are
unknown.

**Scoping caveats** (both from verification, both easy to get wrong):

- "always exists" holds within Kohlberg's **finite-action** class.
  Laraki–Sorin's handbook chapter credits the *compact-action* absorbing case
  to Mertens–Neyman–Rosenberg, not to Kohlberg. Do not propagate the
  misattribution.
- The **symmetry** hypothesis bites. Kohlberg himself showed that in the Big
  Match where player 1 has no information on player 2's action, the maxmin is
  `0` and the uniform value does **not** exist. So existence of a uniform value
  for stochastic games depends on the signalling structure on actions.

**Historical placement** `[secondary]` (Laraki–Sorin §5.1.2): "the first proof
of existence of a uniform value was obtained for the Big Match by Blackwell and
Ferguson, then for absorbing games by Kohlberg. The main result is due to
Mertens and Neyman."

**Repo status.** `L` for the *conclusion* in our own setting, by a different
route: `Absorbing.lean:135`
(`exists_uniformEquilibriumPayoff_of_isAbsorbingState`) handles an absorbing
*initial state* for `n` players, and `OneStepAbsorbingChildUniform.lean:96`
handles all-children-absorbing. Kohlberg's theorem — the zero-sum absorbing
class with a genuine live state — is `—` (not represented).

---

## RENAULT 2011 / VENEL–ZILIOTTO 2016 — the one-player branch is settled

**Rosenberg–Solan–Vieille 2002** `[primary]`, Theorem 1: every POMDP with
finite state, action, and signal sets has a uniform value in **behavior**
strategies for every initial distribution. More precisely, the finite-horizon
values converge and, for each \(\varepsilon>0\), one strategy is
\(\varepsilon\)-optimal at every sufficiently long horizon and every
sufficiently patient discount. The constructed general strategy need be
neither pure nor stationary, and the paper's example rules out an exactly
Blackwell-optimal strategy in general. *Blackwell Optimality in Markov
Decision Processes with Partial Observation*, Annals of Statistics **30**(4),
1178–1193 (2002), DOI
[`10.1214/aos/1031689022`](https://doi.org/10.1214/aos/1031689022),
[primary PDF](https://www.math.tau.ac.il/~eilons/hidden15.pdf).

**Chatterjee--Saona--Ziliotto 2022** `[primary]`, Theorem 2.9: every finite
POMDP admits a deterministic finite-memory \(\varepsilon\)-optimal strategy
for every \(\varepsilon>0\). Remark 2.1 explicitly identifies their
\(\sup_\sigma\mathbb E_\sigma[\liminf_N N^{-1}\sum_{t<N}g_t]\) value with
the limit of finite-horizon expected values and the uniform value. Corollary
3.2 shows that
the promised-gap approximation problem is recursively enumerable but not
decidable for arbitrary POMDPs; Remark 3.3 consequently rules out a computable
general memory bound. *Finite-Memory Strategies in POMDPs with Long-Run
Average Objectives*, Mathematics of Operations Research **47**(1), 100–119,
DOI [`10.1287/moor.2020.1116`](https://doi.org/10.1287/moor.2020.1116),
arXiv:[`1904.13360`](https://arxiv.org/abs/1904.13360).

**Q99 consequence -- internal reduction, not an external POMDP theorem.** A
one-public-state, two-player gadget embeds any rational probabilistic finite
automaton as one opponent's hidden controller memory while revealing the full
action profile. Before a check action the opponent's public output is
uninformative; after the check it is an absorbing acceptance bit. The
deviator's long-run best-response value is therefore exactly the PFA value.
This respects Q99's simultaneous-action timing and makes the one-opponent
product-posterior restriction vacuous.

Together with deterministic finite-memory approximation and exact rational
evaluation of each induced finite Markov chain, the gadget gives the sharp
hierarchy for a rational threshold \(c\): \(L>c\) is
\(\Sigma^0_1\)-complete, \(L\le c\) is \(\Pi^0_1\)-complete,
\(L\ge c\) and \(L=c\) are \(\Pi^0_2\)-complete, and \(L<c\) is
\(\Sigma^0_2\)-complete. Rote (2025), Theorem 1(a), supplies a small strict-
threshold construction at \(c=1/7\); Chadha--Sistla--Viswanathan (2018),
Section 2, records strict-emptiness and value-equality completeness. The Q99
game gadget and the resulting combination are repository arguments and are
not Lean-formalized. They imply finite transducer certificates for strict
rejection and rule out any sound-and-complete recursively enumerable family of
finite rational/algebraic certificates for unrestricted cap acceptance.

This does **not** settle exact attainment, observation- versus
belief-stationary policies, a computable \(\eta\)-optimal memory bound in the
restricted product-filter class, historywise reset/re-entry, or clocked
controllers. The general no-memory-bound theorem above cannot be relabelled as
a theorem about that restricted class without another reduction.

**Renault 2011** `[primary]`, Theorem 6.2 (arXiv numbering): "If the set of
states is finite, a MDP with partial observation, played with behavioral
strategies, has a uniform value" — for **arbitrary** action and signal sets,
strictly generalizing RSV. Proved by recasting the POMDP as a deterministic DP
on `Z = Δ_f(Δ(K)) × [0,1]` metrized by the Fortet–Mourier/Wasserstein distance.
*Uniform value in dynamic programming*, JEMS **13**(2), 309–330 (2011),
DOI [`10.4171/JEMS/254`](https://doi.org/10.4171/JEMS/254), arXiv:0803.2758.
(Do not confuse `/254` with `/256`.)

**Renault Corollary 3.9** `[primary]` — the checkable sufficient condition, and
the single most directly reusable statement in this section:

> Let `(Z, d)` be a **precompact** metric space, `r : Z → [0,1]` uniformly
> continuous, and `F` a transition correspondence that is **non-expansive**:
> for all `z, z'` and all `z₁ ∈ F(z)` there exists `z₁' ∈ F(z')` with
> `d(z₁, z₁') ≤ d(z, z')`. Then for every initial state the uniform value
> exists, equals `v*(z) = sup_{m≥0} inf_{n≥1} v_{m,n}(z) = sup_m inf_n w_{m,n}(z)`,
> and `(vₙ)` converges uniformly.

For compact-valued `F`, non-expansiveness is equivalent to being 1-Lipschitz
for the Hausdorff distance.

**Venel–Ziliotto 2016** `[primary]`, Theorem 4 (arXiv numbering): a POMDP with
finite state set `K`, **compact metric** action set `I`, finite signal set `S`,
continuous payoff and continuous transition has a **pathwise** uniform value in
**pure** strategies — `vₙ(p₁) → v_∞(p₁)` for every initial distribution, and
for every `ε > 0` there is a pure strategy `σ` with
`E[liminf_n (1/n) Σ_{m=1}^n g(k_m, i_m)] ≥ v_∞(p₁) − ε`. This settles the RSV
open question positively. arXiv:1505.07495; published as *Strong Uniform Value
in Gambling Houses and POMDPs*, SIAM J. Control Optim. **54**(4), 1983–2008
(2016), DOI [`10.1137/15M1043340`](https://doi.org/10.1137/15M1043340). Note
the retitling.

**Hidden hypotheses the headline statements omit** (all from verification):

- Renault's transitions must be **finitely supported**
  (`q : K × A → Δ_f(S × K)`), so "arbitrary action and signal sets" does *not*
  mean arbitrary measurable transitions.
- Behavior strategies are essential to Renault's Thm 6.2; his Remark 6.5
  explicitly leaves pure ε-optimal strategies open — exactly what
  Venel–Ziliotto close.
- Venel–Ziliotto require **finite** state and **finite** signal sets (only the
  action set is compact metric) and say nothing about infinite state spaces.
- Venel–Ziliotto need no Lipschitz assumption on `q` because `vₙ` is
  automatically 1-Lipschitz in the belief.

**Theorem numbers are arXiv-version artifacts.** The JEMS and SIAM typeset
versions were inaccessible.

**Repo status.** `—`. Nothing in the tree is about partial observation of the
state. Renault Cor. 3.9's precompact + non-expansive criterion is the closest
thing in the literature to a *reusable sufficient condition* of the shape this
program keeps looking for, and it is not represented here at all.

---

## ROSENBERG–SOLAN–VIEILLE 2003 / COULOMB 2003 — imperfect monitoring

**Statement.** `[primary, abstract-level]` In finite two-player zero-sum
stochastic games where at each stage each player observes the current state and
his own action but only a **stochastic signal** about the opponent's action:
the uniform **max-min** value always exists, and it is **independent of player
2's information structure**. Symmetric statements hold for the uniform min-max
value and player 1's information structure.

This is an existence theorem for the uniform maxmin and minmax **separately**,
not for the uniform value. The two may differ, so the uniform value can fail
once perfect monitoring is dropped.

**Citations.** J.-M. Coulomb, *Stochastic games without perfect monitoring*,
IJGT **32**(1), 73–96 (2003); D. Rosenberg, E. Solan and N. Vieille, *The
MaxMin value of stochastic games with imperfect monitoring*, IJGT **32**(1),
133–150 (2003),
DOI [`10.1007/s001820300150`](https://doi.org/10.1007/s001820300150). The
independence-of-the-opponent's-signalling finding traces to Coulomb (1992,
1999, 2001) for absorbing games. Laraki–Sorin Thm 5.5 credits Coulomb and RSV
jointly and calls the proof "extremely involved".

**Concrete failure witness.** The Big Match in which player 1 gets no signal on
player 2's action has maxmin `0` (Kohlberg 1974) versus value `1/2` under
perfect monitoring, hence minmax `1` by symmetry and **no uniform value**.

**Repo status.** `—` for the theorem. The repo's monitoring machinery
(`GameTheory/Concepts/Repeated/Monitoring*.lean`, 12 files) is about
non-zero-sum repeated-game folk-theorem monitoring, a different subject.

---

## The boundary: where the positive theory stops

`[primary]` **Ziliotto 2016.** A zero-sum repeated game with **symmetric**
information — seven states `K = {1*, 1++, 1ᵀ, 1+, 0*, 0++, 0+}`, action sets
`I = J = {C, Q}`, signal set `A = {D, D'}`, public signals, perfect observation
of the actions, players observe payoffs and play in turn — has `v_λ` **not
convergent** as `λ → 0`. This disproves both of Mertens' (1986 ICM)
conjectures: (1) that the asymptotic value always exists, and (2) that when
player 1 is more informed she can guarantee it in the long run
(`maxmin = lim vₙ`) — symmetric information is the degenerate case of "more
informed", so one construction kills both. A §3 variant makes **neither**
`(v_λ)` **nor** `(vₙ)` converge.

*Citation:* B. Ziliotto, *Zero-sum repeated games: counterexamples to the
existence of the asymptotic value and the conjecture maxmin = lim v(n)*,
Annals of Probability **44**(2), 1107–1133 (2016),
DOI [`10.1214/14-AOP997`](https://doi.org/10.1214/14-AOP997), arXiv:1305.4778.

Two qualifications carried from verification:

- "a fortiori no uniform value" is a standard Tauberian **inference**, not
  Ziliotto's sentence — the paper does not discuss the uniform value for *this*
  example (he separately constructed hidden stochastic games where the uniform
  value itself fails).
- Calling this *the* sharp boundary overstates it. Failure occurs on **at least
  two independent axes**: imperfect state observation with finite data
  (Ziliotto), and **compact actions under perfect observation** — Vigeral, *A
  Zero-Sum Stochastic Game with Compact Action Sets and no Asymptotic Value*,
  Dynamic Games and Applications **3** (2013),
  DOI [`10.1007/s13235-013-0073-z`](https://doi.org/10.1007/s13235-013-0073-z),
  gives a **four-state** example.

`[primary]` **Ziliotto 2024** — the conjectures are *restored* on a subclass.
Theorem 1.1: "In any absorbing game with incomplete information on both sides,
`(v_λ)` and `(vₙ)` converge uniformly to the same limit." Class: two players,
zero-sum, finite `K, L, Ω, I, J`; one non-absorbing state; a fixed unknown
parameter about which each player gets one private signal at the outset.
Theorem 1.3 gives a genuinely **uniform** result on the **one-sided** subclass:
for the limit value `v*`, for any `(p, ω)` and `ε > 0` there exist `σ`,
`n₀ ≥ 1` and `λ₀ ∈ (0,1]` such that for all `n ≥ n₀`, all `λ ∈ (0, λ₀]` and all
`τ`, `γₙ(p,ω,σ,τ) ≥ v*(p,ω) − ε` and `γ_λ(p,ω,σ,τ) ≥ v*(p,ω) − ε`.

*Citation:* B. Ziliotto, *Mertens conjectures in absorbing games with
incomplete information*, Annals of Applied Probability **34**(2) (April 2024),
DOI [`10.1214/23-AAP2011`](https://doi.org/10.1214/23-AAP2011),
arXiv:2106.09405.

⚠ **Disambiguation.** "converge uniformly" in Thm 1.1 means uniform convergence
in sup-norm over the parameter space `(p, q, ω)`, **not** the Mertens–Neyman
uniform value. Thm 1.1 alone is an asymptotic-value result; Thm 1.3 is the
uniform-approach statement and is restricted to the one-sided case.

*Priority note recorded by the paper itself:* "In an unpublished working paper,
Laraki wrote an incomplete proof of existence of the limit value in the general
two-sided case. To the best of our knowledge, this proof has not been
corrected, and is independent of this paper."

**Repo status.** `—` for all of it. Our model has perfect state observation and
finite actions throughout, so these non-existence results sit strictly outside
our hypotheses — which is exactly why they belong here: they mark the walls of
the room, and any generalization attempt that drifts past them is dead on
arrival.

---

## REFUTED in verification — do not reuse

- **A purported four-state compact-action counterexample in §2.2 of Renault's
  tutorial** with `I = {1/2^{2ⁿ}}`, `J = [0, 1/2]`, Lemmas 2.8/2.9. Refuted
  1–2. Cite **Vigeral 2013** (DOI `10.1007/s13235-013-0073-z`) directly
  instead.
- **A purported two-state gambling-house Example 1 in Venel–Ziliotto**
  separating uniform value from limiting-average (AP-criterion) value. Refuted
  **0–3**. The mechanical content of Example 1 is real; the separation
  conclusion drawn from it is contradicted by the source itself.

Consequence: this pass produced **no** verified explicit example separating
uniform from limiting-average value. The nearest surviving facts are that
Venel–Ziliotto's pathwise value is strictly stronger than the plain uniform
value, and that Blackwell–Ferguson's own criterion is limiting-average while
Renault's restatement of the Big Match is uniform.
