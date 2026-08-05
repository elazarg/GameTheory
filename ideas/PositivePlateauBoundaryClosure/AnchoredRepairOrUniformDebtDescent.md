# Anchored repair or uniform optimized-debt descent

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `I`, P0 capstone | PB8/CG8, E40/E46/E47 | zero-debt branch then terminal-to-uniform selection | positive plateau with neither executable repair nor cutoff-independent descent |

## Input contract

Fix a finite quitting table and a sequence of exact finite Nash--Bellman
minimizers whose optimized root debts converge to a positive limit. The input
must come from that same sequence and retain:

- the original date-zero root and its optimized debt;
- the selected debt owner, complete marked terminal quitter set, and a uniform
  positive transported packet-mass lower bound;
- exact-D entry/exit roots, chronological source data, and all playerwise
  `(A,T,χ,B,P)` holonomy coordinates; and
- either a uniformly bounded realized middle or an infinity/stopping-law state
  with a separately proved uniformly bounded finite decoder.

Arbitrary supplied tails, scalar coefficient limits without provenance, and
length-zero certificates are not admissible inputs.

## Required output

For every sufficiently small seam tolerance, produce constants `L,c>0`
independent of the large cutoff and one of the following alternatives.

**Repair.** Decode at most `L` game stages/blocks, chronologically attached to
the supplied minimizer, into an actual terminal behavior tail. The prescribed
payoff recursion and every player's cap against arbitrary behavioral deviations
must hold up to a modulus tending to zero with the single full-state closing
seam. The original owner/action packet and its positive mass must survive the
attachment. This must feed terminal approximate Nash existence—not merely a
local root or a relaxed continuation value.

**Descent — refuted in this grammar (`M`).** The intended output was an exact
zero-boundary extension of at most `L` stages whose aggregate dynamic debt,
evaluated back at the **original date-zero root**, is at most the selected root
debt minus a cutoff-independent `c`.

No such `L, c` exist. For the weight `r({1}) = (a,0)`, `r({2}) = (1,-1)`,
`r({1,2}) = (0,1)` with `0 < a < 1`, the complementary set at each cutoff is a
**singleton** and

\[
 d_m=\frac{a(1-a)}{1-a^{m+1}}\;\downarrow\;a(1-a)>0,
 \qquad
 d_m-d_{m+L}=O(a^m)\to0\ \text{for every fixed }L.
\]

So every bounded-length modification has vanishing decrement, and no finite
appended block can force truncation of the active coordinate. The mechanism is
the seam: a fixed appended block creates a substantial *local* defect, but the
exact complementary repair propagates through the entire preceding array, and
its effect back at the origin decays exponentially in the cutoff.

Accumulation does not rescue it. Sequential decrements telescope,
`Σ_k c_k ≤ d_{m_0} - a(1-a) < ∞`, so no divergent total exists; and sequential
accumulation is equivalent to the uniform route rather than weaker, since both
force a finite horizon with `d_m = 0`.

**Consequence for this capstone.** The stated alternative is no longer
"repair or descent". Descent is closed, and **repair is the only surviving
branch**.

**But the plateau is a property of the pin, not of the game.** That same
weight is trivially solvable: it has an exact stationary equilibrium with zero
debt — player one quits with probability `1/2` at every stage, player two never
quits, values `(a,0)`. With player two never quitting, player one's stop value
is `a` and its continue value is its own continuation, so a constant
continuation `a` gives zero gain; with player one at `1/2`, player two's stop
value is `-1/2+1/2=0` and its continue value is `(1/2)·continuation`, so
continuation `0` gives zero gain. Both are exactly indifferent, and with
terminal continuation `(a,0)` in place of `0` that constant array is
complementary with debt exactly zero at every cutoff.

So `d_∞ = a(1-a)` is manufactured entirely by pinning the terminal
continuation to zero: the pin forces a strictly positive gap at every finite
horizon, which forces the opponent survival product below one, which creates
the debt. Let the gap go to zero and the plateau vanishes.

The refutation is therefore of the **carrier, not the target**. It shows that
the zero-pinned finite-chain family is systematically biased away from
equilibrium by an amount that does not decay. That legitimately closes the
descent branch as defined — but it must not be read as evidence that positive
plateaus are an intrinsic phenomenon of quitting games, because here the game
is easy and only the family is obstructed.

This also identifies the repair concretely. It is not "some seam fix": it is
**unpin the tail**, which is exactly the retained-`V(L)` mechanism that
truncation analysis already isolated and what the marked-cylinder design
exists to carry. The decisive next test is to define the optimized debt over
chains with a *free* admissible terminal continuation and decide whether it
tends to zero. For this weight it is zero at every cutoff immediately. If that
holds generally, the whole plateau family is a pinning artifact; if not, the
surviving plateau is the real object.

E40 makes one accepted seam's scalar error depth-free. E46 gives a greedy
return/exit/dead-end trichotomy, and E47 applies the finite-cover return to an
actual exact-D tail. None preserves the original packet through the middle or
converts an exit/dead end into root debt reduction. Those are the missing game-
facing decoders.

A merely positive or pointwise debt drop is insufficient: it may vanish faster
than the remaining plateau gap. The decrement must be uniform, or accumulated
with a proved divergent total. A local potential exit is not automatically a
new exact Nash--Bellman root. Acceptance requires all quantifiers above and the
existing terminal-to-uniform consumer; fixed-cutoff compactness alone is not
the capstone.

## The seam price, and the three deficits it must not be confused between

The `δ/ρ` seam law is **exact for one object, a sharp bound for a second, and
false for the third** — and the third is the one this group's descent work is
about. Seals differ by leg and must not be quoted as one:

- the exact leg is `L`, machine-checked;
- **the sharp-bound middle leg is `M [reported]` — there is no theorem for it.**
  The formalization's middle deliverable was the transport split, not a bound on
  rowwise complementarity loss;
- the falsity leg is `L`, with an explicit witness.

The exact form needed no hypothesis beyond what the definitions already give:
the successor payoff is affine in the tail value with slope the *full* joint
continue mass, unconditionally, with no exactness assumption. The failure for
the deviation objective has an explicit witness — an isolated coordinate at
hazard rates `1/2` and `1/3`, where the mismatch is a rate-independent constant
while the full deficit varies with the rate, so **no** single `δ` reproduces it
as `δ/ρ`. There the deleted deficit is exactly `0`.

Three contraction deficits are involved and are not interchangeable:

- `ρ_G = 1 - ∏_{t∈G} c(x_t)` — the ordinary **value** recursion over a segment;
- `ρ⁻_{G,i} = 1 - ∏_{t∈G} c_{-i}(x_t)` — coordinate `i`'s **deviation**
  recursion, built from the *deleted* products;
- `μ(B) = S(a)·ρ_B` — the amount of a local block transported to the origin.

Against those:

- for **continuation-value closure with fixed rows** the law is an exact
  residual formula, not an estimate: `z_m - v = d/ρ`, and more generally
  `z_t - v_t = (∏_{u=t}^{m-1} c_u)·(d/ρ)`;
- for **rowwise complementarity loss** it is a sharp upper bound, which may be
  zero;
- for **optimized deviation gain** it is **false**. The correct denominator for
  deviation closure is the *deleted* deficit `1 - ∏ c_{-i}`, not `ρ`. Prefix
  survival is a multiplicative transport factor, never the denominator.

That the deviation objective is priced by the deleted product rather than the
full one is the same deleted-versus-full gap that governs every other
obstruction recorded in this program.

**Two corrections to earlier readings of this law.** It does **not** explain the
refutation below: the exponential decay at the origin and division by absorption
are **independent** effects, the exact factorization being prefix transport
times global re-closing amplification, with local absorption entering only
through a bound on the local map discrepancy. And `ρ → 0` gives an inverse pole
but **not** automatic non-existence at `ρ = 0` — a mass-free value block is the
identity, so it cannot alter an externally prescribed mismatch, yet exact
closure still exists. The stronger gain singularity can occur while full `ρ`
stays bounded away from zero.

**Absorption is statically additive but not consumable.** There is a genuine
one-shot budget for absorption-normalized value corrections, but it does **not**
follow that sequential repairs exhaust a resource, and it does not price
arbitrary complementarity repairs or control the optimized gain recursion. The
conjecture that repeated repair is exhausted by conservation — which would have
closed the accumulation route for every weight rather than one witness — is
**false**.

## The currency has a name: transported leverage

`L`, machine-checked (`QuittingTransportedLeverage.lean`): both leverage
quantities, the coarse absorption bound, the exact re-closing identity, the
vanishing-leverage no-go, and incomparability witnessed in both directions.
The deviation denominator vanishes **exactly** at the isolated window, proved
as an iff — the unit-slope regime under its fourth name. One conflation was
caught by the type-checker rather than review: the enclosing-array deficit is
not the block's own deficit, and the definitions take it as an explicit
parameter so the two cannot be merged. This is the constructive replacement
for the refuted law.
The quantity that actually controls a local modification `B` inside an array `G`
is not absorbed mass but **transported leverage** — the modification's effect on
the block map, amplified by the deficit of the return map being closed:

- **value channel** — `L^val(B;G) = (C_P / ρ̃_G) · sup_{|z|≤1} ‖Φ̃_B(z) − Φ_B(z)‖`,
  which absorption bounds only coarsely, via
  `L^val ≤ 2C_P(ρ_B + ρ̃_B) / ρ̃_G`;
- **deviation channel** — `L^dev_i(B;G) = (Q_{P,i} / (1 − Q̃_{G,i})) ·
  sup_{w∈[-1,1]} |H̃_{B,i}(w) − H_{B,i}(w)|` when `Q̃_{G,i} < 1`, built from the
  block deviation operator
  `H_{t,i}(w) = max{Σ_i(x_t), A_i(x_t) + c_{-i}(x_t)·w}`.

**There is no bound on the deviation leverage in terms of `ρ_B` alone.** That is
the precise sense in which the deviation channel escapes absorption pricing.

Note the block deviation operator is exactly the **anchored max-affine** system
already formalized in this repository — `max{A, T + P·w}` with `A = Σ_i`,
`T = A_i`, `P = c_{-i}` — so its unit-slope dichotomy applies directly, and
`P = 1` is precisely the isolated configuration.

**The corrected obstruction.** A family of modifications whose transported
leverage tends to zero cannot change the origin objective by a fixed positive
amount.

This is **stronger** than the bounded-support refutation recorded above, not a
restatement of it: on a receding-absorber family it also rules out modifications
of arbitrarily large support with vanishing leverage. Across unrestricted arrays
the two are **incomparable** — small support can carry order-one leverage, and
large support can carry vanishing leverage. So the descent branch is closed
against a strictly wider class of repair attempts than the `L`-bounded ones it
was originally stated for.

Related, same source: *extended orbits* — countably many orbit segments, each
either ending at or **converging to** the next, with junk variation summable —
suffice for existence. That is a ready-made replacement for the demand that two
endpoint limits form a genuine bi-infinite orbit through a shared anchor, which
this program recorded as a falsifier.

## What the refutation does and does not show

It does **not** refute equilibrium existence. By the Q125 fence a positive
plateau in the zero-boundary chain grammar does not imply nonexistence, and
both known plateau witnesses are two-player tables, where existence holds
externally. Their equilibria therefore lie **outside** the chain geometry.

The sharper reading is a limitation of the method rather than of the
conjecture: the exact-`D` chain grammar can have its optimized debt plateau
strictly above zero on games that do have equilibria. So a positive plateau is
evidence that the grammar has missed the equilibrium, not that none exists, and
"drive optimized debt to zero" is not a complete route. Any future use of this
capstone must either produce the repair directly or establish that the
grammar's plateau is informative about the game rather than about the grammar.

The immediate open test: exhibit the equilibria of the two plateau witnesses
explicitly and locate exactly where they sit relative to the chain geometry.
That is a bounded, decidable question about two small tables, and it would say
what the grammar is missing.
