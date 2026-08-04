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
