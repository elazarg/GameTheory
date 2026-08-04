# A solo-quitter cycle exists without a join incentive

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `PROVED` |
| Objective priority | `P0` |
| Last audited | 2026-08-04, `7af7acc` |
| Central live claim | If some coordinate `i` has `r_i({i}) > 0` and some rate `p ∈ (0,1]` makes every opponent weakly prefer continuing, then the length-one absorbing cycle in which `i` quits at rate `p` and all opponents are silent is complementary with mismatch zero. |
| Next discriminant | Whether the criterion's failure for every `i` is exactly the class needing `L > 1`. |
| Production destination | `QuittingSoloQuitterEquilibrium.lean` (in flight) |
| Supersedes / superseded by | none |

## Claim ledger

| Claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- |
| The solo-`i` row at rate `p` with `z_i = r_i({i})`, `z_j = r_j({i})` reproduces its own value | `PROVED` | `M` | any weight, any `p ∈ (0,1]` | the criterion |
| It is complementary iff `(1-p)·r_j({j}) + p·r_j({i,j}) ≤ r_j({i})` for every `j ≠ i` | `PROVED` | `M` | as above | the criterion |
| Under `r_i({i}) > 0` it is absorbing with mismatch zero | `PROVED` | `M` | as above | existence base case |
| The criterion is a one-dimensional feasibility problem in `p` | `PROVED` | `M` | the inequality is affine in `p` | decidability of the base case |

## Statement

Fix `i` with `r_i({i}) > 0`. Let `y` be the row with `y_i = p ∈ (0,1]` and
`y_j = 0` for `j ≠ i`, and set

    z_i = r_i({i}),      z_j = r_j({i})   (j ≠ i).

Then `F_y(z) = z`; coordinate `i` is exactly indifferent; coordinate `j ≠ i`
weakly prefers continuing exactly when

    (1-p)·r_j({j}) + p·r_j({i,j})  ≤  r_j({i});                (★)

and the row absorbs, with all-continue mass `1 - p < 1`. If (★) holds for every
`j ≠ i`, the pair is an absorbing complementary length-one cycle, and by the
companion claim its mismatch is `0` because `r_i({i}) > 0`.

Reading of (★): `j`'s payoff from quitting — alone with probability `1-p`, or
together with `i` with probability `p` — must not exceed what `j` gets by
letting `i` quit alone. It is the classical "no opponent wants to join"
condition, here in exact cycle form.

Since (★) is affine in `p`, feasibility is the question of whether finitely
many intervals meet `(0,1]`.

## Calibration

Both known positive-plateau tables satisfy the criterion at `i =` player one,
and in both the feasible set is exactly `p ≤ 1/2`:

| Weight | `r_2({2})` | `r_2({1,2})` | `r_2({1})` | (★) | Equilibrium |
| --- | --- | --- | --- | --- | --- |
| `r({1})=(a,0)`, `r({2})=(1,-1)`, `r({1,2})=(0,1)` | `-1` | `1` | `0` | `-1+2p ≤ 0` | `p = 1/2`, `z = (a,0)` |
| `r({1})=(1/4,0)`, `r({2})=(1,-1/4)`, `r({1,2})=(3/4,1/4)` | `-1/4` | `1/4` | `0` | `-1/4+p/2 ≤ 0` | `p = 1/2`, `z = (1/4,0)` |

Both equilibria are machine-checked, and both sit at the boundary of the
feasible interval. This explains why the zero-pinned backward orbit converges
to them: the orbit is chasing the boundary of (★) from outside.

## Where the criterion fails

On the three-coordinate cyclic table with solo rewards `(1,3,0)`, `(0,1,3)`,
`(3,0,1)` and pair rewards `(1,0,1)`, `(0,1,1)`, `(1,1,0)`, the criterion fails
for every `i`. For `i = 0` and `j = 2`: `r_2({2}) = 1`, `r_2({0,2}) = 1`,
`r_2({0}) = 0`, so (★) reads `1 ≤ 0`, false for every `p`. Cyclic symmetry
gives the same for `i = 1, 2`.

That table is exactly the published witness for stationary incompleteness, and
it carries a length-three candidate cycle: at phase `k`, coordinate `k` quits at
rate `1/2` and the others are silent, with values `(1,2,1)`, `(1,1,2)`,
`(2,1,1)` up to scale. Phase-zero complementarity is checked by hand
(`g = (0, -1/2, 0)`), and the composite absorbs, so `L = 3` plausibly succeeds
where `L = 1` provably fails.

**This is the shape of the general question:** the criterion is the `L = 1` base
case, its failure class is nonempty, and the open question is whether longer
cycles always cover that class with `L` bounded in the number of coordinates.

## Falsifiers and wrong turns

- If (★) holds for some `i, p` but the constructed pair is not complementary,
  the endpoint computation for `j` is wrong — most likely the deleted survival
  factor `c_{-j}(y) = 1-p` or the identification `z_j = r_j({i})`.
- Dropping `r_i({i}) > 0` does not destroy the cycle, only its zero mismatch:
  with `r_i({i}) < 0` the isolated coordinate `i` has mismatch `-r_i({i}) > 0`.
  The hypothesis belongs to the mismatch claim, not the complementarity claim,
  and the two should stay separate in production.
- Absorption must be stated: without `p > 0` the row is all-continue and
  certifies nothing.

## Production map

Formalization in flight as a general theorem over an arbitrary finite
coordinate type, with the two tables above as specializations and their landed
`stationaryRoot_isEndpointNash` results as the faithfulness test. No adapter or
downstream consumer yet beyond the existence question.

## Exit conditions

`MINED` when the general existence question is decided. Returns to the front if
the failure class of (★) is shown to coincide with the class needing `L > 1`,
since that would make the criterion the exact base case of an induction.
