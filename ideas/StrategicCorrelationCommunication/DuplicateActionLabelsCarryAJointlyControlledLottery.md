# Duplicate action labels carry a jointly controlled lottery

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `M [reported]`, P0 | Q157 | the action-padding foundation (`LEAN-F0-1`), the legality chain | a value-preserving transfer for the separating system, or an error in its deviation analysis |

## The theorem

Padding action sets with payoff-irrelevant duplicates — same reward, same
transition, histories recording the **raw** label — is **unsound**: it can
strictly enlarge the set of attainable equilibrium values. The minimal
separating system is sharp at **two players, two states**, one two-element
duplicate fiber per player at one state:

- actions `{c⁰, c¹, x}` with `ν(c¹) = c⁰` at the live state; reward `(1,1)` at
  the live state, `(0,0)` at the dead one; the state survives iff both
  normalized actions are `c⁰`, and `x` kills it permanently;
- the reduced (duplicate-free) attainable set is `{(0,0), (1,1)}`;
- the enlarged attainable set is the **entire diagonal segment**
  `{(λ,λ) : 0 ≤ λ ≤ 1}`.

With one player, or one state, the enlargement is free — both minima sharp.

## The mechanism, and why it defeats every unilateral deviation

The duplicate labels are a **jointly controlled lottery**. Each player plays
`c^{B_i}` for a fair private bit; the public raw history reveals
`Z = B₁ ⊕ B₂`, which is fair and **unbiasable by either player alone** — as
long as one player supplies a fresh fair bit, the other's label choice cannot
move the XOR. Continuation branches on `Z`. A deviator keeps the live state
with probability at most `r/2` per stage from date 2 on, capping every
deviation at exactly the profile's own payoff.

Reduced profiles cannot replicate this: on the live path a reduced profile's
history is **forced** (only `c⁰` is visible), so the two players' survival is
an independent product `α₁α₂` — and the always-`c⁰` deviation collects
`max{α₁, α₂} ≥ √(α₁α₂)`. At target payoff `p` the unavoidable deviation gap is
`√p − p`; at `p = ½`, at least `1/√2 − ½`. The interior of the diagonal is
unreachable: `λ ≤ λ²` fails on `(0,1)`.

## What this settles in the program

**The unconditional padding transfer is false.** The question the legality
chain had reduced to — can a padded-game equilibrium be taken legal without
loss? — is answered **no**. The disintegration chain's conditional transfer
(label-blind + legal witness ⟹ legal payoff, exact equality against a blind
background) stands and is untouched; it is the unconditional step that dies,
and not for want of technique: B2 (simultaneous blinding) and B3 (reducedness
without blindness) both fail *in general*, because the obstruction is the
nonproduct conditional continuation law, not a proof-route artifact.

**The pointwise-repair refutation is now a fact, not a docstring.** The
separating system is exactly the example the recorded obstruction lacked.

**No cheap hypothesis rescues it.** Two players already fail; fiber size two
already fails; a single non-identity action already fails. The checkable safe
cases are one player, one state, trivial retractions — or the repair below.

## The repair, and its price

Recording **normalized** actions in histories makes the enlargement free:
every strategy then factors through normalized histories, per-coordinate
output-pushforward blinds any profile with the joint normalized law preserved
exactly, and deviation caps transfer exactly. This is the answer's §8, and it
is the route the normalized-history subtype was built for.

The price: it **changes the information structure** — perfect monitoring of
payoff-relevant equivalence classes instead of raw actions. It is not a
theorem about the raw-history padded game; it is a different padded game. So
the honest statement for the program is:

> the conjecture for state-dependent action sets is reachable from the
> state-independent conjecture **only** through a padded game whose history
> type is the normalized one — the quotient must be baked into the game, not
> recovered afterwards.

## Connections

- Same shape as [[device-guarantees-need-quotient-measurability-on-both-sides]]:
  a guarantee survives an embedding only when both sides respect the quotient.
  Here the raw-history embedding fails quotient-measurability on the
  *monitoring* side, and the attainable set strictly grows.
- The lottery is the classical jointly-controlled-lottery device arising
  *spontaneously* from padding artifacts — the padded game grants public
  correlation for free. Any future padding or embedding argument must audit
  what correlation devices its bookkeeping smuggles in.

## Open

- Machine-check the separating system against the repository's own
  `normalizedGame` and legality definitions. Dispatched.
- Whether the repo's conjecture statement should be generalized to dependent
  action types (`Act : State → ι → Type`) instead of routing through any
  padding at all — now a genuine design decision, not a convenience question.
