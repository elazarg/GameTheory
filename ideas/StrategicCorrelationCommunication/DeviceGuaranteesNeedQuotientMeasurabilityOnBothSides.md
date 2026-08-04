# A device's guarantee survives strategic embedding only under quotient measurability on both sides

| Field | Value |
| --- | --- |
| Lifecycle | `PENDING` |
| Verdict | `OPEN` (unification), with three instances at their own seals |
| Maturity | `M [reported]` for the two-sided statement; instances as marked below |
| Scope | Correlation, randomization, and padding devices embedded in a stochastic game whose histories are observable |
| Consumer | `LEAN-F0-1`'s converse; any future compiler in this group |
| Falsifier | A device whose guarantee survives while play fails quotient measurability on one side |

## The claim

A device supplies a guarantee — a marginal law, a payoff equivalence, a
protection — defined relative to a **designed quotient** of its realizations.
Embedding it in a game preserves that guarantee only when play is measurable
with respect to that quotient **on both sides**:

- **input side** — every contribution to the device is independent of the
  device's honest input;
- **output side** — every continuation factors through the device's output
  quotient.

Failure on either side breaks the guarantee, but in different places: an
input-side failure breaks the **marginal itself**, while an output-side failure
leaves the marginal and payoff quotient intact and breaks **strategic
transport**.

## Instances

**1. Group sum, input side.** `X` uniformity survives an arbitrary deviator
law, and survives one driven by any private signal — the deviator may randomize
however it likes, through any kernel, and the sum stays uniform. It dies the
moment the contribution may condition on the honest draw: with the last mover
reacting to the draw, the sum is forced to a point. So privacy of the honest
input, not restriction of the deviator, is what the device needs.

**2. Action padding, output side.** `M [reported]` at the behaviour level.
Normalizing illegal actions preserves payoffs and transitions exactly — the
quotient is intact — yet histories record the *raw* action played, so
continuations can condition on which pre-quotient realization occurred. The
marginal survives; the transport does not.

The Markov-level converse is `M+L` and is the degenerate case: the profile type
carries no history, so the channel does not exist and the converse holds. That
the guarantee returns exactly when the history is removed identifies the history
as the channel.

**3. Jointly controlled public XOR, output side.** `M+L`, production. The
transition-factorization hypothesis in `JointlyControlledPublicXor.lean` is this
fence stated for one device: continuations inherit the protection only if they
factor through the protected signal; without factorization the transition may
retain information about the pre-quotient realization.

## Consequence for the padding converse

The two repairs offered for `LEAN-F0-1` are **not** equivalent.

*Normalized-action histories* removes the output-side failure at the source: the
padded game's histories become the legal game's histories, so every equilibrium
transports **definitionally**, with no selection step.

*Normalization-invariant strategies* does not substitute. Restricting the
**deviator** to invariant strategies is unsound outright — the uniform cap
quantifies over all behaviour, so a restricted cap is a strategy-class-scoped
theorem. Restricting only the **prescribed** profile does close the channel, but
the converse must transport an *arbitrary* padded equilibrium while invariance
transports only invariant ones. Bridging that needs an invariant-selection
theorem — any equilibrium implies an invariant one — which is symmetrization
over the label groupoid and meets the recorded non-convexity fence: Nash sets
are not convex, so averaging equilibrium arcs fails
([`RepresentationTheory.md`](../wild/RepresentationTheory.md), §1).

So normalized-action histories is load-bearing; profile invariance is at best a
synthesis-side convenience whose completeness costs an unproved and probably
false-in-general step.

## What would raise the seal

An independent re-derivation of the two-sided statement, or a formalization of
it as a single lemma over an abstract device rather than three instances. The
instances themselves are already at the seals marked above; what is `[reported]`
is that they are one phenomenon.

## Nonclaims

This does not say a device with quotient-measurable play always transports —
only that failing measurability on either side is sufficient to break the
guarantee. It does not establish that the padding converse is false, only that
its output-side channel is real and that one of the two proposed repairs
inherits a blocked selection step.
