# Wild ideas: cryptography and distributed protocols

Cryptographic language is tempting here because players must jointly create
public randomness, detect deviations, remember obligations, and make future
responses credible.  The analogy is useful only after writing down the
available resources.

## 1. The native model is information-theoretic

Players in the stochastic-game conjecture are not computationally bounded.
Their actions and public history are observed according to the game model.
Consequently:

- a public pseudorandom seed gives no unpredictability against a deviator;
- a computational commitment is not binding or hiding against an unbounded
  player unless it is an explicit primitive of the game;
- public-key cryptography and one-way functions cannot be imported for free;
- private channels, pre-shared secrets, and ideal commitments change the model.

The directly relevant theories are therefore information-theoretic coin
flipping, secret sharing, Byzantine agreement, interactive proof systems, and
mechanism-enforced escrow.

## 2. Simultaneous public actions provide live entropy

If two players choose independent uniform elements of a finite group in the
same simultaneous stage, their sum is uniform even when either one changes its
action arbitrarily.  This is a strong one-deviator robust public coin.

The protection applies to that stage's quotient signal.  Once the signal is
public, a deterministic future schedule derived from it is predictable.  Thus
there are two separate resources:

1. **robust generation:** can one deviator bias the current public sample?
2. **persistent secrecy:** after observing the transcript, is future behavior
   still unpredictable?

The native model often supplies the first and not the second.

## 3. Commitment has two logically separate halves

A commitment protocol needs:

- **binding:** the committer cannot change the value after committing;
- **hiding:** the receiver cannot learn the value before opening.

Repeated-game payoffs and absorbing transitions can sometimes enforce binding:
inconsistency forfeits collateral or triggers punishment.  Purely public
histories cannot provide hiding, because the alleged committed value is either
already determined by the transcript or still under some player's future
control.

An ideal simultaneous commit/reveal protocol restores a fair XOR coin because
both values are fixed before either is opened.  But treating the commitment as
ideal explicitly adds a resource.  A valid stochastic-game construction must
realize its binding and hiding properties from the actual action, signal, and
payoff structure.

## 4. Secret sharing identifies the missing resource cleanly

Threshold secret sharing can distribute a secret so that any one share is
statistically independent of it while a qualified set reconstructs it.  This
would create a persistent secret phase robust to one corrupted player.

It requires private shares or private observations.  If every share is written
to the public history, the secret is immediately reconstructible.  Hence
secret-sharing arguments are most useful as resource-separation theorems:

> a proposed construction that behaves like threshold sharing must identify
> the game's actual private channels or admit that it has strengthened the
> model.

## 5. A deterministic seed has a finite entropy budget

Let a hidden seed \(S\) generate an arbitrary deterministic output stream
\(Y_{1:T}\).  The chain rule gives

\[
 \sum_{t=1}^T H(Y_t\mid Y_{<t})
 = H(Y_{1:T})\le H(S).
\]

Stretching a finite information-theoretic seed cannot produce a linear supply
of unpredictable future moves.  It can give excellent discrepancy, but its
average conditional entropy tends to zero.  Fresh simultaneous honest action
can contribute new live entropy every stage.

This is the cryptographic version of the distinction between sigma-delta
calibration and deviation-resistant conditional randomization.

## 6. Detection resembles a public proof system

A monitor can be viewed as producing a public accusation certificate:

- **completeness:** sufficiently harmful deviations eventually generate
  evidence;
- **soundness:** compliant play is not falsely punished too often;
- **attribution:** the evidence identifies an owner who can legally be
  punished;
- **succinctness:** evidence and verification use sublinear resources;
- **enforceability:** the prescribed punishment is itself sequentially
  credible.

The first two resemble sequential hypothesis testing or interactive proofs.
They do not imply the last two.  A statistically convincing detector is not a
cryptographic proof of which player deviated, and a public proof of misconduct
does not itself construct a credible response.

Zero knowledge is usually irrelevant: the public-history model rarely needs to
hide a witness from the players.  Soundness, extractable attribution, and
composable enforcement are the closer analogues.

## 7. Byzantine and distributed-computing viewpoints

The adversary here controls one strategic participant, observes the public
history, and may adapt over time.  Useful comparisons include:

- resilient collective coin flipping;
- Byzantine agreement with authenticated versus unauthenticated messages;
- adaptive versus static corruption;
- common-coin and shared-coin protocols;
- self-stabilizing protocols after detected faults;
- distributed state-machine replication with accountable safety violations.

Important differences must remain explicit.  Standard protocols may assume
private point-to-point channels, signatures, a message scheduler, or honest
majorities.  A stochastic game may offer none of them and must also preserve
payoff incentives, not merely reach agreement.

## 8. Cryptographic reductions as falsifiers

Cryptographic impossibilities can expose hidden resources in a proposed proof:

- a long unpredictable tail generated from one public seed is impossible;
- sequential public coin flipping has a last-mover attack;
- commit/reveal reasoning without an implemented commitment is circular;
- secret-sharing language without private observations is vacuous;
- pooling entropy across invocations is valid only if the relevant conditional
  entropy remains unavailable to the deviator;
- punishment keys or accusation witnesses must be attributable and usable by
  the correct strategic owner.

Computational cryptography may still define a different, interesting theorem
for polynomial-time players.  It should not be confused with the original
unbounded-deviation conjecture.

## 9. Potential constructive imports

1. **Robust quotient coins:** use simultaneous group actions only for
   continuations measurable through the protected quotient.
2. **Ideal-resource compilation:** first prove a theorem assuming a precise
   ideal coin, commitment, or private channel; then separately characterize
   which games implement that resource.
3. **Information-flow types:** label every random variable by who knows it and
   when, preventing a public phase from being used as if secret.
4. **Public accusation certificates:** couple each detector with soundness,
   attribution, and a concrete credible-response consumer.
5. **Entropy accounting:** charge conditional entropy as a consumable resource,
   just as incentive errors and reset debts are charged.
6. **Composability tests:** require that a local randomness or punishment
   primitive retain its guarantee after stopping, rebasing, and adaptive reuse.

## 10. Concrete research questions

1. In the native public-action model, characterize exactly which one-deviator
   robust distributions are implementable in one stage, bounded time, and
   finite expected time.
2. Prove a general no-internal-hiding theorem: under what public-monitoring
   hypotheses can no finite protocol implement a statistically hiding and
   binding commitment?
3. Characterize game transitions that implement payoff-secured binding escrow.
4. What private-signal structures suffice to implement a threshold secret phase
   without changing equilibrium payoffs?
5. Can every usable deviation detector be compiled into a public certificate
   carrying soundness, owner attribution, and a credible punishment?
6. What is the minimum live conditional entropy required to implement an
   accuracy-indexed public lottery with bounded exploitation?
7. Does adaptive reuse of a robust public coin preserve its guarantee under
   arbitrary stopping times and deviator-controlled invocation schedules?
8. Which ideal-resource reductions compose with the recursive child/rebasing
   framework without importing a mediator?

## 11. Experiments

- **E31:** sequential, simultaneous, and ideal commit/reveal coin flipping;
- **E32:** exact threshold-secret-sharing privacy and the failure under public
  disclosure;
- **E33:** the conditional-entropy budget of deterministic seeded schedules
  versus fresh simultaneous entropy.

These experiments identify resource boundaries.  They do not add commitments,
private channels, or computational assumptions to the conjecture.
