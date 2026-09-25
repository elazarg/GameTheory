# General PMF restoration: semantic review

This review records the pre-migration baseline at
`1dba33272108204204758c6eaa5ef8ce49a428c5`; references below to the current or
proposed implementation describe that snapshot. Current implementation status
is in the [delivery ledger](DeliveryLedger.md) and the
[worklog](PMFRestorationWorklog.md). The full restoration subsequently passed
P0–P4; this review preserves the original design reasoning and pseudocode.
The baseline used finite-support laws; the proposal
restores general `PMF` to the **canonical** form, protocol, preference,
deviation, and assessment semantics. D2 chose a finite-support *representation* after
comparing two finite representations; it did not experimentally establish that
all useful laws have finite support ([D2](decisions/D2-finite-law-representation.md),
EXP-003/004). EXP-110/112 already show a direct infinite-support stopping PMF
and bounded real expectation in experimental code.

## Ownership and target shape

Keep `GameSignature`, `Profile`, and `Profile.update` as the unique strategy,
outcome, and unilateral-replacement owners (`Core/Signature.lean`). In the
target, `GameForm.play : Profile sig → PMF sig.Outcome`,
`GameForm.outcomeLaw` binds a `PMF (Profile sig)`, and the existing
`WeakPreference`, `DeviationScheme`, `IsEquilibrium`, and `IsNash` declarations
use PMF laws. This is an in-place semantic change, with finite-support laws
embedded by `FinDist.toPMF` and a finite-specialization preservation theorem.
It does not promise source compatibility in this greenfield rewrite. An
isolated temporary PMF prototype may validate the design before cutover but
must be removed or reduced to a test afterward. Do not create a permanent
parallel `PMFGameForm`/`PMFProtocol` hierarchy or a universal probability
carrier abstraction. The single equilibrium predicate must still use canonical
`Profile.update` for unilateral deviations and preserve the existing
finite-support propositions under embedding.

Here preservation fixes the compared laws and deviation family. Enlarging
mixed strategies or deviations on infinite carriers can change equilibrium
for arbitrary preferences; equivalence then needs its own hypotheses and
proof. Finite-carrier specialization does not enlarge those law domains.

For sequential play, keep the existing `ExecutionProtocol`/`InformationModel`
and indexed histories (`Protocol/Execution.lean`, `Protocol/History.lean`,
`Protocol/Information.lean`). Change the canonical `ExecutionProtocol.step`
to `PMF State`, then migrate its randomized/behavioral runners and their
downstream theorems to `PMF`. The legality, terminality, progress, menu
adequacy, and history invariants remain the same mathematical notions.
Finite-support inputs should have a theorem showing that the new runner is
the `toPMF` image of the old finite run, proved during migration or against a
temporary reference implementation. This is semantic regression evidence,
not a compatibility adapter retained in the public API.

Sketch (pseudocode; names, universes, and Lean obligations unverified):

```lean
structure GameForm (ι) where
  sig : GameSignature ι
  play : Profile sig → PMF sig.Outcome

def GameForm.outcomeLaw (F) (μ : PMF (Profile F.sig)) :=
  μ.bind F.play

-- Existing deviation schemes and IsEquilibrium consume these PMF laws.
-- FinDist.toPMF gives a finite-specialization theorem for each public concept.

-- A proposition about a specific law and observable, not a default value.
def PayoffAdmissible (μ : PMF Ω) (u : Ω → ℝ) : Prop :=
  Summable (fun ω => (μ ω).toReal * |u ω|)

noncomputable def expectedUtility (μ : PMF Ω) (u : Ω → ℝ)
    (h : PayoffAdmissible μ u) : ℝ :=
  ∑' ω, (μ ω).toReal * u ω
```

The exact definition may use Mathlib's `Integrable u μ.toMeasure` and Bochner
integral, provided a discrete measurability premise is explicit and the
`tsum` bridge is proved. `CountablePMFExpectation.lean` supplies a bounded
integral/`tsum`/`FinDist.expect` example. A bare real `tsum` or Bochner
integral is unsafe as a payoff API: Mathlib's default for a nonsummable sum or
nonintegrable integral can silently return zero. The summability or
integrability proof must travel to every comparison. `ENNReal` expected values
are useful for nonnegative objectives, but do not by themselves express
signed payoff comparisons.

Two admissibility routes are useful. A pointwise **uniform bound**
`∀ ω, ‖u i ω‖ ≤ C i` gives integrability for every PMF and every deviation;
it is a convenient sufficient hypothesis for Nash or sequential rationality.
The weaker **per-law** route allows unbounded payoff but must certify the
status quo *and every law under every quantified deviation*. A predicate that
checks only the equilibrium profile and silently excludes an inadmissible
deviation changes Nash's quantifier. State such a restricted-deviation concept
explicitly if needed, or use an extended-value preference with its own clear
mathematics. A context should hold a law-producing outcome function and a
preference on laws, or a `value` with a certificate for every candidate it
compares; it must not make `Context.value : candidate → ℝ` by calling an
unguarded integral (`Protocol/Assessment.lean`, `BehavioralAssessment.lean`).

## Sequential obligations

The canonical PMF runner should follow the existing terminal-first recursion and use
`PMF.bindOnSupport` when the continuation takes a proof that a sampled
successor is in the transition support. This is essential for dependent
`History.extend` and legal transitions, not a cosmetic rewrite of `bind`.
Prove `runFrom_add`, terminal absorption, support/reach equivalence, and the
finite-to-PMF runner commutation during migration. Finite players remain a local capability for
independent simultaneous choice (`FinDist.pi` today), even when action menus
and history fibers are infinite. An infinite player index would need a
separate countable-product or measure construction; PMF alone does not provide
the joint law. Unused information states still need inhabited legal menus
for total policies, just as in D61.

Canonical `BehavioralPolicy i info` and history beliefs should range over
`PMF (Choice i info)` and `PMF (InformationHistory i site.1)` respectively.
`InformationSite` keeps the fiber inhabited; antichain remains a substantive
premise, including for infinite fibers. A full-support local PMF means every
legal choice has strictly positive mass; it can exist on a countable infinite
menu, but not an uncountable menu (a PMF has at most countable support).
Nonemptiness of a menu supplies a Dirac policy, not a full-support policy.
Likewise, a chance edge with zero mass remains unreachable under player
trembles, so full mixing alone never implies Bayes at every syntactically
possible information site.

For an infinite information fiber, define reach weights in `ENNReal` and
`informationMass = ∑' h, reachWeight h`. Before normalizing, prove this is the
mass of a disjoint first-arrival event, hence at most one; the antichain
premise prevents counting nested histories twice. Require positive mass and
prove the weighted sum equals that mass. Then construct the normalized PMF
on the *fiber subtype* and prove pointwise Bayes. Avoid `toReal` of a possibly
infinite `ENNReal` denominator and avoid a zero-mass fallback that is mistaken
for Bayes. The current finite `informationMass`, `bayesBelief`, and
`IsBayesConsistent` are the template (`Protocol/BehavioralAssessment.lean`),
while v1's `AssessmentForm.infoMass` is only a schema: its unrestricted `tsum`
of history probabilities does not establish antichain event mass.

Continuation rationality should compare the assessment strategy with **all**
whole behavioral-policy replacements for the deviating player, via canonical
`Profile.update`, while other players and the information-site belief remain
fixed. Restricting to the current local action requires a proved one-shot
deviation principle; `BehavioralAssessment.IsSequentiallyRationalAt` already
uses the whole policy. For an infinite menu, finite-simplex arguments and
uniform trembles do not apply. Sequential consistency may still be defined
by pointwise PMF convergence, but such convergence of probabilities is not
sufficient on its own to pass an unbounded payoff through expectation.
Limit theorems need bounded payoff, uniform integrability, or another explicit
continuity certificate. In countable spaces, pointwise convergence of PMF
weights plus total mass one yields tightness/total variation convergence, but
the proof belongs in the analytic bridge.

A fuel-indexed continuation law is well-defined without termination, but it
is a truncated game. For terminal-payoff semantics prove a bound certificate:
every history in the support after `bound` steps is terminal, for every profile
and deviation under discussion. Then prove `runFrom (bound + extra) =
runFrom bound` and expected-payoff independence of the chosen certified bound.
The finite runner already has these lemmas (`Information.lean`); D61's
`SequentialExistenceBoundaryTest` refutes an equilibrium claim at an arbitrary
rolling fuel. A mere finite state type or almost-sure termination gives no
uniform finite bound. Almost-sure stopping with an infinite horizon would need
a separate stopping/path-measure semantics and integrability proof.

Implementation evidence added in EXP-125: well-founded play supplies a terminal
PMF directly by support-dependent recursion, without requiring a uniform finite
horizon. Its equality with any stopped bounded runner is a law theorem; real
payoff evaluation then carries its own integrability proof. One-shot comparison
derives integration of supported continuations from the compared root law.
This covers well-founded termination; it does not identify almost-sure stopping
in a potentially infinite play tree with well-foundedness.

## What v1 offers, and what it does not

The `v1-final` tag contains `Concepts/Mixed/SequentialAssessment.lean`,
`Languages/EFG/Sequential.lean`, `Math/PMFIter.lean`, and PMF product/conditioning
lemmas. It demonstrates PMF behavioral strategies, PMF history beliefs,
`ENNReal` reach weights, pointwise convergence, and PMF continuation bind.
Those are valuable proof ideas. Its `AssessmentForm` owns fresh strategy and
outcome fields instead of the present `GameSignature`, and EFG
`continuationTree` selects the root for invalid histories; the current
history subtype should make that fallback unnecessary. Its EU specialization
calls `expect` without an integrability certificate, so it cannot be imported
as a sound general real-valued payoff interface. Its history-mass sum also
needs the current antichain argument. Inspect old proofs as ingredients, then
reprove the critical runner/Bayes/utility bridges on canonical types.

Finite sequential-equilibrium **existence** is a separate compactness and
fixed-point theorem, not part of the definition. D61 and
`Analysis/Protocol/SequentialExistence.lean` use finite simplices, positive
uniform perturbations, perfect recall, finite complete histories, and a
certified terminal horizon. General PMF semantics permits infinite-support
laws, but supplies neither compact infinite policy spaces nor a sequential
equilibrium existence theorem. Preserve the finite theorem and only add an
infinite-case theorem after its own topology, tightness/compactness, payoff
continuity, and deviation-limit hypotheses are proved.

## Minimum hostile validation before promotion

1. **Static value and equilibrium:** a geometric PMF on `Nat` with a bounded
   nonconstant reward, plus an unbounded reward whose absolute weighted sum
   diverges. Prove the first EU and finite-form preservation, and ensure the
   second cannot enter unrestricted Nash through a hidden zero value.
2. **Dependent protocol run:** one finite player chooses among countably many
   legal actions with positive mass, followed by a countably supported chance
   transition; run from a typed history, prove support/reach and finite
   projection. Kill the design if dependent continuation needs user-visible
   casts or loses the legal-history invariant.
3. **Infinite Bayes fiber:** an antichain of countably many histories at varying
   depths with positive total mass and a nested-history counterexample.
   Normalize the former and show the latter's naive reach sum double counts.
   Kill the proposed Bayes API if it normalizes without antichain/event proof.
4. **Continuation and fuel:** an off-path information set with two viable
   whole-policy deviations and delayed terminal reward. Prove full-deviation
   quantification and bound independence; exhibit a rolling-fuel disagreement.
5. **Analysis boundary:** pointwise fully mixed approximation on a countably
   infinite menu; check existence of a full-support reference PMF, belief
   convergence, and bounded-EU limit. Keep simplex/compactness existence
   isolated. Kill any claim that nonempty menus alone provide full support or
   that pointwise limits preserve unbounded expected utility.

The currently compiled pilot covers geometric full support, countable
conditioning, bounded bind/Fubini, and a nonsummable control. It is evidence
for probability primitives, not approval for end-to-end cutover. Each further
spike should reserve an EXP entry and record its Lean artifact, commands, and
outcome. The decision record should compare the in-place PMF migration with
the current finite implementation using the hostile slices above. Promotion
requires the canonical equilibrium and runner semantics to compile
warning-free, the finite-specialization bridges to hold, and no permanent
parallel concept owners.
