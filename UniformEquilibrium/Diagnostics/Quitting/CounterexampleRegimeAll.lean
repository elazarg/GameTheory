/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitLimit
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitSelfLoop
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAggregatePrefixConsumption
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAggregatePrefixResidualRegression
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBoundaryProvenanceAlternative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCapCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCoalitionLocks
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtConservation
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceObstructionCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceDynamicAlternative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeKilledCapacityPotential
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeKilledTailPotential
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOneStageObstructionCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeExactCycleStrata
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFiniteInstability
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFloorViolationBudget
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketDefect
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketEnergy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSupport
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSurplus
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneAttachmentRepair
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneTangentReadout
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeReachableCarryTelescope
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeNonpositiveFloorTerminalCapRegression
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalIncomingPathAlternative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeQuantitative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodicWindows
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSearchConsequences
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSeam
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTailBridge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentAnchoredProjectiveLCP
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentMixingCompatibility
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacketEnergy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGauge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGaugeDefect
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGaugeScalarClosure
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGaugeSecondJet
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentRegularArcLift
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentSupportTransversality
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerExactRoot
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerPacketEdge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerPacketDichotomy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerApproxPunishment
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerSupport
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentSupportLiftFarkas
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeViolationCollapse
import UniformEquilibrium.Diagnostics.Quitting.FourPlayerSingletonBlocker
import UniformEquilibrium.Diagnostics.Quitting.MinimalFinCounterexample
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.AbsorptionPath.FiniteWindowRefusalReweighting
import UniformEquilibrium.Quitting.AbsorptionPath.FlowCostateObstructionAdapter
import UniformEquilibrium.Quitting.AbsorptionPath.SurvivalWeightedObstructionAdapter
import UniformEquilibrium.Quitting.Classification.SingletonPacketDefectAlgebra
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryLimitGeometry
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas
import UniformEquilibrium.Quitting.Cycles.PeriodicNormalizedSeam
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapChargedAnchorCounterexample
import UniformEquilibrium.Quitting.Debt.Dynamic.PeriodicDebtHolonomy
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorCapSplice
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Quitting.Terminal.TailCompression.SummableTailBestResponse

/-!
# Quitting counterexample regime

This is the public umbrella for the combined counterexample normal form, its
canonical prefix-charge capacity, quantitative exact-D restrictions,
search-facing recurrence tests, the exact bridge from optimized exact-D tails
to punishment-floor prefixes, the membership-toggle and
stationary-cap instability families, support dynamics of the forced packet,
canonical minimal finite counterexamples, emptiness at small player types,
orbit value limits, quantitative floor-violation budgets, the collapse that
makes the extracted optimized tail's absorption unconditionally summable,
its positive-debt all-Continue self-loop limit, and exact evaluation of
periodically restarted tail windows.  The optimized tail additionally carries
exact finite and infinite debt conservation, a logarithmic owner-clock bound,
the positive phantom-plateau theorem, closed augmented-cap membership in the
global floor carrier, and a canonical periodic-window family whose player and
refusal/phase obstruction stabilize on an infinite set.  The forced packet's
noncomplementarity has one uniform compact refusal margin across all normalized
packets of the fixed table.  Stable pure quitting coalitions independently
generate unbounded canonical prefix charge, linking the sure-exit and capacity
screens.  The umbrella also exports the augmented-cap splice
interface and the finite regressions delimiting singleton complementarity and
cap-only arguments.

Every unaugmented value on the optimized tail already dominates the behavioral
punishment floor, so every finite chronological tail segment reverses to a
legal exact floor prefix with the same charge.  The tail is also uniformly
ballistic in absorption time: after one date, every positive-absorption window
has endpoint distance at least one fixed positive multiple of its absorbed
mass.  Thus no late window closes at little-o of charge scale.  This does not
produce recurrence; finite total charge permits a bounded ballistic approach
to the limiting all-Continue state.  The signed normalization is retained
more precisely: either the tail is eventually literally all-Continue, or
positive one-stage windows extract a nonzero charge-tangent packet from the
same roots.  Its remaining finite sign dispatch is a negative coordinate or,
after excluding all negative coordinates, a positive active-owner coordinate.
The corresponding phase-repair and support-enlargement consumers remain open.
On the active-positive branch, after excluding every negative tangent
coordinate, the same tail-derived packet is canonically a normalized
singleton-source packet.  Its weighted surplus is its mass-weighted tangent,
so it contains a distinct supported pair with positive reciprocal singleton
effect.  For any supplied product root and intended interior support, the
remaining collision-aware continuation lift is now one explicit finite affine
system: its physical branch decodes an exact Nash--Bellman edge, and its dual
branch supplies Farkas multipliers certifying that this root has no lift.
Actual collision and higher Möbius terms are retained in the rows.  Choosing
the simultaneous quit probabilities remains a genuinely multiaffine search;
the singleton-level handoff does not itself produce that root or contradict
all of its pointwise certificates.
The same packet also embeds canonically into the existing anchored projective
singleton LCP at every positive cemetery weight: singleton weights are a
rescaling of packet mass and the anchor is boundary minus the corresponding
rescaled tangent.  An active-positive coordinate becomes a strictly negative
projective LCP direction.  What remains absent in arbitrary player count is
the resolved-chart feasibility/arc lift turning that anchored first-event
datum into actual product-root Nash--Bellman rates; the three-player analytic
compiler does not supply such a generic constructor.
At the first blow-up, the active mixing row has a simpler exact form.  On a
positive-mass owner it is the mass-weighted pair-join effect
`sum_{j≠i} mass_j * (r_i({i,j})-r_i({i}))`.  Either every active row
vanishes, or a supported outsider has the same strict sign and supplies a
finite pair-join pivot.  In the compatible active-positive branch, collision
energy must cancel the positive singleton energy exactly, forcing a supported
pair with negative reciprocal collision increment.  These are finite
first-order directions; neither the canonical sign separator nor the pair
it selects is yet a feasible analytic arc or a strategic Farkas certificate.
On the compatible branch, the first radial blow-up supplies the exact
polynomial interface.  Hazards are `t*leading` and continuation is
`boundary+t*drift`; exact polynomial residuals retain every coalition and
factor the physical Bellman and mixing equations by `t`.  The packet solves
the exceptional-divisor Bellman rows, and compatibility solves its active
mixing rows.  If the blow-up derivative is surjective and its kernel has a
positive radial direction, the existing analytic implicit-function theorem
produces a positive radial equality arc.  With the strict physical cell signs,
each nonzero point decodes to an exact Nash--Bellman root.  The literal
ungauged compatible chart cannot meet those two regularity hypotheses:
compatibility makes every exceptional-divisor base point lie on one
projective scale line, whose nonzero tangent has radial coordinate zero; the
source has exactly one dimension more than the equality rows, so
surjectivity makes that line the whole kernel.  A projective gauge or a
radial-parameter implicit-function theorem is therefore mandatory.  On a
three-owner support, one explicit radial minor exactly separates the
transverse-surjective/no-outward branch from the singular/outward branch and
the latter supplies a finite left costate.  None of these statements creates
a global return.
The canonical projective gauge `sum leading = 1` now removes exactly the
scale line, with an injective affine chart and an exact equality between its
full-residual zero image and the ungauged zero set on that hyperplane.  The
gauged full system is square, so full derivative surjectivity would isolate
the base rather than produce an arc.  A nonvacuous regular theorem therefore
uses a codimension-one reduced residual together with an explicit local
recovery equivalence to the full equations.  Surjectivity and an outward
kernel direction for that reduced system produce an analytic arc of literal
full zeros and feed the existing Nash--Bellman decoder.  Constructing the
reduced equation/recovery pair remains the exact analytic gate.  The natural
choice of simply deleting one active mixing row fails in general.  Its exact
missing scalar is `Bellman_i + (1-t*a_i)*Mixing_i`; after Bellman closure and
nonzero own survival, this vanishes exactly when the omitted row does.  A
normalized regression through the packet keeps every Bellman row and all
retained mixing rows zero while the omitted row varies as `s*(Jv)_i`.
Compatibility kills only the packet mass direction, not arbitrary zero-sum
gauge variations, so no local recovery theorem follows from it.
Nor does packet sign/energy force the missing scalar to cross zero.  For a
three-owner support, a nonzero radial minor makes the omitted defect have a
nonzero derivative and hence one fixed one-sided sign along any supplied
reduced branch.  If the minor vanishes, the explicit outward direction kills
all selected first-order rows and leaves an honest higher-order closure
problem.  The finite alternative is transverse sign obstruction versus
higher-order singularity, not an implicit first-order repair.
For the three-owner zero-minor branch, the first nontrivial omitted-row
calculation is now exact.  Along the sum-one Bellman-forced affine outward
path, the defect is `s^2*(Q+s*C)`.  Nonzero quadratic coefficient gives an
eventual fixed sign; if it vanishes, a nonzero cubic coefficient gives a
fixed sign at every positive scale; if both vanish, this scalar is identically
zero along the path.  The path is not asserted to solve the retained
nonlinear mixing rows, so this classifies the second jet without constructing
an arc or return.
For two declared active owners, Bellman elimination makes the reduced support
Jacobian exactly `[[0,D₁₂],[D₂₁,0]]`, where
`Dᵢⱼ=r_i({i,j})-r_i({i})`.  A signed directed pivot is regular precisely
when its reciprocal effect is nonzero, and the outward leading variation is
explicit.  In contrast, if those two owners are the entire positive support
and both packet rows are compatible, positivity forces `D₁₂=D₂₁=0`:
the whole reduced Jacobian vanishes.  This singularity integrates exactly
rather than requiring a second jet.  For arbitrary hazards below one, the
Bellman-eliminated continuation has active coordinates
`w_i=(z_i-p_j*r_i({j}))/(1-p_j)` and symmetrically; both active gains vanish,
because a two-owner root has no triple or higher coalition.  If the inactive
gain signs and continuation floor/upper-box bounds also hold, this packages
one exact Nash--Bellman edge.  Those gates, and any reachable return, lasso,
or cycle, remain separate.  Along the packet-selected ray
`p_i=t*mass_i`, positive subunit hazards and survival are automatic.  Active
continuation is exactly `boundary_i-t*tangent_i/(1-t*mass_j)`: nonnegative
tangent makes its upper bound automatic, strict floor slack is stable for
small `t`, and a tight floor with positive tangent fails at every positive
scale.  Strict outsider singleton slack also gives eventual outsider Nash
signs through an exact finite polynomial regression.  Tight outsider rows
and inactive continuation bounds remain independent finite gates.
Consequently either every sufficiently small positive scale supplies a
positive-charge exact edge, or some punishment boundary, inactive singleton
row, or upper-box coordinate is tight.  At an active positive-tangent
coordinate, equality with the punishment value blocks the ray at every
positive scale; it does not realize the min--max infimum.  A tight inactive
singleton row is exactly the finite outsider regression starting from zero.
The tight active punishment face is nevertheless asymptotically consumable
at any fixed tolerance.  Its exact floor deficit tends to zero with the
hazard scale, and approximate min--max supplies a player-specific
target-closed punishment tail below the exact-ray continuation plus the
chosen rationality error and tail slack.  A single stationary row working
for all errors would force actual attainment of the punishment infimum, so
the available tails necessarily depend on scale/tolerance and do not yet
form one common multi-player suffix or return.

Independently of that selected-tail geometry, reward-table closure gives a
robust finite-cycle restriction: a hypothetical counterexample has one
positive-radius reward neighborhood containing no punishment-admissible exact
cycle of any period.  For a fixed root cycle, a common own-set reward shift is
governed by an exact finite global feedback system.  On an absorbing cycle its
value correction is unique, its unit multipliers lie on probability scale,
and the system eliminates player by player.  This does not prove density of
solved-cycle strata or show that own-set shifts exhaust general reward-table
perturbations.

For proper-face arguments, the umbrella exports an original-coordinate
outsider-`Never` estimate.  If the outsider's live continuation is at most
`eta` below its solo reward and insider absorption is at most `delta` at every
date, every behavioral deviation gains at most `eta + 2*M*delta` over literal
`Never`.  The theorem does not derive either quantitative premise from a
restricted equilibrium.

The umbrella also exports the general summable-tail boundary geometry used by
the regime: an explicit remaining-charge bound on literal behavioral best
responses, simultaneous annotation convergence with an active-owner pinning
criterion, and the scalar phase/refusal algebra that separates underfunding
from punishment-floor failure.  None of these results identifies the forced
packet with a tail occupation or realizes an augmented cap as a suffix.
At the local dynamic-debt level, vanishing of the named diagonal seam is
exactly the criterion for the displayed root to lift to a Nash--Bellman edge
between augmented caps; the umbrella does not assert that this criterion holds
along the optimized tail.
Playerwise dynamic debt is also exported as an exact killed-potential
reference account.  An excessive account with the same initial value can
dissipate only by losing the corresponding surviving boundary: boundary
dominance is equivalent to zero total killed dissipation, forces every
positively reached local dissipation to vanish, and strict dissipation forces
strict boundary shortfall.  The counterexample
regime does not supply that boundary dominance, so this accounting theorem
does not erase the positive phantom plateau.
The canonical prefix-capacity potential nevertheless supplies a natural
account: remaining capacity is nonnegative, pays each chronological
absorption charge, and after singleton-cap scaling is killed-excessive for
the exact debt source.  Its initial mismatch with exact debt is explicit and
has no proved sign or vanishing property; shifting the account arithmetically
does not preserve excessivity automatically.
Product-root collision mass is at most `choose (card ι) 2` times squared
one-stage absorption.  The exported weighted-window concentration theorem has
a separate zero-absorption branch; its conditional singleton-mixture payoff
comparison applies when both absorption and singleton mass are positive.
On a supplied finite exact-debt window, a positive debt coordinate that returns
to its initial value forces every opponent to Continue throughout.  Two
distinct returning positive coordinates make the entire window all-Continue,
so an absorbing return can carry at most one such coordinate.
The forced packet's weighted surplus is a quadratic form depending only on the
symmetric reciprocal part of the singleton solo-effect matrix.  Consequently
every counterexample packet supports a pair with positive reciprocal solo
effect; if all reciprocal pair sums are nonpositive, the complementary-mixture
compiler supplies a uniform payoff.
Canonical source-typed finite windows now retain normalized singleton owner
occupation, collision mass, and full absorbing delivery.  Late collision
vanishes at the product-law rate, and positive limiting owner occupation pins
the annotation boundary directly.  Normalizing the singleton mixture by total
absorption gives a collision error bound without a positive singleton-mass
premise.  Refusal conditioning uses a different
deleted-player survival law; its normalized discrepancy is explicitly bounded
by the chronological reweighting error divided by a positive deleted-absorption
denominator.  No theorem here makes that ratio vanish for the canonical
windows.
Adjacent source windows also form exact survival-weighted obstruction blocks:
singleton and collision charge in the later window is killed by the earlier
joint-survival factor, while endpoint displacement is an unweighted
coboundary.  This makes normalized tangent composition explicit, but does not
yet supply a strategically feasible raw-current family or a compatible
co-state.
The same data is exported as a sparse two-grade raw flow.  Raw charge has
survival degree one, endpoint coboundary has degree zero, and arbitrary finite
co-states obey the exact adjoint pairing law across adjacent windows.  This
flow has an exact compact one-stage carrier: its source retains boxed exact
Nash--Bellman and dynamic-debt constraints together with the punishment floor
at both endpoints, every canonical tail edge belongs to it, and every finite
co-state support is attained.  Enriching this carrier by the playerwise
diagonal dynamic-debt source makes the previously missing debt price literal:
the negative coordinate selector exposes exactly the zero-source face, and
for an exact edge this face is equivalent to the corresponding augmented-cap
transport equation.  Consecutive source coordinates fold to current debt
minus survival-weighted terminal debt.  The theorem still does not force the
canonical tail into that face, prove recurrence there, or decode a
strategically realizable exit.
The exact dynamic alternative shows why: at every date the selected tail flow
is in the zero-source face now, is there at the next edge, or the canonical
killed-capacity account dissipates strictly.  The latter is exactly strict
growth of the survival-scaled debt/capacity boundary mismatch.  Face
recurrence follows if that mismatch is nonexpanding on positive-length
windows at arbitrarily late starts, but the current regime supplies only the
reverse weak inequality.  Thus the remaining premise is a concrete boundary
comparison, not compactness or co-state selection.
Projective provenance cannot silently provide that comparison: a moving zero
terminal boundary may escape every fixed coordinate and leave a positive
harmonic limit, even under exact finite killed recursions.  The two-ended
compactification retains a reverse ray but no bridge survival, while the
metrizable marked decoder jointly retains both anchors and repair state but
does not carry the canonical capacity potential.  On the actual optimized
tail the capacity account is antitone, its killed dissipations are summable,
and the one-step boundary-mismatch excess tends to zero.  This gives
asymptotic equality only; every finite excess may remain strictly positive.

Periodic attachment has a second, exact normalization fence.  For an
absorbing exact Nash--Bellman word, the finite-stop and refusal branches of
the literal periodic best-response envelope are controlled by endpoint drift
divided by the joint and opponent survival gaps.  Ordinary endpoint
convergence does not imply these normalized ratios vanish; on the optimized
counterexample tail the joint-absorption ratio is eventually bounded away
from zero in endpoint-distance scale.  In the refusal branch, positive debt
can survive precisely in this normalization, so a
tail-derived singleton packet and a phantom plateau need not contradict one
another even after occupation identification.  The isolated
opponent-survival-one branch remains the separately classified negative-solo
exception.
For a repeated one-root word these coefficients have an exact mass atlas.
Writing `A` for absorption, `mu` for the normalized singleton-owner mass,
`C` for joint survival, and `rho` for opponent survival gives
`rho-C=A*mu` and `1-rho=A*(1-mu)`.  The phase evaluator is
`-C*tangent-phaseSlack`; on `mu<1` the refusal evaluator is
`mu/(1-mu)*tangent-refusalSlack/(A*(1-mu))`.  At `mu=1` every opponent
continues surely and the refusal denominator is genuinely zero.  The
canonical extraction retains literal one-stage fuel and now packages actual
root-mass and endpoint-tangent convergence to the tail packet, with one fixed
signed coordinate.  Its single exact Nash--Bellman edge makes both displayed
slacks nonnegative.  The periodically repeated root remains a diagnostic
deviation; the source tail is not asserted to be periodic or attached to that
restart.
On the active-positive owner, full limiting mass is impossible.  The selected
roots eventually have proper positive owner mass, positive endpoint tangent,
and positive own Continue probability; exact root complementarity then makes
the refusal slack zero.  The diagnostic repeated-root refusal gain converges
to `mass/(1-mass)*tangent` and is eventually strictly positive.  This sharpens
the refusal branch quantitatively.  The exact attachment formula shows what
prevents an unconditional transfer: actual attached `Never` gain is the
periodic refusal gain plus the joint-survival tangent correction plus
opponent survival times the difference between actual suffix-`Never` payoff
and stationary refusal value.  The counterexample tail neither realizes its
far annotation as an honest suffix payoff nor controls this final boundary
defect.  If both facts are supplied, the diagnostic becomes an eventual
literal profitable deviation; they are not consequences of the present tail
asymptotics.
The terminal-gap lane remains co-realized even when that owner-specific
attachment fails.  Every positive finite prefix has behavioral-tail repair
value at least the regime gap, because the boundary value and all-behavior
envelope come from the same actual suffix.  Elementary tail compression
therefore returns, behind every selected one-root prefix, a sure-joint,
sure-solo, or `Never` cap whose terminal exploitability remains above half the
gap.  This is an unconditional terminal obstruction, not a recovery of the
active owner's deviation or of the stored Nash--Bellman annotation.
For the canonical aggregate minimizer, this co-realized repair floor is also
bounded above by the optimized aggregate exact-`D` objective.  Consequently
every cutoff has a marked aggregate anchor whose packet mass carries the
terminal gap with an explicit reward/cardinality constant.  The packet is not
yet a punishment-floor reachable predecessor.  A conditional consumption
theorem splits half the gap between the next-cutoff objective drop and one
legal predecessor charge once literal state attachment and the comparison
`capped exploitability ≤ objective drop + scaled charge` are supplied; neither
premise follows from tail compression alone.
Among the elementary caps, immediate `Never` has an exact zero-boundary
interpretation: its terminal exploitability is the calibrated path's maximum
dynamic debt.  The generic consumption inequality then reduces to the
concrete endpoint requirement that next-cutoff aggregate debt be paid by a
scaled legal predecessor charge.  For a literally attached reachable edge,
one-edge conservation gives the sharp bound
`residual ≤ jointContinue * oldDebt + |I| * M * charge`.  Thus the new
diagonal seam is charged automatically, but old debt that survives joint
Continue is a separate potential and must itself be charged before the
consumer closes.  A rational augmented-cap regression has positive carried
debt at an exact all-Continue Nash root with zero absorption, so no local
exact-Nash bound may erase this term; the regression does not assert
punishment-floor reachability.  A positive internal cutoff retains an arbitrary word,
while sure-joint and sure-solo caps introduce nonzero pure-exit boundaries;
those branches still need boundary reinsertion or an exact appended
Nash--Bellman chain.
Across a supplied coherent chronology of literally reachable predecessor
edges, the canonical remaining-capacity potential does amortize every new
diagonal seam.  Its scaled account is killed-excessive for aggregate debt,
and finite telescoping reduces all carried terms to one survival-weighted
far-end boundary comparison.  Neither reachability nor finite charge
capacity supplies that comparison, and the calibrated minimizers have not
yet been assembled into such a literal coherent reachable chronology.  A
literal reachable state must dominate the punishment floor coordinatewise,
which the zero-boundary aggregate-minimizer API does not establish; any
strict floor violation rules out the required identification.  At the other
end, a finitely killed window closes the telescope outright.  Otherwise the
only quantitative error is the exact survival-weighted far debt, so a
cofinal construction must make that remainder vanish or compare same-state
debt with remaining capacity.
When the punishment vector is coordinatewise nonpositive, every exact-`D`
point of every finite zero-boundary chain already dominates the floor.  The
reversed selected chain is therefore a literal path in the global
floor-admissible relation, starting from its own terminal zero-payoff state;
it becomes floor-anchor reachable if that one terminal state is reachable.
More importantly, the global admissible capacity potential telescopes debt
along each selected finite chain separately, so no nesting of minimizers
across cutoffs is needed.  The remaining hypothesis is still the same-state
terminal exact-debt cap being dominated by the terminal admissible capacity
account.  Nonpositive punishment does not prove that comparison.
The far datum is now explicit: terminal payoff is zero and terminal aggregate
debt is `sum_i max(0,r_i({i}))`.  If this cap vanishes, the telescope closes.
More generally, an admissible path ending at the terminal state reserves its
charge in terminal remaining capacity and closes the estimate when the
scaled incoming charge pays that cap.  The intrinsic reversed chain has the
opposite orientation and spends, rather than funds, terminal capacity.  A
two-player regression has nonpositive punishment values but positive
terminal cap, so `punishment ≤ 0` alone cannot erase the boundary; it is not
a counterexample-regime witness and does not falsify the full capacity
inequality.
The terminal funding search is now finite.  The admissible capacity potential
depends only on payoff, not on the stored root.  Whenever
`0 < terminalDebt < |I|*M`, a canonical one-owner hazard has exactly enough
absorption to fund the cap; frozen-root feasibility yields either a literal
incoming admissible edge and the carry conclusion, or explicit finite Farkas
multipliers for that root.  At saturation, every singleton cap equals `M`
and the obvious pure-singleton zero-target predecessor is Bellman-infeasible.
More complicated full-absorption roots remain the saturated residual.
-/
