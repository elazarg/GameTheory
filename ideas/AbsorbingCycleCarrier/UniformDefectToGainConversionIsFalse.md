# The uniform defect-to-gain conversion is false

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `WRONG` for the uniform conversion; `OPEN` for what replaces it |
| Objective priority | `P0` |
| Last audited | 2026-08-04, `67ad767` |
| Central live claim | Relaxing exact complementarity to a defect `ε` does **not** produce a uniform carrier: for a *fixed* relaxed cycle the resulting deviation gain is quantitatively bounded in `ε`, but there is **no** constant `K` for which every relaxed cycle of a weight satisfies `gain ≤ K · ε`. |
| Next discriminant | Exhibit the family realizing `gain / ε → ∞` explicitly and read off what the blow-up is a function of — period, deleted survival product, or coordinate isolation. That fixes which weaker, non-uniform conversion could still carry the mass-path limit. |
| Production destination | none yet |
| Supersedes / superseded by | none; answers the conversion question left open by [`FiniteCyclesAreRefutedTheCarrierIsAMassPath.md`](FiniteCyclesAreRefutedTheCarrierIsAMassPath.md) |

## Provenance and seal caveat, load-bearing

Every claim below comes from **an independent solver's answer**. It has **not**
been audited in this repository, and none of it is formalized. The ledger marks
each such row `M [reported]`: the source presents it as rigorous mathematics,
and this repository has checked neither the derivations nor the arithmetic. The
marker is not decoration — `C2` is a negative result now being used to
redirect the group's gate, which is exactly the situation in which an
unverified `M` is most expensive to be wrong about.

Seal legend used here, beyond [`../README.md`](../README.md): `[reported]` means
supplied by an external worker and not checked here; `[verified]` means checked
by hand inside this repository.

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| C1 | For a **fixed** relaxed cycle with complementarity defect `ε`, the deviation gain it permits admits a quantitative bound in terms of `ε` | `PROVED` | `M [reported]` | one cycle at a time | the only surviving half of the conversion |
| C2 | There is **no** uniform constant `K` with `gain ≤ K · ε` across the relaxed cycles of a weight | `PROVED` | `M [reported]` | across cycles, hence across periods | kills the conversion; makes it this group's gate |
| C3 | The two-coordinate weight `r({1}) = (1, -1)`, `r({2}) = (1, -1)`, `r({1,2}) = (0, 1)` *does* admit relaxed admissible cycles, via an explicit two-phase cycle with exact gains | `PROVED` | `M [reported]` | that weight only | shows relaxed objects are not the scarce thing |
| C4 | That existence holds for a reason **specific to that weight**, visible only after computing the cyclic deviation fixed point — not by any general mechanism | `PROVED` | `M [reported]` | that weight only | forbids reading `C3` as a producer |
| C5 | For that weight the dependence on the accuracy is **essential**: it has approximate solutions at every accuracy and **no exact one** | `PROVED` | `M [reported]` | that weight only | explains why relaxation was attempted at all |
| C6 | Eventual periodicity imposes no additional restriction once arbitrarily small gain is allowed | `PROVED` | `M [reported]` | strategy shape, that weight's setting | removes a hoped-for structural fence |
| C7 | Eventually all-zero tails suffice up to arbitrary slack | `PROVED` | `M [reported]` | same | removes a second hoped-for fence |

`C5` is consistent with what is already machine-adjacent in this repository:
the docstring of `quittingGame_exists_uniformEquilibriumPayoff` in
`GameTheory/Concepts/Stochastic/QuittingConjecture.lean` records, for exactly
this weight, that every absorbing complementary cycle has coordinate `1` silent
at every phase, so the deleted survival product at coordinate `2` is `1`, and
since `r_2({2}) = -1 < 0` the mismatch there is `1` and no cycle is admissible.
That is the "no exact one" half of `C5`, independently arrived at. The
"approximate at every accuracy" half is new and is the reported part.

## Why this is now the gate

The conversion was the bridge that **both** live routes out of the finite-cycle
refutation were leaning on.

- The **relaxation route** says: exact absorbing complementary cycles do not
  exist in general, but defect-`ε` ones do; convert defect into gain and the
  carrier survives in approximate form.
- The **mass-path route** says: take the limit of the defect-vanishing family,
  land on a continuous mass-parametrized absorption path, and read the target
  off the limit.

Both need `gain ≤ K · ε` with `K` not depending on which member of the family
is used — the first to get an `ε`-equilibrium at each accuracy, the second to
know that the limit of vanishing defects is a limit of vanishing gains. `C2`
says that inference is unavailable.

The consequence for project control is a change of target, not a retreat.
Existence of relaxed objects is **not** the obstruction: `C3` exhibits them,
and [`FiniteCyclesAreRefutedTheCarrierIsAMassPath.md`](FiniteCyclesAreRefutedTheCarrierIsAMassPath.md)
exhibits a whole period-`3m` family with defect of order `1/m`. What is
obstructed is the **conversion**. Any repair must therefore be a statement
about how gain degrades along a family, not another existence theorem.

## What the two-coordinate weight does and does not show

`C3` is a positive result and is easy to over-read. Read together with `C4` it
says: the relaxed cycles for that weight exist because of a coincidence in its
cyclic deviation fixed point, discovered by computing it, and no general
argument was found that would transport the construction to another weight. So
`C3` is a witness against "relaxation is empty" and **not** a producer.

`C5` is the sharper statement: the family of relaxed solutions for this weight
degenerates as the accuracy tends to zero, since its limit — an exact solution
— does not exist. Any conversion that survived `C2` would have to tolerate
precisely that degeneration.

`C6` and `C7` close off two structural fences that would have been convenient:
requiring the deviating behaviour to be eventually periodic buys nothing once
arbitrarily small gain is allowed, and eventually all-zero tails already
achieve arbitrary slack. Neither is a restriction that can be imposed to
recover uniformity.

## Ambiguities in the supplied statement, not resolved here

These are recorded rather than silently decided:

- **The constant in `C1` was not supplied.** The claim as received asserts that
  a quantitative bound exists for a fixed cycle; its exact form, and what it
  depends on besides `ε`, is not stated here because it was not stated to us.
  Whatever it is, it must blow up along some family, by `C2`.
- **"Relaxed admissible cycle" is read as follows**: complementarity holds only
  up to a defect `ε`, and admissibility is asked in the corresponding
  approximate sense — small deviation gain — rather than as exact zero mismatch.
  This reading is forced by the terminology fence below, but it is a reading.
- **"Exact gains" in `C3` is read** as: the two-phase cycle's deviation gains
  were computed in closed form rather than merely bounded.
- **The quantifier order in `C2`** is read as: for each weight, no `K` works
  uniformly over that weight's relaxed cycles. A weaker reading — no single `K`
  works uniformly over *all weights* — would be a much cheaper claim and would
  not have the stated consequence. If the source meant the weaker one, the gate
  argument above is overstated and this file must be corrected.

## Falsifiers and wrong turns

- **The direct falsifier.** Exhibit a constant `K`, depending only on the
  weight (or only on the number of coordinates), together with a proof that
  every relaxed admissible cycle of defect `ε` permits deviation gain at most
  `K · ε`. `C2` then dies and the relaxation route reopens as originally hoped.
  This is the single test worth running against the reported answer.
- **The cheap falsifier for the provenance.** Re-derive `C1` and `C2` here. All
  seven rows are `[reported]`; a single arithmetic slip in the family that
  realizes the blow-up would restore the conversion.
- **Terminology fence — do not confuse the complementarity defect with the
  mismatch.** The mismatch is defined only *after* exact complementarity: it is
  the anchored deviation fixed point minus the cycle value, and the anchored
  fixed point argument of
  [`MismatchVanishesExceptOnIsolatedNegativeCoordinates.md`](MismatchVanishesExceptOnIsolatedNegativeCoordinates.md)
  consumes complementarity *at every phase*. A relaxed cycle has no mismatch to
  speak of. A statement of the form "cycles whose mismatch tends to zero" is a
  category error, and a proof that quietly substitutes mismatch for defect
  proves nothing about this claim.
- **Do not read `C3` as reopening the carrier for that weight.** The weight has
  no exact admissible cycle (`C5`, and independently the
  `QuittingConjecture.lean` docstring). Its uniform-equilibrium payoff exists
  for external, two-player reasons; that equilibrium lies outside the cycle
  carrier.
- **Do not use `C6`/`C7` as positive construction principles.** They say
  restrictions *cost nothing*, i.e. they are non-fences. They do not say that
  eventually periodic or eventually silent profiles are where the solution
  lives.

## Production map

```text
external solver's answer  ->  [MISSING: internal audit]  ->  no production surface
```

Nothing here is formalized and nothing should be until the audit lands. The
adjacent production facts, for orientation:

- the sound half of the carrier —
  `exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle` in
  `GameTheory/Concepts/Stochastic/QuittingZeroSoloDisjunct.lean` — consumes an
  **exact** admissible absorbing cycle and is untouched by anything here;
- the open premise `quitting_zeroSolo_or_admissibleCycle` in
  `GameTheory/Concepts/Stochastic/QuittingConjecture.lean` is the completeness
  statement that the relaxation route was trying to reach.

Missing arrows, in order of value: (1) audit of `C2`; (2) an explicit named
family realizing `gain / ε → ∞`, which is what a Lean regression would need;
(3) a candidate weaker conversion with its own hypotheses.

## Exit conditions

- `MINED` when a weaker, non-uniform conversion is stated with its hypotheses
  and either proved or refuted, and the mass-path route is told which of the
  two it may use.
- Claim `C2` becomes `WRONG` if a uniform `K` is exhibited; the file then
  survives as the regression recording why the question was asked.
- `BLOCKED` if the internal audit cannot be completed without the source's
  unstated construction, in which case the prerequisite is the family behind
  `C2`.
