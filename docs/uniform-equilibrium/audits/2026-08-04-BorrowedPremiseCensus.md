# Audit, 2026-08-04 — borrowed-premise census

> **Standing.** Dated audit record. Sweep of `docs/uniform-equilibrium/`,
> `ideas/`, and Lean docstrings under `GameTheory/Concepts/Stochastic/` for
> every place an external result is consumed as a premise. ~20 distinct results
> consumed. The finding is not bad records — the literature wing is unusually
> disciplined — but **use sites that do not honour them**.

## The headline

**No Lean theorem's meaning depends on an external result.** The separation is
clean and deliberate: every source-named declaration proves a statement about a
concrete internally-defined object, no external result appears as an axiom,
hypothesis, or `opaque` stand-in, and `PuiseuxDiscountedValueSelection`
correctly makes Bewley–Kohlberg an explicit *input structure* rather than a
borrowed conclusion. The exposure is entirely in the prose layer.

## Load-bearing and not primary-verified, ranked by damage-if-false

**1. Solan 1999, *Three-Player Absorbing Games*, MOR 24(3):669–698.** The
largest single exposure. It is what settles `n ≤ 3`, and it is
`SECONDARY_VERIFIED` with the primary text unread. Consumers: the LCP group's
C1 (`P0`); `InvertedCounterexampleSearch`'s K1, which that file itself calls
"the constraint doing the most work in cutting the dimension of the search";
the non-vacuity argument of the case-2 carrier refutation; the `Q̄` record's
scope warning. **At every use site it is a bare "Solan (1999)" or has no
citation at all** — including `TheGluingStepIsOnlyARemark.md`'s "the base of
the induction is external and solid". *Second, independent exposure on the same
citation:* the published conclusion is **undiscounted**; the **uniform** reading
is sourced separately from Munk–Solan arXiv:2001.03094, recorded honestly at
`20-nonzero-sum-equilibrium.md:130-133` but flattened to "settled" downstream.
Under the repository's own terminology table, uniform is strictly stronger
except in positive recursive absorbing games — which quitting games with
negative payoffs are not. **Partly acted on**: the LCP README now cites it in
full and names the undiscounted/uniform gap.

**2. AGKRS Theorem 4.15's converse, as used by LCP C1.** Not unverified —
*fenced, twice*, and the fence was not honoured at a `P0` use site. Definition
4.13's endpoint convention is recorded as defective in
`20-nonzero-sum-equilibrium.md:195-230` and
`SourceCorrections-QuittingAbsorptionPaths.md`, both saying the theorem must
not be used as a literal path/nonexistence equivalence until a repaired bridge
is proved. **Acted on**: the gate is now stated in the LCP README and C1 is
marked conditional.

**3. AGKRS Theorem 3.5 versus Solan–Vieille Prop. 2.4/2.6.** The repository
holds a machine-checked two-player regression against a statement one of its
own records prints as a clean import. The 2001 source proves a **disjunction**
(globally approximately optimal **or** a stationary approximate equilibrium
exists); Theorem 3.5 states the first disjunct alone. **Acted on**: fenced in
the `Q̄` record, with the reconciliation stated as owed. The likeliest loose
joint is the mapping from the regression's profile to Definition 4.13 verbatim,
not an error in a refereed theorem.

**4. Solan–Solan 2020 published numbering.** `PRIMARY_FULLTEXT` on the
preprint only; the scope corrections are keyed to preprint numbers (2.6, 2.10,
2.11). If MOR renumbered, every downstream discharge obligation points at the
wrong result. Low probability, mechanical to check. Downstream *does* honour
the recorded scope correction — the LCP README says "stationary approximate",
links the record, and forbids the uniform upgrade in its falsifier row.

**5. Solan–Vieille 2001, Prop. 2.13.** The tree's most-quoted proposition
number, cited ~15 times as "Solan–Vieille (2001), Proposition 2.13" with no
title or journal, **and there is no wing record for Solan–Vieille 2001 at
all**. Worse, the verified text is the 1998 Northwestern DP 1227 working paper,
and `40-open-status.md` warns numbering could have shifted in copy-editing — so
a proposition *number* is cited against a preprint. **Damage is documentary
only**: the Lean is genuinely independent
(`quittingGame_hasUniformDeviationUpperApproximation` discharges the
quitting-specific instance internally), so Prop 2.13 is inspiration, not import.
*Stale*: `SourceCorrections-QuittingAbsorptionPaths.md:133-137` still says "the
quitting-specific proof remains to be landed". It has landed.

**6. Solan 2003 IGTR volume/year.** IGTR volume 3 is 2001, not 2003 — though
AGKRS's own reference list gives "3, 291–300 (2003)". Verify the pair. Damage
low; the mathematics is `PRIMARY_FULLTEXT` on the preprint.

**7. `InvertedCounterexampleSearch`'s K1 (`n ≥ 4`).** Self-flagged as
"attributed to the literature; the file does not name the source theorem",
while also being the constraint doing the most search-space pruning. Almost
certainly Solan 1999; pinning it costs one edit and collapses it into row 1.

## Uncited external premises

- `PositivePlateauBoundaryClosure/BackgroundAndDerivations.md:29` — "**The
  literature theorem** has exact hypotheses", source unnamed.
- `QuittingGameConjecture/BackgroundAndDerivations.md` — "the known two- and
  three-player terminal results", "the FTV cyclic example demonstrates". This
  file has the heaviest citation load in the tree and **zero** links to the
  literature wing.
- FTV 1997's no-stationary-`ε`-equilibrium is asserted with no citation at
  `AbsorbingCycleCarrier/VanishingAbsorptionIsTheOnlyRemainingCase.md:71`,
  `SoloQuitterCycleExistsWithoutJoinIncentive.md:84`, and
  `FTVCyclicAdmissibleCycle.lean:43-45`. The reference doc handles it
  exemplarily — it caught that the abstract's universal "(ε > 0)" reading is
  false, since payoffs lie in `[0,3]` so every stationary profile is trivially a
  `3`-equilibrium, and `LEAN-P2-1` is `BLOCKED` pending the exact quantifier.
  The use sites do not carry that.
- **Governance gap.** `ideas/README.md:79-81` requires attribution to route
  through the literature wing. Only **4 of ~20** non-wing files that consume an
  external result actually link a record.

## Handled well, recorded for the pattern

`Solan–Vieille 2002 GEB` (autonomous correlation) — risk (d), using a richer
solution concept as if it gave ordinary Nash, is the exact hazard and is fenced
hard ("no de-correlation compiler has been proved"). `Simon 2012` — risk (c) is
caught explicitly, with "**would establish**" flagged as the paper's own word
and the Solan–Solan reading-trap noted. `AGKRS Remark 5.5(1)` (the gluing step)
— labelled "a remark, not a numbered result, and carries no proof", sealed `I`,
and posed as something to *prove* rather than consume. `Ummels Thm 4.13` —
explicitly "source-conditional internal result, not a new primary literature
fact".

One mis-pairing: `QuittingGameConjecture/BackgroundAndDerivations.md:488-496`
footnotes the Solan–Solan **sunspot** claim to the **LCP** paper.

## Docstrings asserting external content the declaration does not prove

Four, only the first a genuine defect.

- `FTVCyclicAdmissibleCycle.lean:43-45` — "it has no stationary `ε`-equilibrium
  for small `ε`", stated flatly, unformalized FTV 1997. Mitigated by the
  headline theorem's own docstring at `:479-481`, which disclaims it. Fix: move
  the disclaimer up or attribute in place.
- `QuittingConjecture.lean` — "a uniform-equilibrium payoff does exist for it
  externally". Labelled "externally"; premise primary-verified; low damage.
- `QuittingUnboundedInverseIterate.lean` — a literature-audit judgement about
  Solan 2003's proof, strongly mitigated by the paragraph that draws the
  boundary explicitly.
- `SingleControllerPrimalExistence.lean:197-204` — a "more generally" remark
  that the same docstring says the formal proof does not use.

## Same hazard, internal source

`AbsorbingCycleCarrier/UniformDefectToGainConversionIsFalse.md:18-24` seals
seven rows `M [reported]` from "an independent solver's answer ... not
audited", while explicitly "being used to redirect the group's gate". Not
literature, identical exposure.
