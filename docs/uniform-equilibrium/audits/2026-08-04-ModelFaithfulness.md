# Audit, 2026-08-04 — is the ladder standing on the ground?

> **Standing.** Dated audit record, not a live ledger. The question asked was
> narrow: are the repository's definitions faithful to the standard objects, so
> that theorems proved about them mean what everyone assumes? Six checks, with
> file:line evidence. The verdicts below are the auditor's; where this program
> has since acted on one, the action is noted.
>
> **Read twice, independently.** A second pass reached the same verdict on all
> six points from its own reads. Treat the six as corroborated. Its three
> additions are at the end.

## Summary

**The ground is solid.** The payoff notion is the textbook one, the deviation
class is unrestricted, the never-terminate value is a semantic `0`, the
complementarity predicates are exactly right, and the landed bridges really do
build behavior profiles and verify the uniform condition — all axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only). The danger to the program
is not unsoundness. It is that the only landed carrier is provably
non-exhaustive, and that the fences preventing vacuity are per-theorem side
conditions rather than structure.

## 1. The payoff notion — `FAITHFUL`

`Uniform.lean:91-95`:

```lean
def IsUniformEquilibriumPayoff (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorProfile) (T₀ : ℕ), ∀ T, T₀ ≤ T →
    G.IsεHorizonNash s₀ T ε σ ∧
      ∀ who, |G.finiteAveragePayoff s₀ T σ who - v who| ≤ ε
```

Expanded: **∀ε>0 ∃σ ∃T₀ ∀T≥T₀ ∀i ∀dev**, with the payoff-proximity clause under
the same `∀T≥T₀`. That is Solan–Vieille Def. 2.1 / Mertens–Neyman verbatim —
not a finite-horizon surrogate, because `finiteAveragePayoff` (`Basic.lean:178`)
is the genuine `T`-stage Cesàro average and the uniformity in `T` is what makes
the notion uniform. No bridge lemma is needed because there is no weaker
internal notion; the sibling `HasUniformDeviationCapConstructor`
(`Uniform.lean:169`) is proved exactly equivalent at `Uniform.lean:181-199`.

Two harmless caveats: `StochasticGame.discount` is vestigial and unused
(`Basic.lean:22`; `quittingGame` sets it to `0`), and in `quittingGame` the
stage on which a set quits pays `0`, with `r S` arriving the next stage
(`QuittingGame.lean:53-57`). Under Cesàro averaging the one-stage delay is
invisible, and the repository *proves* the limit object matches
(`tendsto_finiteAveragePayoff_quittingGame`) rather than assuming it.

## 2. The strategy class — `FAITHFUL`

`BehaviorStrategy G i := (t : ℕ) → G.Hist t → PMF (G.Act i)` (`Basic.lean:72`),
with `Hist t` the full record of past states and joint actions plus the current
state. Arbitrary, history-dependent, perfect monitoring. Every link quantifies
over that full class with no restriction — `IsεHorizonNash` (`Uniform.lean:76`),
`IsεAsymptoticNash` (`Asymptotic.lean:43`), and critically
`HasUniformDeviationUpperApproximation`
(`TerminalToUniformDeviationApproximation.lean:48`). The one-shot `PMF Bool`
deviations of `IsεQuittingRootNash` live purely at the Bellman layer; the
passage to full behavior strategies is *exact* via
`quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue`
(`QuittingBehaviorPureTimeExtremality.lean:224`), legitimate because before
absorption a quitting game has exactly one public history.

## 3. The never-terminate payoff — `FAITHFUL WITH CAVEAT`

**It is a semantic constant `0`, and it is consistent.** This closes a question
raised by an external auditor earlier the same day and left open there.

- `quittingGame.stagePayoff` at the live state is `| none => 0`
  (`QuittingGame.lean:55`), hard-coded for every action.
- `quittingTerminalPayoff` (`QuittingAsymptotic.lean:198`) sums over absorbed
  mass; non-absorption contributes nothing, and
  `tendsto_finiteAveragePayoff_quittingGame` *proves* it is the Cesàro limit.
- `FTVCyclicMinimality.terminalReward allContinue = ![0,0,0]`
  (`FTVCyclicMinimality.lean:216`), and the docstring's claim that the value
  "is ignored by terminal sums" is **true, not merely asserted**:
  `terminalProfiles := Finset.univ.erase allContinue` (`:302`), so the sums at
  `:339` and `:344` literally exclude it. Independently, `ftvReward` reads it
  only through nonempty quitter sets. Both zero and dropped.

The caveat is that a third object also exists: the Bellman layer genuinely
carries a **free continuation vector**, giving `F_y(z)_i` with `z` a free
parameter (`QuittingRootContinuation.lean:242`,
`QuittingStationaryPayoff.lean:41`). What pins it to semantics is *absorption*,
not a terminal condition — see §6. No module sets a nonzero all-continue value
and then claims a semantic conclusion.

## 4. The complementarity predicates — `FAITHFUL`

`quittingRootSuccessorPayoff_eq_endpointMix`
(`QuittingRootSuccessorCertificate.lean:104`) proves the payoff *is*
`y_i·Quit_i + (1−y_i)·Continue_i`, the map `s ↦ s·Σ_i + (1−s)·Γ_i`. The `ε` in
`IsεQuittingRootEndpointNash` (`:119`) is on the correct side: pure-Quit regret
is `(1−y)·D`, pure-Continue regret is `−y·D`, so the two clauses say exactly
that no pure endpoint gains more than `ε`. This is not an eyeball check —
`isεQuittingRootEndpointNash_iff_isεQuittingRootNash` (`:130-233`) proves
equivalence with the full mixed-deviation condition for arbitrary `ε`.

## 5. The bridges — `FAITHFUL`, all three reach a strategy

None stops at a certificate about arrays of reals.

- `quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`
  (`QuittingZeroSoloDisjunct.lean:125`) constructs a real `BehaviorProfile` and
  proves it exactly terminal-Nash against all behavior deviations via an
  **iff** (`QuittingSimpleBranches.lean:326`), so the hypothesis is exactly the
  class where it works.
- `exists_uniformEquilibriumPayoff_of_admissible_quittingCyclicContinuationBlock`
  (`QuittingAdmissibleCycleTerminalEquilibrium.lean:558`): the combinatorial
  object becomes a strategy at `quittingCyclicContinuationBlockProfile` (`:474`).
  Two things are assumed there and **both are flagged in the module docstring**
  (`:53-64`), including that admissibility is not derivable from the block and
  a two-player counterexample showing so, marked "hand check, not formalized
  here". Honest.
- The real load-bearer under all three is
  `quittingGame_hasUniformDeviationUpperApproximation`
  (`QuittingTerminalUniformization.lean:75-198`) — a genuine proof of the
  one-sided uniform approximation, the quitting-specific content of
  Solan–Vieille Prop. 2.13, split on the sign of `r_i({i})`. Together with the
  full **iff** at `QuittingTerminalUniformPayoffSelection.lean:167`, the
  auditor calls this the strongest single asset in the repository.

Non-vacuity is demonstrated, not argued: `FTVCyclicAdmissibleCycle.lean:487`
derives axiom-clean that the FTV table has uniform equilibrium payoff `(1,2,1)`.

## 6. Vacuity — `FAITHFUL`; the fence exists and its necessity is machine-checked

- **The absorption fence is present.** `IsQuittingCyclicContinuationBlock`
  (`QuittingCyclePinnedDebt.lean:152`) carries `∃ stage, 0 < absorptionMass` as
  its third clause. Its necessity is *proved*, not asserted:
  `quittingAllContinueBlock_forced` (`:392`) shows that for every terminal
  inside the reward cube dominating the solo rewards, the all-Continue block
  satisfies every other clause with absorption mass identically `0`, and the
  objective would be vacuously zero there;
  `not_isQuittingCyclicContinuationBlock_allContinueBlock` (`:434`) closes it.
  **This is exactly the "all-continue rows at `z = Λ` satisfy everything" trap,
  and it is fenced.**
- `IsQuittingZeroSolo`: not vacuously true, not vacuously false
  (`FTVCyclicAdmissibleCycle.lean:438`, `QuittingZeroSoloDisjunct.lean:216`).
- `HasAdmissibleAbsorbingQuittingCycle`: not vacuously false
  (`:445`), and provably not vacuously true
  (`QuittingDisjunctionCounterexample.lean:635`).
- Exactly two `sorry`s in project source, both intentional. Nothing in the
  verified chain touches `sorryAx`. `native_decide` appears only in
  `BlockPairK11Dyadic*`, confirmed outside the quitting chain.

## The three weaknesses, ranked

**1. The only landed carrier is refuted, and the conjecture files documented an
architecture that does not exist.** `not_forall_isQuittingZeroSolo_or_...`
(`QuittingDisjunctionCounterexample.lean:676`) proves the disjunction is not
exhaustive, so `exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle`
can never be upgraded to unconditional existence, and the large
`Quitting*Cycle*` / `Quitting*Debt*` mass built on that carrier cannot close
the conjecture as organized. Both conjecture docstrings still named
`quitting_zeroSolo_or_admissibleCycle` as "the one open premise" — a
declaration that exists nowhere.
**Acted on 2026-08-04 (`bad7543`)**: both docstrings rewritten to the real
position. The structural half of the finding stands: no named premise
currently reduces to the conjecture.

**2. `StochasticGame.Act : ι → Type` is state-independent while its field
docstring claimed it "may depend on state".** So
`exists_uniformDeviationCapConstructor` was billed as the central open problem
while stating it only for the state-independent class. The padding reduction is
standard and WLOG but is formalized nowhere.
**Acted on 2026-08-04**: the false field docstring corrected, a scope note added
to the conjecture, and the reduction queued as `LEAN-F0-1`. Quitting games are
unaffected (`Act = Bool` everywhere).

**3. The free-continuation vacuity surface is large and the fence guarding it
is a per-theorem side condition, not structural.** Every
`IsεQuittingRootSuccessorCertificate` is a statement about arrays of reals with
`tail` free, and `quittingRootSuccessorPayoff reward z allContinueRoot = z`
(`QuittingNashBellmanClockReduction.lean:132`) means the all-continue row
satisfies the successor equation against *every* `z`. Only two things stop the
trap — the absorption clause and zero-anchoring at a cutoff — and both are
hypotheses carried theorem-by-theorem across the tree, so a new certificate
omitting both reintroduces it silently and passes every existing test.
**Queued as `LEAN-F0-2`**: make the fence structural, so vacuity becomes a type
error rather than a missing hypothesis. This trap has been rediscovered
independently five or more times.

## Additions from the second, independent pass

**A soundness argument by import graph, verified.** Exactly two `sorry`s exist
in `GameTheory/`, in `QuittingConjecture.lean` and
`UniformExistenceConjecture.lean`. Those two modules are imported by **nothing
except each other and the root `GameTheory.lean` aggregator** — checked
directly: `QuittingConjecture` has one importer (`GameTheory.lean`),
`UniformExistenceConjecture` has two (`QuittingConjecture` and
`GameTheory.lean`). So **no landed theorem can transitively depend on
`sorryAx`**, by the import graph alone, independently of any `#print axioms`
run. That is a stronger and cheaper guarantee than per-theorem axiom audits,
and it is worth preserving deliberately: keep the conjecture modules leaves.

**One more unformalized WLOG.** Deviations are *behavior* strategies, not mixed
strategies. Perfect recall holds — a player sees its own past actions — so
Kuhn's theorem makes the restriction vacuous, but Kuhn is not in this
repository. Same shape as the `Act` padding reduction: it does not make any
landed theorem false, it makes a statement *about* the theorems unchecked.

**Two load-bearing non-redundancy claims are prose, not theorems.** That (H2)
admissibility cannot be dropped from the cycle bridge
(`QuittingAdmissibleCycleTerminalEquilibrium.lean:54-65`, "hand check, not
formalized here") and that the `carrierReward` table admits no admissible cycle
(`QuittingZeroSoloDisjunct.lean:186-194`). Both are two-player concrete tables,
so both are promotable to `¬`-theorems in a few hours each, which removes prose
from the load path.

**Tooling note carried forward.** The second pass could not complete a clean
`#print axioms` sweep: the docstring edit to `StochasticGame.lean` invalidates
the whole downstream olean tree, and concurrent `lean_verify` calls collided
and aborted a build. One clean run correctly reported `sorryAx` for
`quittingGame_exists_uniformEquilibriumPayoff`; two others returned an empty
axiom list, which is not credible and was treated as tool failure rather than
evidence. **Do not run concurrent `lean_verify` calls against a tree with a
build in flight.**
