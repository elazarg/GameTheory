# Phase 5: stressing the design under theorem load

Status: open. The mode is neither validation nor harvesting.

Phases 0–3 asked whether the architecture survives hostile slices. Phase 4 asked
whether ordinary mathematics goes through on it. This phase asks the question
that decides what the library costs over its lifetime: **when the next important
theorem arrives, does it land cheaply, or does it need machinery the design
should have made unnecessary?**

The test for a design choice here is not whether a theorem can be proved on it.
It is whether a theorem *from a part of the subject that has not been built yet*
can be stated without a parallel copy of something that already exists.

## The cost question, measured rather than feared

The concern that opened the phase was that the old library needed roughly four
and a half thousand lines of mathematics above the fixed-point dependency, and
that the same bill might come due again. It does not, and the reason is worth
recording because it is not the reason one would guess.

Those lines were never spent on equilibrium existence. Measured by import, in
the pinned snapshot:

| v1 module | lines | what consumes it |
|---|---:|---|
| `FixedPoint/Scarf` | 2554 | **nothing** |
| `LinearProgramming` | — | **nothing** |
| `SchauderFixedPoint` → `FixedPoint/KKM` | 444 | envy-free cake cutting, and nothing else |
| `Simplex` → `Minimax/Loomis` | ~1200 | Loomis's theorem, and through it Perron–Frobenius |
| `SimplexApproximation` | 134 | the folk theorem, all five importers |

Equilibrium existence in v1 went a different way entirely — Brouwer, via
`ProductSimplexBrouwer`, `NashExistenceMixed`, and `NashExistence`: **842
lines**. The same theorem here is **320**, because Kakutani applies directly to
the best-reply correspondence and the finite-support law type already presents a
point of the simplex.

So the bill is real but it is attached to *specific theorems* — fair division,
Loomis, the folk theorem — rather than to the architecture. The lesson for this
phase is that "will we need those lines" is the wrong question. The right one is
which upcoming theorems carry their own irreducible mathematics, and which are
paying a tax the design could remove.

## Findings

### The preference vocabulary was about lotteries by accident

Recorded as [EXP-024](ExperimentLog.md). Thirteen of the sixteen declarations in
`Core/Preference.lean` were relation algebra nailed to `FinDist Outcome`, which
none of them used; and every one of them was agent-indexed, so a *social*
ranking — one ranking, no agent — could not borrow any of it.

Nothing had asked, because every theorem to that point compared laws. Social
choice asks immediately: it ranks alternatives, and there is no probability
anywhere in it.

The repair splits the vocabulary rather than duplicating it. `Rank` states each
law for one comparison over an arbitrary carrier; `Preference` states it as that
law holding for every agent, and is definitionally that. The library rebuilt
with no downstream edit at all, because currying makes the new definitions defeq
to the old.

The downstream theorem is the Condorcet paradox, in `Examples/Voting.lean`:
three voters in rotation, each total and transitive, whose majority ranking
cycles. Individual rationality and social irrationality now read in the same
words.

Delegating to Mathlib was measured and rejected. Its bare-relation `Transitive`,
`Reflexive`, and `Total` are deprecated in favour of typeclasses, and a
preference here must stay an argument — one carrier is routinely studied under
several preferences at once.

## Axes not yet stressed

Each of these is a part of the subject the design has never been asked about,
listed with the choice it would put pressure on.

*Cooperative games.* A coalitional game is a value on coalitions, not a form
with strategies. Either it reuses the coalition machinery the core already has —
`Subprofile`, `Profile.restrict`, `Preference.coalition`, the strong-equilibrium
deviation shape — or `GameForm` is not the centre it claims to be. The core and
the Shapley value are the theorems to push at it.

*Arrow's theorem.* The vocabulary now states it. Proving it is the honest test
of whether the split above was deep enough, since the pivotal-voter argument
manipulates whole profiles of rankings rather than one comparison at a time.

*Repeated play and the folk theorem.* Stresses the protocol layer's
composability, and needs limits — so it also tests whether the analytic boundary
is drawn in the right place, or whether a second class of theorem wants to live
above it.

*Bayesian games.* Types, priors, and interim expected utility, against
`InformationModel`.

*Sequential equilibrium.* Consistency is a limit of completely mixed behavioral
profiles, which puts topology on strategies rather than on outcomes — the first
thing that would want the analytic root to reach *down* into the protocol layer
rather than up from the static core.
