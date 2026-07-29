# Phase 4: the static harvest

Status: first pass complete. Five theorem families recovered against the
accepted API, each instantiated, none requiring a change to it.

The mode here differs from the earlier phases. Those validated architecture by
pushing hostile slices at it; this one assumes the architecture and asks whether
ordinary mathematics goes through on it. The measure of success is therefore
*absence of friction*: no definition was widened, no interface was renegotiated,
and the only additions to the law type are general facts that had consumers in
the same commit.

## What was recovered

| Family | Where | The theorem that carries it |
|---|---|---|
| iterated strict dominance | `Core/Response.lean` | a strictly dominated strategy is never rationalizable, with nothing assumed about what beats it |
| Pareto comparisons | `Core/Response.lean` | a strong equilibrium is weakly Pareto efficient |
| the correlated hierarchy | `Core/Equilibrium.lean` | both correlated concepts are closed under mixing; Nash sits inside them |
| potential games | `Core/Potential.lean` | a finite potential game has a pure equilibrium |
| the mixed extension | `Core/Mixed.lean` | pure equilibria survive it, and a mixed equilibrium is indifferent across its own support |

Each is instantiated in `Examples/Classic.lean` on the Prisoner's Dilemma, in
the style the file already used: the finite frontend supplies one computed fact
and the semantic layer carries it the rest of the way. Cooperation is strictly
dominated *by computation*; that it is never rationalizable and never played in
equilibrium follows *by theorem*.

## Hypotheses that earn their place

Three hypotheses in this pass are not technical noise, and each is documented
where it appears rather than hidden behind an instance.

*A witness profile*, for "a dominant strategy is never strictly dominated". With
no profile at all, strict dominance is vacuous and every strategy dominates
every other, so the statement is false without an inhabitant. Lean rejected the
version without it.

*Convexity of the preference*, for closure of the correlated concepts under
mixing. Nothing forces a weak preference to respect mixing; expected utility
does, and that is proved rather than assumed.

*Expected utility specifically*, for survival of the mixed extension. A pure
equilibrium resists only pure deviations while the mixed game offers a law over
them, and what closes the gap is that the deviator's utility is the *average* of
the pure ones. A preference that does not respect averaging has no reason to
survive the embedding.

## Where the theorems stop, stated rather than skirted

*Strong equilibrium gives only weak Pareto efficiency.* An equilibrium against
coalitions objects when every member gains; Pareto domination allows some
members to be indifferent, and is the stronger demand. The Prisoner's Dilemma
exhibits the gap: mutual defection is weakly Pareto efficient and is not Pareto
efficient.

*Nash equilibria are not convex.* Mixing two of them correlates the players,
which is exactly what a Nash profile may not do. The correlated concepts survive
because each compares a composition of the status quo against another
composition of the same status quo, and composition is affine in the law it
composes with.

*A potential buys existence and nothing else.* It constrains unilateral changes
only, so it says nothing about coalitions and nothing about efficiency.

## Additions to the law type

Five, each with a consumer in the same commit: composition is affine in the law
it composes with; an expectation is bounded by a bound its support respects; an
average that attains its bound attains it everywhere it looks; and the strict
version underneath that.

## Measurements

```text
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

| Measure | Value |
|---|---:|
| `GameTheory/Core` theorems | 103 |
| `GameTheory/Core` modules | 9 |
| interface changes required by the harvest | 0 |
| `sorry`, `admit`, `native_decide`, custom axioms | 0 |
| transport tokens added to the static layer | 0 |

## Outstanding

- A mechanism-design encoding, with truthful reporting as a dominance statement.
  That is a language module rather than a theorem family, so it belongs with the
  other encodings and carries the same obligation: a workaround list.
- The remaining flagship at this layer is *not* general equilibrium existence.
  That route is closed: the pinned Mathlib has neither Brouwer nor Kakutani, and
  supplying either would be a topology project of its own. What is in reach is
  the two-player zero-sum minimax theorem, since Mathlib does carry Sion's
  version of it.
- The dependency boundary for that work sits at the bridge presenting a
  finite-support law as a compact convex set, not at the theorem: importing
  Sion's theorem makes neither of the probed constants reachable. The boundary
  should be a root that Core and Protocol do not import, with its own probe
  expectations recorded rather than an exception patched into the existing ones.
