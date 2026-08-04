# Audit, 2026-08-04 — Simon's Mousetrap is retracted, and it would have reached us

> **Standing.** Dated audit record, not a live ledger. The retraction is
> independently verified and settled. The counterfactual — what would have
> happened had the proof stood — was read **twice, independently**, and the two
> readings agree on the mathematics but classify it differently. Both are
> recorded below, because the disagreement is the informative part.

## Trigger

`ephemeral/old/counterexample-research/sources/simon-noeq-v1.pdf` — R. S. Simon,
*A Stochastic Game without Approximate Equilibria*, arXiv:2310.04217v1
[math.FA], 6 Oct 2023 — had been downloaded into the repository and never
processed. Its abstract claims a stochastic game with finitely many players
and actions, and finitely many states, that lacks approximate equilibria. If
correct at our hypotheses, `exists_uniformEquilibriumPayoff` in
`UniformExistenceConjecture.lean` would be **false**, and the repository would
have been carrying a deliberate `sorry` on a false statement.

## Verdict 1 — the paper is withdrawn by its author. `SETTLED`

**arXiv:2310.04217 was withdrawn on 20 Oct 2023, fourteen days after posting,
with the author's own comment: "The proof is flawed."**

Verified directly at the arXiv Atom API on 2026-08-04:

```
<title>A Stochastic Game without Approximate Equilibria</title>
<published>2023-10-06T13:04:42Z</published>
<updated>2023-10-20T12:09:44Z</updated>
<link href="https://arxiv.org/abs/2310.04217v2" .../>
<arxiv:comment>The proof is flawed</arxiv:comment>
```

Corroborated by the abs page submission history (`[v1] 24 KB`,
`[v2] ... (withdrawn)` at 1 KB) and by the v2 page, which serves no PDF and
voids the license.

**Trap worth recording.** `arxiv.org/pdf/2310.04217` still serves the v1 PDF,
so a naive fetch or a search summarizer reports the paper as live, and a local
copy looks current. The metadata is authoritative; the PDF endpoint is not.
Any future literature audit in this program must check the Atom API's
`<arxiv:comment>` and version list, not just retrieve a PDF.

No published version exists, no repaired version has appeared, and Simon has
posted nothing to arXiv since. No third-party rebuttal exists and none should
be expected — a preprint retracted in fourteen days does not attract one.

Do not conflate this with two legitimate Simon results also in the tree:
*The challenge of non-zero-sum stochastic games*, IJGT 45(1):191–204 (2016)
(`sources/simon-challenge.pdf`, reference [9] of the withdrawn paper), and
*On games without approximate equilibria*, IJGT (2020), which is about
**Bayesian** games.

## Verdict 2 — had it stood, it would have refuted our exact statement. `CONSIDERED JUDGEMENT`

This is the part with lasting value, because it removes two defences the
repository was implicitly relying on. The auditor worked from the arXiv LaTeX
source (`Mouse5.tex`) rather than the PDF, and reports:

**Finite states — sound, though never counted in the paper.** The affine
family is pinned by slope `a_i = 2·10^12·(i−50)` and the crossing condition,
forcing `b_i − b_{i+1} = 10^10·(2i+1)`, so every `s_i^±` lies in `10^10·ℤ`.
All stage payoffs then lie in `(1/10^4)ℤ`, and cumulative sums are confined to
`[−3·10^16, 3·10^16]`. The recast state space is roughly `10^45`. Finite.
(One incidental over-estimate in the paper's own bound, conservative and
harmless.)

**Finite actions — confirmed.** Cat `102^101`, mouse `202`, dogs `2` each.
Astronomical, and irrelevant to `[∀ i, Finite (G.Act i)]`.

**Payoff notion — the defence fails.** The repository's docstring hedged that
the counterexample might need a genuinely non-limit-average Borel payoff. It
does not. The single non-sum term, `(1/1000)·liminf_n |A_n|/n`, is *exactly*
the limit average of the stage payoff `(1/1000)·1[state = S_200]` under the
paper's own finite-state encoding — the most limit-average object in the game.
It is the *sums* that need the standard running-sum-in-the-state encoding, and
the lattice structure of the payoffs supports it. The recast is exact:
`V^i = liminf_T (1/T)Σ_{t≤T} g_i` pathwise for every player.

**Monitoring — the defence fails.** This was the expected leak and is not one.
Because only the mouse acts on odd stages, nothing observable is generated
between the two halves of a combined stage: the mouse loses nothing by
committing simultaneously, the cat's within-stage advantage is absorbed by the
standard Kuhn normalization into its function-valued action set, and the dogs'
ignorance becomes plain within-stage simultaneity. The paper states the
post-stage full disclosure explicitly.

**Conclusion.** Finite states ✓, finite nonempty action sets ✓, four players ✓,
perfect monitoring ✓, limit average of stage payoffs ✓. Had the proof stood,
no hypothesis of ours would have saved us. Confidence reported: ~85%.

Two specification gaps in the paper, recorded for completeness: it never
defines the cat's or the dogs' payoff on non-absorbing paths (the recast
supplies `0`, which the argument tacitly uses), and the penalty depends on a
*future* action, so the recast must charge it one combined stage later with
the relevant indices carried in the state.

## The one real gap this exposes in our own definitions

`IsUniformEquilibriumPayoff` (`Uniform.lean:91`) constrains only
**finite-horizon averages** `finiteAveragePayoff s₀ T σ` for `T ≥ T₀`. A
non-existence result for the **liminf-average** game does not formally imply
non-existence of a uniform equilibrium payoff without a bridging lemma. The
deviation direction goes through by Fatou:
`E[liminf A_T] ≤ liminf E[A_T] ≤ v_i + 2ε`. The on-path direction,
`E_σ[liminf A_T] ≥ v_i − ε`, does **not** follow from pinned expectations
alone.

This is worth knowing independently of Simon: it is where the Lean work would
be if a valid counterexample ever did land at these hypotheses, and it is a
genuine asymmetry in what our definition can consume. Queued as `LEAN-F0-3`.

## The quitting-game front

The paper's Conclusion identifies three fronts — three-and-four-player games,
two-player games with **infinitely** many states (not a contradiction of
Vieille, since "normal" permits countably many), and quitting games — and
states beliefs, not results. On our middle target it says exactly one clause:

> "Also we believe there is a counter-example for quitting games."

No argument, no sketch, no player count. He gives methodological pessimism
about the perfection method only for the two-player/non-amenable front, and
says nothing about whether perfection would apply to quitting games.

**Transportability of the method: no, not as instantiated.** The abstract
perfection theorem (a normal stochastic game with approximate equilibria is
perfect) does apply to quitting games, so perfection remains a legitimate
necessary condition to attack. But the Mousetrap's *non-perfection* proof
needs a rich action set for the mouse to carry a quadratic penalty, a control
player who observes her declaration *within* the stage and punishes dishonesty,
and an enormous cumulative-sum state space. A quitting game has two actions per
player, one live state, and no observable but termination. A quitting-game
counterexample by this route would need a wholly new construction.

The belief survives the retraction as an expert's intuition — what was
withdrawn is a proof, not an intuition — but it is a single unargued sentence
in a retracted paper, and should be weighted accordingly.

## Where the auditor could not follow the proof

Recorded because it is the honest part. Lemma X (non-absorbing paths in `B`
are null) invokes the strong law on events that are neither independent nor
identically distributed and whose conditional probabilities depend on the
profile; what is needed is a martingale or conditional Borel–Cantelli
argument, and it is not given. The paper notes that the argument fails if
`limsup` replaces `liminf`, which shows how tightly it hangs on the
aggregation choice. Lemma 4's pivotal supermartingale claim is asserted rather
than derived, and Lemma Y's hypothesis — that dog quitting is the only reason
play may stop — is exactly what the Conclusion admits can fail once
cumulative-payoff absorption is live. Any guess at where "the proof is flawed"
bites is a guess.

## Actions taken

- `UniformExistenceConjecture.lean` and `QuittingConjecture.lean` rewritten to
  record the retraction as the reason the statement is safe, and to stop
  offering hypothesis-mismatch as a defence.
- `LEAN-F0-3` queued for the finite-horizon/liminf bridging lemma.
- Rule added: check the arXiv Atom API version list and `<arxiv:comment>`
  before treating any preprint as live.
