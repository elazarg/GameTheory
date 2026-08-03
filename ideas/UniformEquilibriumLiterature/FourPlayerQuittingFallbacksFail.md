# Four-player quitting fallback-collapse fence

| Field | Value |
| --- | --- |
| Citation of record | Solan--Vieille, *Quitting Games--An Example*, IJGT 31(3):365--381 (2002), DOI `10.1007/s001820200125` |
| Source confidence | `PRIMARY_VERIFIED` for the qualitative propositions; `UNRESOLVED` for the printed period-two numerical packet |
| Mathematical status | `PROVED`; numerical constants disputed |
| Repository status | `RECORDED` |
| Lean status | `PLANNED` |
| Objective priority | `P1` |
| Exact scope and quantifiers | One explicit four-player quitting table defeats the stationary exact, sufficiently accurate stationary/perturbed, small-termination, and solo-payoff-convex-hull fallback languages stated in the paper. |
| Source alignment | No Lean transcription yet. |
| Lean destination | `SolanVieilleFourPlayerQuittingFence.lean` |
| Acceptance and consumer | Transcribe the source-stable table, prove each qualitative fence separately, and use it as a permanent regression for every proposed quitting architecture. |
| Discrepancies | The printed period-two probabilities/payoffs do not pass the current arithmetic audit; no uncertain constants enter Lean. |

The corrected repository account is in
[`30-counterexamples.md`](../../docs/uniform-equilibrium/references/30-counterexamples.md).
The 2001 MOR paper is not the citation for this fence. Source-aligned theorem
docstrings must cite the 2002 IJGT propositions individually. The existence of
some cyclic equilibrium is not a license to formalize the disputed printed
certificate.
