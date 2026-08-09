# P-MATCH: ordinal deferred acceptance and perfect stable matchings

Title: Native ordinal Gale--Shapley stability and balanced perfectness
Family ID: P-MATCH
Pinned roots: `GameTheory/Cooperative/Matching.lean`, `GameTheory/Cooperative/GaleShapley.lean`, `GameTheory/Cooperative/GaleShapley/Perfect.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `98288d9`
Canonical destination: `GameTheory.Cooperative`
Domain contract / decision: D9, EXP-068, D35
Owner: Wave 4 / matching and market design
Status: partial; all 74 declarations classified, with stability and perfectness complete and 11 optimality/symmetry rows deferred
Last verified: 2026-08-09

The successor replaces v1's integer scores and separate reservation values by
the canonical probability-free `Ranking` over optional partners.  The outside
option is therefore part of the same ordinal comparison.  Finiteness and
linear-ranking laws occur only on deferred acceptance; the semantic market
stores neither capability.  The bounded gate completes general stable
existence and balanced completely-acceptable perfectness.  Proposer
optimality, receiver pessimality, and the two opposed-preference symmetry
lemmas are named BFS work rather than prerequisites for the mature workflow.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Cooperative/Matching.lean` | `MatchingMarket` | structure | adapt | `GameTheory.MatchingMarket` | EXP-068 owner comparison | Ordinal rankings over `Option` replace two integer scores and reservation values. |
| same | `IsMatching` | def | port | `GameTheory.MatchingMarket.IsMatching` | focused build | One-to-one partial assignment remains a separate certificate. |
| same | `IsBlockingPair` | def | adapt | `GameTheory.MatchingMarket.IsBlockingPair` | hostile negative control | Direct strict comparisons against optional current partners. |
| same | `IsIndividuallyRationalA` | def | subsumed | `GameTheory.MatchingMarket.IsIndividuallyRational` | projection `.1` | Both sides share one transparent predicate. |
| same | `IsIndividuallyRationalB` | def | subsumed | `GameTheory.MatchingMarket.IsIndividuallyRational` | projection `.2` | Both sides share one transparent predicate. |
| same | `HasCompleteAcceptability` | def | adapt | `GameTheory.MatchingMarket.HasCompleteAcceptability` | hostile fixture | Strictly ranks every partner above `none`. |
| same | `hasCompleteAcceptability_reserveA_ne` | theorem | retired | direct strict ranking | D35 representation decision | No numeric reservation equality survives in the ordinal API. |
| same | `hasCompleteAcceptability_reserveB_ne` | theorem | retired | direct strict ranking | D35 representation decision | No numeric reservation equality survives in the ordinal API. |
| same | `IsStable` | def | adapt | `GameTheory.MatchingMarket.IsStable` | explicit blocking-pair rejection | Same validity/IR/no-blocking content over the canonical relation. |
| same | `IsStable.isIndividuallyRationalA` | theorem | subsumed | `GameTheory.MatchingMarket.IsStable.isIndividuallyRational` | projection `.1` | Combined theorem. |
| same | `IsStable.isIndividuallyRationalB` | theorem | subsumed | `GameTheory.MatchingMarket.IsStable.isIndividuallyRational` | projection `.2` | Combined theorem. |
| same | `StableMatching` | abbrev | port | `GameTheory.MatchingMarket.StableMatching` | focused build | Stable subtype. |
| same | `<anonymous@113>` | instance | port | `MatchingMarket.StableMatching.instCoeFun` | root build | Stable matchings coerce to assignments. |
| same | `ext` | theorem | port | `GameTheory.MatchingMarket.StableMatching.ext` | focused build | Pointwise extensionality. |
| same | `empty_isMatching` | theorem | port | `GameTheory.MatchingMarket.empty_isMatching` | focused build | Empty assignment is injective. |
| same | `empty_stable_if_all_prefer_unmatched` | theorem | adapt | same name under `GameTheory.MatchingMarket` | focused build | Outside-option preference is direct. |
| same | `stable_respects_mutual_top` | theorem | adapt | same name under `GameTheory.MatchingMarket` | ordinal top-choice theorem | States topness over optional partners. |
| same | `stable_ir` | theorem | adapt | `GameTheory.MatchingMarket.stable_individually_rational` | focused build | Combined two-sided conclusion. |
| `GameTheory/Cooperative/GaleShapley.lean` | `accW` | abbrev | adapt | `GameTheory.MatchingMarket.AcceptableToLeft` | focused build | Ordinal outside-option comparison. |
| same | `accM` | abbrev | adapt | `GameTheory.MatchingMarket.AcceptableToRight` | focused build | Ordinal outside-option comparison. |
| same | `available` | def | adapt | `GameTheory.MatchingMarket.available` | first-round witness | No stored finite market. |
| same | `topChoice` | def | adapt | `GameTheory.MatchingMarket.topChoice` | hostile rankings | Finite total relation selector, not integer argmax. |
| same | `suitors` | def | adapt | `GameTheory.MatchingMarket.suitors` | rejection witness | Canonical proposal set. |
| same | `holder` | def | adapt | `GameTheory.MatchingMarket.holder` | partner-replacement witness | Ordinal greatest suitor. |
| same | `daStep` | def | adapt | `GameTheory.MatchingMarket.daStep` | exact first-round equality | Inflationary rejection step. |
| same | `mem_available` | theorem | port | `GameTheory.MatchingMarket.mem_available` | focused build | Membership specification. |
| same | `topChoice_spec` | theorem | adapt | `GameTheory.MatchingMarket.topChoice_spec` | focused build | Greatest under the ranking relation. |
| same | `topChoice_mem` | theorem | port | `GameTheory.MatchingMarket.topChoice_mem` | focused build | Availability. |
| same | `accW_of_topChoice` | theorem | adapt | `GameTheory.MatchingMarket.acceptableToLeft_of_topChoice` | focused build | Direct acceptability. |
| same | `mem_suitors` | theorem | port | `GameTheory.MatchingMarket.mem_suitors` | focused build | Suitor specification. |
| same | `holder_spec` | theorem | adapt | `GameTheory.MatchingMarket.holder_spec` | focused build | Greatest under the receiver ranking. |
| same | `holder_isSome_of_suitors` | theorem | port | same name under `GameTheory.MatchingMarket` | focused build | Nonempty suitors give a holder. |
| same | `subset_daStep` | theorem | port | `GameTheory.MatchingMarket.subset_daStep` | focused build | Inflationarity. |
| same | `daMeasure` | def | port | `GameTheory.MatchingMarket.daMeasure` | focused build | Total rejection count. |
| same | `daMeasure_mono` | theorem | port | `GameTheory.MatchingMarket.daMeasure_mono` | focused build | Measure monotonicity. |
| same | `daMeasure_le` | theorem | port | `GameTheory.MatchingMarket.daMeasure_le` | focused build | Finite product bound. |
| same | `exists_daStep_iterate_fixed` | theorem | port | same name under `GameTheory.MatchingMarket` | focused build | Termination to a fixed iterate. |
| same | `fixedPoint_holder` | theorem | port | `GameTheory.MatchingMarket.fixedPoint_holder` | focused build | Unrejected proposals are held. |
| same | `fixedPoint_isMatching` | theorem | port | `GameTheory.MatchingMarket.fixedPoint_isMatching` | focused build | Fixed-point assignment is one-to-one. |
| same | `fixedPoint_ir` | theorem | adapt | `GameTheory.MatchingMarket.fixedPoint_individuallyRational` | focused build | Combined two-sided predicate. |
| same | `topChoice_eq_of_isMax` | theorem | adapt | `GameTheory.MatchingMarket.topChoice_eq_of_isBest` | hostile choice proofs | Antisymmetry replaces injective integer scores. |
| same | `available_daStep_subset` | theorem | port | `GameTheory.MatchingMarket.available_daStep_subset` | focused build | Availability shrinks. |
| same | `holder_remains_suitor` | theorem | adapt | `GameTheory.MatchingMarket.holder_remains_suitor` | focused build | Uses ordinal uniqueness. |
| same | `holder_improve` | theorem | adapt | `GameTheory.MatchingMarket.holder_improves` | partner-replacement fixture | Weak ordinal improvement. |
| same | `Inv` | def | adapt | `GameTheory.MatchingMarket.DeferredAcceptanceInvariant` | focused build | Rejection justified by unacceptability or a strictly better holder. |
| same | `inv_empty` | theorem | adapt | `GameTheory.MatchingMarket.invariant_empty` | focused build | Base invariant. |
| same | `inv_step` | theorem | adapt | `GameTheory.MatchingMarket.invariant_step` | focused build | Ordinal preservation proof. |
| same | `inv_iterate` | theorem | adapt | `GameTheory.MatchingMarket.invariant_iterate` | focused build | Iterated invariant. |
| same | `no_blocking` | theorem | adapt | `GameTheory.MatchingMarket.no_blocking_at_fixedPoint` | focused build | Fixed point plus invariant excludes blocking. |
| same | `daFixedPoint` | def | port | `GameTheory.MatchingMarket.daFixedPoint` | focused build | Classically selected terminating iterate. |
| same | `daStep_daFixedPoint` | theorem | port | `GameTheory.MatchingMarket.daStep_daFixedPoint` | focused build | Fixedness. |
| same | `daMatching` | def | adapt | `GameTheory.MatchingMarket.deferredAcceptance` | hostile specialization | Descriptive public name. |
| same | `daMatching_isStable` | theorem | adapt | `GameTheory.MatchingMarket.deferredAcceptance_isStable` | general flagship | Ordinal stability. |
| same | `exists_stable` | theorem | adapt | `GameTheory.MatchingMarket.exists_stable` | general flagship | Arbitrary finite carriers, relation-valued preferences. |
| same | `IsAchievable` | def | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Needed only for optimality, not existence or perfectness. |
| same | `MAchInv` | def | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Optimality invariant. |
| same | `machInv_empty` | theorem | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Optimality invariant base. |
| same | `machInv_step` | theorem | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Port against ordinal rankings. |
| same | `machInv_iterate` | theorem | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Port against ordinal rankings. |
| same | `daMatching_man_optimal` | theorem | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Recover as left-proposer optimality. |
| same | `daMatching_woman_pessimal_of_matched` | theorem | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Receiver-side comparison. |
| same | `daMatching_woman_matched_in_stable` | theorem | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Rural-hospitals bridge. |
| same | `daMatching_woman_pessimal` | theorem | deferred | P-MATCH proposer-optimality BFS gate | D35 follow-up | Strong receiver-pessimal result. |
| `GameTheory/Cooperative/GaleShapley/Perfect.lean` | `exists_unmatched_right_of_unmatched_left` | theorem | port | same name under `GameTheory.MatchingMarket` | focused build | Balanced finite counting. |
| same | `exists_unmatched_left_of_unmatched_right` | theorem | port | same name under `GameTheory.MatchingMarket` | focused build | Valid matching counting. |
| same | `not_unmatched_acceptable_pair_of_stable` | theorem | adapt | same name under `GameTheory.MatchingMarket` | focused build | Direct ordinal block. |
| same | `opposed_preferences` | theorem | deferred | P-MATCH symmetry BFS gate | D35 follow-up | Requires the inverse-market surface, unnecessary for perfectness. |
| same | `opposed_preferences_women` | theorem | deferred | P-MATCH symmetry BFS gate | D35 follow-up | Symmetric corollary. |
| same | `stable_matching_perfect` | theorem | adapt | `GameTheory.MatchingMarket.stable_matching_perfect` | general flagship | Complete acceptability is one ordinal certificate. |
| same | `rightPartner` | def | adapt | `GameTheory.MatchingMarket.rightPartner` | focused build | Consumes a reusable `IsPerfect` certificate. |
| same | `leftPartner` | def | adapt | `GameTheory.MatchingMarket.leftPartner` | focused build | Consumes a reusable `IsPerfect` certificate. |
| same | `match_rightPartner` | theorem | adapt | same name under `GameTheory.MatchingMarket` | focused build | Perfectness projection. |
| same | `match_leftPartner` | theorem | adapt | same name under `GameTheory.MatchingMarket` | focused build | Perfectness projection. |
| same | `rightPartner_eq_iff_leftPartner_eq` | theorem | adapt | same name under `GameTheory.MatchingMarket` | focused build | Uses the independent validity certificate. |

Attribution: the predecessor supplies the inflationary rejection-state proof,
termination measure, rejection invariant, and balanced perfectness counting
argument.  The successor keeps those arguments while replacing cardinal scores
by `Ranking`, making `none` the actual outside option, and moving all
capabilities to operations and theorems.

Validation:

```text
lake build GameTheory.Cooperative GameTheory.Tests.Matching
git diff --check
```

The hostile fixture has three agents on each side.  Its exact first round
rejects left zero from right zero; at the reachable next state right one
replaces left two with left zero.  A separate assignment has the concrete
blocking pair `(left one, right zero)`, while the contested final assignment is
stable and perfect and the general perfect-stable theorem specializes to the
same market.
