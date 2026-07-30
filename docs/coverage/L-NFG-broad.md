# L-NFG: Broad normal-form language and examples

Title: Broad normal-form language and examples
Family ID: L-NFG
Pinned roots: `GameTheory/Languages/NFG/CheapTalkExamples.lean`; `GameTheory/Languages/NFG/Compile.lean`; `GameTheory/Languages/NFG/CountableExample.lean`; `GameTheory/Languages/NFG/Examples.lean`; `GameTheory/Languages/NFG/MatchingPenniesMixed.lean`; `GameTheory/Languages/NFG/PublicGoods.lean`; `GameTheory/Languages/NFG/Stackelberg.lean`; `GameTheory/Languages/NFG/Syntax.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `01f790a`
Canonical destination: GameTheory.Languages.NFG; GameTheory.Examples; canonical Core and Analysis concepts
Domain contract / decision: D4-D10, D15, EXP-042
Owner: Wave 2 / mature static and language recovery
Status: in progress; 4 reviewed, 104 unreviewed
Last verified: 2026-07-30

This ledger is an exact generated review queue for the L-NFG family.
18 declarations are already accounted for in
earlier bounded ledgers and are not duplicated here. Every row below is
initially seeded as `unreviewed`: the generated index supplies spelling,
location, kind, and visibility only. It does not infer a mathematical
disposition. Reviewed rows replace that seed with explicit evidence.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Languages/NFG/CheapTalkExamples.lean` | `extension` | def | unreviewed | review required | generated index seed only | public, pinned line 26 |
| same | `game` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 31 |
| same | `opera_babbling_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 36 |
| same | `football_babbling_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 43 |
| `GameTheory/Languages/NFG/CountableExample.lean` | `natChoose` | def | adapt | `GameTheory.Examples.NFG.natChoose`; `natChooseUtility` | focused build | Utility is separated from the utility-free NFG syntax; no finite action capability is added. |
| same | `natChoose_zero` | def | adapt | `GameTheory.Examples.NFG.natChooseZero` | focused build | Canonical `Profile` over the compiled signature. |
| same | `natChoose_zero_is_nash` | theorem | adapt | `GameTheory.Examples.NFG.natChooseZero_isNash` | focused build | Uses canonical `IsNash` and `euPreference`, not a language-specific predicate. |
| same | `natChoose_zero_dominant_0` | theorem | adapt | `GameTheory.Examples.NFG.natChooseZero_isDominant_zero` | focused build | Uses canonical `IsDominant`; the action carrier remains `ℕ`. |
| `GameTheory/Languages/NFG/Examples.lean` | `PDAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 27 |
| same | `prisonersDilemma` | def | unreviewed | review required | generated index seed only | public, pinned line 36 |
| same | `pd_defect_defect` | def | unreviewed | review required | generated index seed only | public, pinned line 51 |
| same | `pd_defect_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 55 |
| same | `pd_coop_coop` | def | unreviewed | review required | generated index seed only | public, pinned line 61 |
| same | `pd_coop_not_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 65 |
| same | `MPAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 75 |
| same | `matchingPennies` | def | unreviewed | review required | generated index seed only | public, pinned line 84 |
| same | `matchingPennies_no_pure_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 99 |
| same | `SHAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 127 |
| same | `stagHunt` | def | unreviewed | review required | generated index seed only | public, pinned line 139 |
| same | `sh_stag_stag` | def | unreviewed | review required | generated index seed only | public, pinned line 152 |
| same | `sh_hare_hare` | def | unreviewed | review required | generated index seed only | public, pinned line 156 |
| same | `sh_stag_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 160 |
| same | `sh_hare_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 166 |
| same | `sh_stag_hare_not_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 173 |
| same | `HDAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 188 |
| same | `hawkDove` | def | unreviewed | review required | generated index seed only | public, pinned line 200 |
| same | `hd_hawk_dove` | def | unreviewed | review required | generated index seed only | public, pinned line 213 |
| same | `hd_dove_hawk` | def | unreviewed | review required | generated index seed only | public, pinned line 217 |
| same | `hd_hawk_dove_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 221 |
| same | `hd_dove_hawk_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 227 |
| same | `BoSAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 239 |
| same | `battleOfTheSexes` | def | unreviewed | review required | generated index seed only | public, pinned line 251 |
| same | `bos_opera_opera` | def | unreviewed | review required | generated index seed only | public, pinned line 263 |
| same | `bos_football_football` | def | unreviewed | review required | generated index seed only | public, pinned line 267 |
| same | `bos_opera_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 271 |
| same | `bos_football_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 277 |
| same | `DGAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 290 |
| same | `dictatorGame` | def | unreviewed | review required | generated index seed only | public, pinned line 300 |
| same | `dg_keep_all` | def | unreviewed | review required | generated index seed only | public, pinned line 313 |
| same | `dg_keep_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 318 |
| same | `dg_giveAll_not_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 325 |
| same | `TDAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 343 |
| same | `travelersDilemma` | def | unreviewed | review required | generated index seed only | public, pinned line 356 |
| same | `td_claim2_claim2` | def | unreviewed | review required | generated index seed only | public, pinned line 369 |
| same | `td_claim2_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 374 |
| same | `CournotQty` | inductive | unreviewed | review required | generated index seed only | public, pinned line 388 |
| same | `cournotProfit` | def | unreviewed | review required | generated index seed only | public, pinned line 398 |
| same | `cournotDuopoly` | def | unreviewed | review required | generated index seed only | public, pinned line 404 |
| same | `cournot_q2_q2` | def | unreviewed | review required | generated index seed only | public, pinned line 412 |
| same | `cournot_q2_q2_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 416 |
| same | `BraessRAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 446 |
| same | `BraessAAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 450 |
| same | `braessRestricted` | def | unreviewed | review required | generated index seed only | public, pinned line 455 |
| same | `braessAugmented` | def | unreviewed | review required | generated index seed only | public, pinned line 466 |
| same | `braessRestricted_aa_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 486 |
| same | `braessAugmented_cc_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 494 |
| same | `braessAugmented_aa_not_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 502 |
| same | `braess_welfare_decreases` | theorem | unreviewed | review required | generated index seed only | public, pinned line 516 |
| same | `BertrandPrice` | inductive | unreviewed | review required | generated index seed only | public, pinned line 546 |
| same | `BertrandPrice.toReal` | def | unreviewed | review required | generated index seed only | public, pinned line 551 |
| same | `bertrandProfit` | def | unreviewed | review required | generated index seed only | public, pinned line 556 |
| same | `bertrandDuopoly` | def | unreviewed | review required | generated index seed only | public, pinned line 568 |
| same | `bertrand_p2_p2` | def | unreviewed | review required | generated index seed only | public, pinned line 576 |
| same | `bertrand_p1_p1` | def | unreviewed | review required | generated index seed only | public, pinned line 580 |
| same | `bertrand_p2_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 584 |
| same | `bertrand_p1_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 592 |
| same | `pd_defect_udist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 602 |
| same | `pd_defect_isNashFor_eu` | theorem | unreviewed | review required | generated index seed only | public, pinned line 609 |
| same | `pd_defect_isDominantFor_eu` | theorem | unreviewed | review required | generated index seed only | public, pinned line 616 |
| `GameTheory/Languages/NFG/MatchingPenniesMixed.lean` | `<anonymous@32>` | instance | unreviewed | review required | generated index seed only | private, pinned line 32 |
| same | `matchingPenniesOutcomeFintype` | instance | unreviewed | review required | generated index seed only | private, pinned line 34 |
| same | `matchingPenniesOutcomeFinite` | instance | unreviewed | review required | generated index seed only | private, pinned line 39 |
| same | `matchingPenniesStrategyNonempty` | instance | unreviewed | review required | generated index seed only | private, pinned line 43 |
| same | `matchingPenniesStrategyFintype` | instance | unreviewed | review required | generated index seed only | private, pinned line 47 |
| same | `matchingPenniesLabels` | def | unreviewed | review required | generated index seed only | private, pinned line 55 |
| same | `matchingPennies_matchingPenniesLike` | def | unreviewed | review required | generated index seed only | private, pinned line 74 |
| same | `matchingPenniesFairMixed` | def | unreviewed | review required | generated index seed only | public, pinned line 96 |
| same | `matchingPennies_uniform_mixed_balanced` | theorem | unreviewed | review required | generated index seed only | public, pinned line 101 |
| same | `matchingPennies_mixed_nash_iff_half` | theorem | unreviewed | review required | generated index seed only | public, pinned line 108 |
| same | `matchingPennies_fair_mixed_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 124 |
| same | `matchingPenniesLabels_uniform_eq_fair` | theorem | unreviewed | review required | generated index seed only | private, pinned line 139 |
| same | `matchingPennies_fair_correlated_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 156 |
| same | `matchingPennies_correlated_eq_unique` | theorem | unreviewed | review required | generated index seed only | public, pinned line 164 |
| same | `matchingPennies_correlated_eq_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 175 |
| `GameTheory/Languages/NFG/PublicGoods.lean` | `publicGoods_freeRide_dominant` | theorem | unreviewed | review required | generated index seed only | public, pinned line 29 |
| same | `publicGoods_cooperation_pareto` | theorem | unreviewed | review required | generated index seed only | public, pinned line 49 |
| `GameTheory/Languages/NFG/Stackelberg.lean` | `StackelbergGame` | structure | unreviewed | review required | generated index seed only | public, pinned line 37 |
| same | `followerBR` | def | unreviewed | review required | generated index seed only | public, pinned line 52 |
| same | `stackelbergPayoff` | def | unreviewed | review required | generated index seed only | public, pinned line 56 |
| same | `IsStackelbergEq` | def | unreviewed | review required | generated index seed only | public, pinned line 60 |
| same | `IsSimNash` | def | unreviewed | review required | generated index seed only | public, pinned line 64 |
| same | `stackelberg_leader_ge_commitment` | theorem | unreviewed | review required | generated index seed only | public, pinned line 71 |
| same | `followerBR_at_nash_unique` | theorem | unreviewed | review required | generated index seed only | public, pinned line 82 |
| same | `toKernelGame` | def | unreviewed | review required | generated index seed only | public, pinned line 94 |
| same | `fight` | def | unreviewed | review required | generated index seed only | public, pinned line 127 |
| same | `accommodate` | def | unreviewed | review required | generated index seed only | public, pinned line 128 |
| same | `enter` | def | unreviewed | review required | generated index seed only | public, pinned line 129 |
| same | `stayOut` | def | unreviewed | review required | generated index seed only | public, pinned line 130 |
| same | `uL` | def | unreviewed | review required | generated index seed only | public, pinned line 133 |
| same | `uF` | def | unreviewed | review required | generated index seed only | public, pinned line 140 |
| same | `game` | def | unreviewed | review required | generated index seed only | public, pinned line 147 |
| same | `br` | def | unreviewed | review required | generated index seed only | public, pinned line 155 |
| same | `br_isBR` | theorem | unreviewed | review required | generated index seed only | public, pinned line 160 |
| same | `game_stackelberg_eq_fight` | theorem | unreviewed | review required | generated index seed only | public, pinned line 166 |
| same | `game_simNash_accommodate` | theorem | unreviewed | review required | generated index seed only | public, pinned line 174 |
| same | `game_br_at_accommodate` | theorem | unreviewed | review required | generated index seed only | public, pinned line 184 |
| same | `leader_advantage` | theorem | unreviewed | review required | generated index seed only | public, pinned line 191 |
| same | `leader_advantage_strict` | theorem | unreviewed | review required | generated index seed only | public, pinned line 196 |

Before this ledger can become complete, each row must be reviewed against
the canonical successor API and assigned an allowed non-`unreviewed`
disposition with concrete build, theorem, decision, or counterexample
evidence. Generated name similarity is never sufficient.
