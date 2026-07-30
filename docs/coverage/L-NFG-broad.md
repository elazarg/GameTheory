# L-NFG: Broad normal-form language and examples

Title: Broad normal-form language and examples
Family ID: L-NFG
Pinned roots: `GameTheory/Languages/NFG/CheapTalkExamples.lean`; `GameTheory/Languages/NFG/Compile.lean`; `GameTheory/Languages/NFG/CountableExample.lean`; `GameTheory/Languages/NFG/Examples.lean`; `GameTheory/Languages/NFG/MatchingPenniesMixed.lean`; `GameTheory/Languages/NFG/PublicGoods.lean`; `GameTheory/Languages/NFG/Stackelberg.lean`; `GameTheory/Languages/NFG/Syntax.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `01f790a`
Canonical destination: GameTheory.Languages.NFG; GameTheory.Examples; canonical Core and Analysis concepts
Domain contract / decision: D4-D10, D15, EXP-042
Owner: Wave 2 / mature static and language recovery
Status: in progress; 54 reviewed, 54 unreviewed
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
| `GameTheory/Languages/NFG/Examples.lean` | `PDAction` | inductive | adapt | `GameTheory.Examples.Choice` | focused build | Canonical descriptive action type; no NFG-local semantic type. |
| same | `prisonersDilemma` | def | adapt | `GameTheory.Examples.prisonersDilemma` | focused build | Canonical rational `TableGame`; uses the standard ordinally equivalent payoff normalization. |
| same | `pd_defect_defect` | def | adapt | `GameTheory.Examples.bothDefect` | focused build | Canonical `Profile` witness. |
| same | `pd_defect_is_nash` | theorem | adapt | `GameTheory.Examples.prisonersDilemma_bothDefect_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `pd_coop_coop` | def | adapt | `GameTheory.Examples.bothCooperate` | focused build | Canonical `Profile` witness. |
| same | `pd_coop_not_nash` | theorem | adapt | `GameTheory.Examples.prisonersDilemma_bothCooperate_not_isNash` | focused build | Derived from the canonical unique-equilibrium theorem. |
| same | `MPAction` | inductive | adapt | `GameTheory.Examples.Side` | focused build | Canonical coin-side action type. |
| same | `matchingPennies` | def | adapt | `GameTheory.Examples.matchingPennies` | focused build | Exact rational `TableGame` with the canonical mixed extension available separately. |
| same | `matchingPennies_no_pure_nash` | theorem | adapt | `GameTheory.Examples.matchingPennies_noPureNash` | focused build | Universal semantic no-pure-Nash statement recovered. |
| same | `SHAction` | inductive | adapt | `GameTheory.Examples.Hunt` | focused build | Canonical descriptive action type. |
| same | `stagHunt` | def | adapt | `GameTheory.Examples.stagHunt` | focused build | Symmetric canonical `TableGame`, indexed by own and opponent actions. |
| same | `sh_stag_stag` | def | adapt | `GameTheory.Examples.bothStag` | focused build | Canonical `Profile` witness. |
| same | `sh_hare_hare` | def | adapt | `GameTheory.Examples.bothHare` | focused build | Canonical `Profile` witness. |
| same | `sh_stag_is_nash` | theorem | adapt | `GameTheory.Examples.stagHunt_bothStag_isNash` | focused build | Semantic `IsNash` theorem backed by the verified finite checker. |
| same | `sh_hare_is_nash` | theorem | adapt | `GameTheory.Examples.stagHunt_bothHare_isNash` | focused build | Semantic `IsNash` theorem backed by the verified finite checker. |
| same | `sh_stag_hare_not_nash` | theorem | adapt | `GameTheory.Examples.stagHunt_stagHare_not_isNash` | focused build | Canonical mismatched profile and semantic refutation. |
| same | `HDAction` | inductive | adapt | `GameTheory.Examples.Contest` | focused build | Canonical descriptive action type. |
| same | `hawkDove` | def | adapt | `GameTheory.Examples.hawkDove` | focused build | Symmetric canonical `TableGame`, indexed by own and opponent actions. |
| same | `hd_hawk_dove` | def | adapt | `GameTheory.Examples.hawkDoveProfile` | focused build | Canonical asymmetric `Profile` witness. |
| same | `hd_dove_hawk` | def | adapt | `GameTheory.Examples.doveHawkProfile` | focused build | Canonical role-reversed `Profile` witness. |
| same | `hd_hawk_dove_is_nash` | theorem | adapt | `GameTheory.Examples.hawkDoveProfile_isNash` | focused build | Semantic `IsNash` theorem backed by the verified finite checker. |
| same | `hd_dove_hawk_is_nash` | theorem | adapt | `GameTheory.Examples.doveHawkProfile_isNash` | focused build | Semantic `IsNash` theorem backed by the verified finite checker. |
| same | `BoSAction` | inductive | adapt | `GameTheory.Examples.Venue` | focused build | Canonical venue action type. |
| same | `battleOfTheSexes` | def | adapt | `GameTheory.Examples.battleOfTheSexes` | focused build | Canonical rational `TableGame`. |
| same | `bos_opera_opera` | def | adapt | `GameTheory.Examples.bothOpera` | focused build | Canonical `Profile` witness. |
| same | `bos_football_football` | def | adapt | `GameTheory.Examples.bothFootball` | focused build | Canonical `Profile` witness. |
| same | `bos_opera_is_nash` | theorem | adapt | `GameTheory.Examples.battleOfTheSexes_bothOpera_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `bos_football_is_nash` | theorem | adapt | `GameTheory.Examples.battleOfTheSexes_bothFootball_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `DGAction` | inductive | adapt | `GameTheory.Examples.Economic.Split` | focused build | Only the dictator receives this action carrier in the canonical heterogeneous signature. |
| same | `dictatorGame` | def | adapt | `GameTheory.Examples.Economic.dictatorGame` | focused build | Receiver carrier narrowed from three payoff-irrelevant actions to `PUnit`; payoffs are unchanged. |
| same | `dg_keep_all` | def | adapt | `GameTheory.Examples.Economic.dictatorKeepsAll` | focused build | Canonical heterogeneous `Profile` witness. |
| same | `dg_keep_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.dictatorKeepsAll_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `dg_giveAll_not_nash` | theorem | adapt | `GameTheory.Examples.Economic.dictatorGivesAll_not_isNash` | focused build | Canonical semantic refutation. |
| same | `TDAction` | inductive | adapt | `GameTheory.Examples.Economic.Claim` | focused build | Canonical descriptive action type. |
| same | `travelersDilemma` | def | adapt | `GameTheory.Examples.Economic.travelersDilemma` | focused build | Exact rational `TableGame`. |
| same | `td_claim2_claim2` | def | adapt | `GameTheory.Examples.Economic.bothClaimTwo` | focused build | Canonical `Profile` witness. |
| same | `td_claim2_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.travelersDilemma_bothClaimTwo_isNash` | focused build | Semantic theorem retained; exhaustive enumeration additionally records the weak `(3,3)` equilibrium. |
| same | `CournotQty` | inductive | adapt | `GameTheory.Examples.Economic.Quantity` | focused build | Canonical descriptive action type. |
| same | `cournotProfit` | def | adapt | `GameTheory.Examples.Economic.cournotProfit` | focused build | Same integer-valued table, represented computably in `ℚ`. |
| same | `cournotDuopoly` | def | adapt | `GameTheory.Examples.Economic.cournotDuopoly` | focused build | Canonical symmetric `TableGame`. |
| same | `cournot_q2_q2` | def | adapt | `GameTheory.Examples.Economic.bothQuantityTwo` | focused build | Canonical `Profile` witness. |
| same | `cournot_q2_q2_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.cournotDuopoly_bothQuantityTwo_isNash` | focused build | The theorem survives; `cournotDuopoly_nashCount` machine-refutes the pinned prose claim of uniqueness and records three equilibria and payoff two at `(2,2)`. |
| same | `BraessRAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 446 |
| same | `BraessAAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 450 |
| same | `braessRestricted` | def | unreviewed | review required | generated index seed only | public, pinned line 455 |
| same | `braessAugmented` | def | unreviewed | review required | generated index seed only | public, pinned line 466 |
| same | `braessRestricted_aa_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 486 |
| same | `braessAugmented_cc_is_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 494 |
| same | `braessAugmented_aa_not_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 502 |
| same | `braess_welfare_decreases` | theorem | unreviewed | review required | generated index seed only | public, pinned line 516 |
| same | `BertrandPrice` | inductive | adapt | `GameTheory.Examples.Economic.Price` | focused build | Canonical descriptive action type. |
| same | `BertrandPrice.toReal` | def | adapt | `GameTheory.Examples.Economic.Price.value` | focused build | Exact value is sufficient in `ℚ`; no analytic scalar is needed. |
| same | `bertrandProfit` | def | adapt | `GameTheory.Examples.Economic.bertrandProfit` | focused build | Every payoff is multiplied by two, preserving preferences while avoiding kernel reduction over `1/2`. |
| same | `bertrandDuopoly` | def | adapt | `GameTheory.Examples.Economic.bertrandDuopoly` | focused build | Canonical symmetric `TableGame`. |
| same | `bertrand_p2_p2` | def | adapt | `GameTheory.Examples.Economic.bothPriceTwo` | focused build | Canonical `Profile` witness. |
| same | `bertrand_p1_p1` | def | adapt | `GameTheory.Examples.Economic.bothPriceOne` | focused build | Canonical `Profile` witness. |
| same | `bertrand_p2_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.bertrandDuopoly_bothPriceTwo_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `bertrand_p1_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.bertrandDuopoly_bothPriceOne_isNash` | focused build | Published against canonical semantic `IsNash`. |
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
