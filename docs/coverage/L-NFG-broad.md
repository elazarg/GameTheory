# L-NFG: Broad normal-form language and examples

Title: Broad normal-form language and examples
Family ID: L-NFG
Pinned roots: `GameTheory/Languages/NFG/CheapTalkExamples.lean`; `GameTheory/Languages/NFG/Compile.lean`; `GameTheory/Languages/NFG/CountableExample.lean`; `GameTheory/Languages/NFG/Examples.lean`; `GameTheory/Languages/NFG/MatchingPenniesMixed.lean`; `GameTheory/Languages/NFG/PublicGoods.lean`; `GameTheory/Languages/NFG/Stackelberg.lean`; `GameTheory/Languages/NFG/Syntax.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `01f790a`
Canonical destination: GameTheory.Languages.NFG; GameTheory.Examples; canonical Core and Analysis concepts
Domain contract / decision: D4-D10, D15, EXP-042
Owner: Wave 2 / mature static and language recovery
Status: complete; 108/108 reviewed, no deferred rows
Last verified: 2026-08-02

This ledger is an exact generated review queue for the L-NFG family.
18 declarations are already accounted for in
earlier bounded ledgers and are not duplicated here. Every row below is
initially seeded as `unreviewed`: the generated index supplies spelling,
location, kind, and visibility only. It does not infer a mathematical
disposition. Reviewed rows replace that seed with explicit evidence.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Languages/NFG/CheapTalkExamples.lean` | `extension` | def | adapt | `GameTheory.Examples.CheapTalk.battleMessages` | EXP-046/D18; full build (3,361 jobs) | The concrete message extension uses the canonical static construction; staged messaging remains Protocol-owned. |
| same | `game` | abbrev | adapt | `GameTheory.Examples.CheapTalk.battleMessages.form` | EXP-046/D18; full build (3,361 jobs) | The extension's `GameForm` is transparent and does not introduce an NFG-local evaluator. |
| same | `opera_babbling_nash` | theorem | adapt | `GameTheory.Examples.CheapTalk.battleOfTheSexes_opera_babbling_isNash` | EXP-046/D18; full build (3,361 jobs) | Recovered through `GameForm.CheapTalkExtension.babbling_isNash` and ordinary `IsNash`. |
| same | `football_babbling_nash` | theorem | adapt | `GameTheory.Examples.CheapTalk.battleOfTheSexes_football_babbling_isNash` | EXP-046/D18; full build (3,361 jobs) | Second concrete witness of the same generic theorem. |
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
| same | `BraessRAction` | inductive | adapt | `GameTheory.Examples.Economic.RestrictedRoute` | focused build | Canonical descriptive pre-shortcut action type. |
| same | `BraessAAction` | inductive | adapt | `GameTheory.Examples.Economic.AugmentedRoute` | focused build | Canonical descriptive post-shortcut action type. |
| same | `braessRestricted` | def | adapt | `GameTheory.Examples.Economic.braessRestricted` | focused build | Exact rational `TableGame`. |
| same | `braessAugmented` | def | adapt | `GameTheory.Examples.Economic.braessAugmented` | focused build | Exact rational `TableGame`; the dominant-profile checker confirms the shortcut claim. |
| same | `braessRestricted_aa_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.braessRestrictedAA_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `braessAugmented_cc_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.braessAugmentedCC_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `braessAugmented_aa_not_nash` | theorem | adapt | `GameTheory.Examples.Economic.braessAugmentedAA_not_isNash` | focused build | Canonical semantic refutation. |
| same | `braess_welfare_decreases` | theorem | adapt | `GameTheory.Examples.Economic.braessWelfareDecreases` | focused build | Exact equilibrium welfare comparison, six versus four. |
| same | `BertrandPrice` | inductive | adapt | `GameTheory.Examples.Economic.Price` | focused build | Canonical descriptive action type. |
| same | `BertrandPrice.toReal` | def | adapt | `GameTheory.Examples.Economic.Price.value` | focused build | Exact value is sufficient in `ℚ`; no analytic scalar is needed. |
| same | `bertrandProfit` | def | adapt | `GameTheory.Examples.Economic.bertrandProfit` | focused build | Every payoff is multiplied by two, preserving preferences while avoiding kernel reduction over `1/2`. |
| same | `bertrandDuopoly` | def | adapt | `GameTheory.Examples.Economic.bertrandDuopoly` | focused build | Canonical symmetric `TableGame`. |
| same | `bertrand_p2_p2` | def | adapt | `GameTheory.Examples.Economic.bothPriceTwo` | focused build | Canonical `Profile` witness. |
| same | `bertrand_p1_p1` | def | adapt | `GameTheory.Examples.Economic.bothPriceOne` | focused build | Canonical `Profile` witness. |
| same | `bertrand_p2_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.bertrandDuopoly_bothPriceTwo_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `bertrand_p1_is_nash` | theorem | adapt | `GameTheory.Examples.Economic.bertrandDuopoly_bothPriceOne_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `pd_defect_udist` | theorem | adapt | `GameTheory.Examples.prisonersDilemma_bothDefect_play` | focused build | Canonical deterministic `GameForm` law; no `KernelGame` wrapper. |
| same | `pd_defect_isNashFor_eu` | theorem | retired | `GameTheory.Examples.prisonersDilemma_bothDefect_isNash` | D5; focused build | `IsNashFor euPref` was a parallel predicate wrapper; expected-utility Nash is the canonical `IsNash` specialization. |
| same | `pd_defect_isDominantFor_eu` | theorem | retired | `GameTheory.Examples.prisonersDilemma_defect_isDominant` | D5; focused build | Canonical `IsDominant` replaces the `KernelGame.IsDominantFor` wrapper. |
| `GameTheory/Languages/NFG/MatchingPenniesMixed.lean` | `<anonymous@32>` | instance | retired | `GameTheory.Examples.Side.heads` | focused build | Private nonemptiness plumbing; the concrete constructor is available where needed. |
| same | `matchingPenniesOutcomeFintype` | instance | retired | `GameTheory.Finite.TableGame.instFintypeProfile` | D9; focused build | The executable table carries its authoritative finite strategy capabilities; semantic outcomes do not store them. |
| same | `matchingPenniesOutcomeFinite` | instance | retired | `GameTheory.Finite.TableGame.instFintypeProfile` | D9; focused build | Duplicate private bridge from `Fintype` to `Finite`. |
| same | `matchingPenniesStrategyNonempty` | instance | retired | `GameTheory.Examples.Side.heads` | focused build | Private instance required only by the predecessor's generic wrapper. |
| same | `matchingPenniesStrategyFintype` | instance | retired | `GameTheory.Finite.TableGame.instFintypeAction` | D9; focused build | The finite capability is authoritative data of `TableGame`. |
| same | `matchingPenniesLabels` | def | retired | `GameTheory.Examples.Side`; `pennyProfile` | focused build | Private Boolean-label adapter for a predecessor calculus; the canonical example uses its action type directly. |
| same | `matchingPennies_matchingPenniesLike` | def | retired | `matchingPennies_payoff`; `uniformPennies_verify` | focused build | Private certificate for the predecessor binary wrapper; direct payoff equations and verified exact arithmetic are authoritative. |
| same | `matchingPenniesFairMixed` | def | adapt | `GameTheory.Examples.fairPennies`; `uniformPennies` | focused build | Named semantic profile compiled from exact rational half/half weights. |
| same | `matchingPennies_uniform_mixed_balanced` | theorem | adapt | `uniformPennies_expectedPayoff_zero`; `uniformPennies_pureDeviation_expectedPayoff_zero` | focused build | Both the status quo and every pure deviation have exact payoff zero. |
| same | `matchingPennies_mixed_nash_iff_half` | theorem | adapt | `GameTheory.Examples.matchingPennies_mixed_isNash_iff_half` | S-MIX binary ledger; focused build (1,740 jobs) | Instantiates `GameForm.MatchingPenniesLike.isNash_iff_half` over the canonical mixed extension; no `IsNashMixed` wrapper. |
| same | `matchingPennies_fair_mixed_nash` | theorem | adapt | `GameTheory.Examples.fairPennies_isNash` | focused build | Published against `IsNash` of the canonical mixed extension. |
| same | `matchingPenniesLabels_uniform_eq_fair` | theorem | retired | `GameTheory.Examples.fairPennies` | focused build | Private equality between two predecessor presentations; the successor names one canonical semantic profile. |
| same | `matchingPennies_fair_correlated_eq` | theorem | adapt | `GameTheory.Examples.matchingPennies_fair_isCorrelatedEq` | S-CORR mixed-Nash ledger; focused build (1,739 jobs) | Concrete consumer of the preference-parametric `GameTheory.IsNash.isCorrelatedEq_pi`; no example-local transport proof. |
| same | `matchingPennies_correlated_eq_unique` | theorem | adapt | `GameTheory.Examples.matchingPennies_correlatedEq_unique` | S-ZERO constant-sum correlation ledger; focused build (1,741 jobs) | Instantiates the language-independent `GameForm.MatchingPenniesLike.correlatedEq_unique` theorem on the canonical table. |
| same | `matchingPennies_correlated_eq_iff` | theorem | adapt | `GameTheory.Examples.matchingPennies_isCorrelatedEq_iff` | S-ZERO constant-sum correlation ledger; focused build (1,741 jobs) | Combines the unique-law theorem with the preference-parametric mixed-Nash-to-CE bridge. |
| `GameTheory/Languages/NFG/PublicGoods.lean` | `publicGoods_freeRide_dominant` | theorem | adapt | `GameTheory.Examples.Economic.publicGoods_freeRide` | focused build | Uses the named `removeContribution` operation instead of a raw function update; the parametric inequality is unchanged. |
| same | `publicGoods_cooperation_pareto` | theorem | adapt | `GameTheory.Examples.Economic.publicGoods_cooperationPareto` | focused build | Parametric cooperation-versus-defection payoff theorem recovered. |
| `GameTheory/Languages/NFG/Stackelberg.lean` | `StackelbergGame` | structure | retired | `GameTheory.Protocol.Tree`; `GameTheory.Finite.TableGame` | D0/D5/D6; focused build | The parallel wrapper mixed sequential commitment and simultaneous semantics; the successor example presents each through its canonical root. |
| same | `followerBR` | def | retired | `GameTheory.IsBestResponse`; `ExecutionProtocol.IsOneShotOptimal`; `followerResponse_optimal` | D5/D6; focused build | Best response is already canonical; no Stackelberg-local solution predicate is retained. |
| same | `stackelbergPayoff` | def | retired | `ExecutionProtocol.backwardValue`; `GameTheory.Examples.Stackelberg.commitmentValue` | D6; focused build | General sequential value belongs to Protocol; the finite example's closed form is named locally. |
| same | `IsStackelbergEq` | def | retired | `GameTheory.Protocol.Tree.PureStrategy`; `fight_maximizes_commitment` | D5/D6; focused build | A second equilibrium predicate would duplicate the validated sequential optimality surface. |
| same | `IsSimNash` | def | retired | `GameTheory.IsNash` | D5; focused build | Simultaneous Nash is the canonical static predicate. |
| same | `stackelberg_leader_ge_commitment` | theorem | adapt | `GameTheory.Examples.Stackelberg.leaderPayoff_ge_of_maximizes` | focused build | Generic mathematical projection retained without the retired wrapper. |
| same | `followerBR_at_nash_unique` | theorem | adapt | `GameTheory.Examples.Stackelberg.response_eq_of_unique` | focused build | Generic uniqueness argument retained without either parallel predicate. |
| same | `toKernelGame` | def | retired | `GameTheory.Finite.TableGame.toForm` | D0/D5; focused build | Static compilation is the existing `GameForm` bridge; no `KernelGame` compatibility surface is recreated. |
| same | `fight` | def | adapt | `GameTheory.Examples.Stackelberg.LeaderAction.fight` | focused build | Constructor replaces a Boolean nickname. |
| same | `accommodate` | def | adapt | `GameTheory.Examples.Stackelberg.LeaderAction.accommodate` | focused build | Constructor replaces a Boolean nickname. |
| same | `enter` | def | adapt | `GameTheory.Examples.Stackelberg.FollowerAction.enter` | focused build | Constructor replaces a Boolean nickname. |
| same | `stayOut` | def | adapt | `GameTheory.Examples.Stackelberg.FollowerAction.stayOut` | focused build | Constructor replaces a Boolean nickname. |
| same | `uL` | def | adapt | `GameTheory.Examples.Stackelberg.leaderPayoff` | focused build | Exact integer payoffs represented in `ℚ`. |
| same | `uF` | def | adapt | `GameTheory.Examples.Stackelberg.followerPayoff` | focused build | Exact integer payoffs represented in `ℚ`. |
| same | `game` | def | adapt | `GameTheory.Examples.Stackelberg.entryTree`; `simultaneousGame` | focused build | Sequential commitment and simultaneous comparison are explicit canonical presentations. |
| same | `br` | def | adapt | `GameTheory.Examples.Stackelberg.followerResponse` | focused build | Contingent follower strategy used directly by the tree plan. |
| same | `br_isBR` | theorem | adapt | `GameTheory.Examples.Stackelberg.followerResponse_optimal` | focused build | Best-response inequalities proved after every possible commitment. |
| same | `game_stackelberg_eq_fight` | theorem | adapt | `GameTheory.Examples.Stackelberg.fight_maximizes_commitment`; `eval_entryPlan` | focused build | The tree realizes the response-contingent plan and fighting maximizes its leader value. |
| same | `game_simNash_accommodate` | theorem | adapt | `GameTheory.Examples.Stackelberg.accommodateEnter_isNash` | focused build | Published against canonical semantic `IsNash`. |
| same | `game_br_at_accommodate` | theorem | adapt | `GameTheory.Examples.Stackelberg.followerResponse_accommodate` | focused build | Definitional response equation retained. |
| same | `leader_advantage` | theorem | adapt | `GameTheory.Examples.Stackelberg.leaderAdvantage` | focused build | Weak comparison derived from the strict theorem. |
| same | `leader_advantage_strict` | theorem | adapt | `GameTheory.Examples.Stackelberg.leaderAdvantage_strict` | focused build | Commitment value two is strictly above simultaneous-equilibrium payoff one. |

Before this ledger can become complete, each row must be reviewed against
the canonical successor API and assigned an allowed non-`unreviewed`
disposition with concrete build, theorem, decision, or counterexample
evidence. Generated name similarity is never sufficient.
