# T4: one-shot NFG to FOSG compilation

Title: One-shot normal-form game as a factored-observation stochastic game
Family ID: T4
Pinned roots: `GameTheory/Languages/NFG/Syntax.lean`;
`GameTheory/Languages/NFG/Compile.lean`;
`GameTheory/Languages/Bridges/NFG_FOSG.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: working tree based on `2b659df`
Canonical destinations: `GameTheory.Languages.NFG`;
`GameTheory.Languages.FOSG`; a named direct bridge between them
Domain contract / decision: D0, D4, D6, D7, EXP-042
Owner: Wave 1 / named language transfers
Status: complete
Last verified: 2026-07-30

The frozen claim is not the whole 31-file predecessor closure. Its mathematical
content is a deterministic one-step simultaneous move, a lift of every source
action profile to information-local target policies, and equality of the
resulting outcome and utility laws. The successor must express the move with
the accepted general-state Protocol interface: D6 proved that serializing a
simultaneous move as a single-mover tree strictly enlarges the strategy space.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Languages/NFG/Syntax.lean` | `NFGGame` | structure | adapt | `GameTheory.Languages.NFG.Game` | EXP-042; full build | Keeps action syntax and deterministic outcome. Utility and capabilities remain operation-local. |
| same | `StrategyProfile` | abbreviation | subsume | `Profile` of the compiled signature | D1 | The source action family is the compiled strategy family definitionally. |
| same | `deviate`, `deviate_same`, `deviate_other` | definition/theorems | retire | `Profile.update` | D1/D5 | The stable profile implementation already owns the only point update. |
| same | `IsNashPure`, `IsDominant`, `dominant_is_nash` | solution family | retire as language API | canonical Core predicates and later theorem recovery | D4/D5 | T4 must not create a second Nash API. Mathematical results may be adapted after the frontend gate. |
| `Languages/NFG/Compile.lean` | `NFGGame.toKernelGame` | compiler | adapt | `NFG.Game.toGameForm` | D1/D2/D4 | Deterministic play is `FinDist.pure`; utilities remain a separate evaluation. |
| same | `toKernelGame_outcomeKernel` | theorem | adapt | `NFG.Game.toGameForm_play` | EXP-042 | This is the direct source-side equation used by T4. |
| same | `IsNashPure_iff_kernelGame`, `IsDominant_iff_kernelGame` | bridge theorems | retire | definitional use of Core predicates | D5 | There is no source duplicate to bridge. |
| same | `toKernelGame_udist` | theorem | subsume | direct outcome-law theorem plus `expectedUtility_pure` | D2/D4 | A joint utility distribution is not a second primitive in the successor. |
| same | mixed definitions and bridge | definitions/theorems | subsume | `GameForm.mixed` and its existing laws | D2/D5 | T4 is pure and one-shot; later NFG recovery reuses the canonical mixed extension. |
| `Languages/Bridges/NFG_FOSG.lean` | `actionsOfJoint` | definition | adapt privately | `NFG.OneShotFOSG.State.actionOfJoint` | hostile slice | Consumes only a certified legal simultaneous joint action; no default action or padding value. |
| same | `toFOSG` | definition | adapt | `NFG.OneShotFOSG.game` | EXP-042 | Target state retains the source profile; observations and menus compile through Protocol rather than redefining execution. |
| same | terminal/active/transition/bounded-horizon lemmas | theorem family | adapt minimally | `active_initial`; `runFor_chooserOfProfile_one` | EXP-042 | Horizon one follows from the named run law; no stored horizon certificate. |
| same | history/view helper lemmas | theorem family | subsume | canonical `Trace`, `History`, and `InformationModel` laws | D6 | Do not recover a parallel FOSG history evaluator. |
| same | `liftBehavioral`, `jointActionOf`, `liftProfile` | definitions | adapt | `Policy.ofAction`; `policyProfile`; `chooserOfProfile` | EXP-042 | The lift preserves source players and action types; all players act at the same target history. |
| same | `toFOSG_legalActionLaw_nil`, transition-support, `oneStepHistory`, `toFOSG_runDist_one` | laws/helpers | adapt minimally | `historyChooser_policyProfile`; `runFor_chooserOfProfile_one` | EXP-042 | Uses the actual Protocol/Information runner. |
| same | `toFOSG_oneStepHistory_utility` | theorem | subsume | outcome preservation plus utility pullback | D4 | Utilities do not belong in execution syntax. |
| same | `toFOSG_udist_eq` | theorem | adapt | `toProtocolForm_play_policyProfile`; `toProtocolForm_utilityLaw_policyProfile` | D0/T4/EXP-042 | Exact equality for canonical finite outcome laws and every external utility. |
| same | `toFOSG_morphism` | certificate wrapper | retire | direct named theorems | D7/D15 | The wrapper adds no composition consumer; T4 credits the named equalities. |

Attribution: the predecessor supplies the one-step encoding, all-player profile
lift, and exact preservation target. The successor deliberately does not copy
its `KernelGame`, FOSG history/evaluator, language-specific solution concepts,
or morphism hierarchy.

Completion requires all of the following:

1. a transparent NFG syntax whose compiler is the canonical deterministic
   `GameForm`, with no solution-concept import;
2. a FOSG frontend that owns factored observations but delegates execution,
   histories, information-local policies, and strategic compilation to
   Protocol;
3. a hostile simultaneous-action example proving that every source player acts
   at the same history and that no policy sees an opponent's current action;
4. a lifted source profile whose actual compiled target law, mapped back to the
   NFG outcome, is exactly the source play law;
5. source, import, axiom, focused-build, full-build, and Phase 3 audit evidence.

All five conditions pass. The stable split is:

- `GameTheory.Languages.NFG`: deterministic syntax and canonical static
  compiler;
- `GameTheory.Languages.FOSG`: the transparent execution/information
  specialization and its delegated compiler;
- `GameTheory.Languages.Bridges.NFGFOSG`: the named one-shot construction and
  exact outcome/utility laws.

`Experimental/PostArchitecture/NFGFOSGTest.lean` retains the hostile
two-player witness. Both source players are active initially; changing only the
column action leaves the row policy action unchanged while changing the
terminal outcome.

Validation:

```text
lake build GameTheory.Languages.NFG GameTheory.Languages.FOSG
lake build GameTheory.Languages.Bridges.NFGFOSG
lake build GameTheory.Experimental.PostArchitecture.NFGFOSGTest
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

The focused build is 1,724 jobs and the full build 3,341. The Phase 3 positive
and negative probes report NFG boundary/input counts `2/3`, FOSG
solution/input counts `2/3`, and four reached bridge inputs. Source audits find
zero placeholders, custom axioms, direct updates, transports, or forbidden
imports. The two generic laws and hostile probes use only `propext`,
`Classical.choice`, and `Quot.sound`.
