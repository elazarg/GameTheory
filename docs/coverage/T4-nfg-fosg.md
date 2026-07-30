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
| same | `StrategyProfile` | abbreviation | subsumed | `Profile` of the compiled signature | D1 | The source action family is the compiled strategy family definitionally. |
| same | `deviate` | definition | retired | `Profile.update` | D1/D5 | The stable profile implementation already owns the only point update. |
| same | `deviate_same` | theorem | retired | `Profile.update_same` | D1/D5 | Duplicate wrapper over the canonical operation. |
| same | `deviate_other` | theorem | retired | `Profile.update_of_ne` | D1/D5 | Duplicate wrapper over the canonical operation. |
| same | `IsNashPure` | definition | retired | canonical `IsNash` | D4/D5 | T4 must not create a second Nash API. |
| same | `IsDominant` | definition | retired | canonical `IsDominant` | D4/D5 | T4 must not create a second dominance API. |
| same | `dominant_is_nash` | theorem | subsumed | `IsDominantProfile.isNash` | D4/D5; `Core.Response` build | The generic canonical theorem applies directly after deterministic NFG compilation. |
| `Languages/NFG/Compile.lean` | `NFGGame.toKernelGame` | compiler | adapt | `NFG.Game.toGameForm` | D1/D2/D4 | Deterministic play is `FinDist.pure`; utilities remain a separate evaluation. |
| same | `toKernelGame_outcomeKernel` | theorem | adapt | `NFG.Game.toGameForm_play` | EXP-042 | This is the direct source-side equation used by T4. |
| same | `IsNashPure_iff_kernelGame` | theorem | retired | definitional use of canonical `IsNash` | D5 | There is no source duplicate to bridge. |
| same | `IsDominant_iff_kernelGame` | theorem | retired | definitional use of canonical `IsDominant` | D5 | There is no source duplicate to bridge. |
| same | `toKernelGame_udist` | theorem | subsumed | direct outcome-law theorem plus finite-law mapping | D2/D4 | A joint utility distribution is not a second primitive in the successor. |
| same | `MixedProfile` | abbreviation | subsumed | `Profile G.toGameForm.sig.mixed` | D2/D5 | The canonical mixed signature supplies the strategy family. |
| same | `NFGGame.toMixedKernelGame` | definition | subsumed | `GameForm.mixed` | D2/D5 | One canonical mixed extension. |
| same | `NFGGame.toMixedKernelGame_eq_mixedExtension` | theorem | subsumed | definitional equality of `GameForm.mixed` | D2/D5 | The predecessor wrapper disappears. |
| same | `IsNashMixed` | definition | retired | canonical `IsNash` on `GameForm.mixed` | D5 | No language-specific mixed-Nash predicate. |
| same | `NFGGame.toMixed_morphism` | definition | retired | `GameForm.mixed_play_purify` | D7 | A generic morphism wrapper is not needed for the point-mass law. |
| `Languages/Bridges/NFG_FOSG.lean` | `actionsOfJoint` | definition | adapt | `NFG.OneShotFOSG.State.actionOfJoint` | hostile slice | Private successor helper; consumes only a certified legal simultaneous joint action. |
| same | `toFOSG` | definition | adapt | `NFG.OneShotFOSG.game` | EXP-042 | Target state retains the source profile; observations and menus compile through Protocol rather than redefining execution. |
| same | `toFOSG_boundedHorizon` | theorem | adapt | `runFor_chooserOfProfile_one` | EXP-042 | Horizon one follows from the named run law; no stored horizon certificate. |
| same | `toFOSG_history_eq_nil_of_playerView_nil` | theorem | subsumed | canonical `Trace`/`InformationModel` history view | D6 | No parallel FOSG history evaluator. |
| same | `toFOSG_lastState_true_of_steps_ne_nil` | theorem | subsumed | `runFor_chooserOfProfile_one` | D6/EXP-042 | Terminal state retains the profile rather than a Boolean flag. |
| same | `liftBehavioral` | definition | adapt | `Policy.ofAction` | EXP-042 | Source action becomes an information-local target policy. |
| same | `jointActionOf` | definition | adapt | `chooserOfProfile` | EXP-042 | The all-player joint action is constructed without padding. |
| same | `actionsOfJoint_jointActionOf` | theorem | adapt | `State.actionOfJoint_some` | EXP-042 | Certified decoding recovers every coordinate. |
| same | `liftProfile` | definition | adapt | `policyProfile` | EXP-042 | The lift preserves source players and action types. |
| same | `toFOSG_legalActionLaw_nil` | theorem | adapt | `historyChooser_policyProfile` | EXP-042 | Uses the actual information-local chooser. |
| same | `instDecidablePredToFOSGTerminal` | instance | retired | target terminality reduces by cases | D9 | No stored or public decidability capability is needed. |
| same | `instFintypeToFOSGHistory` | instance | retired | operation-local finite history capability | D9 | T4 uses the runner directly and needs no history enumeration. |
| same | `toFOSG_transition_init_support` | theorem | subsumed | `FinDist.support_pure` on the named execution | EXP-042 | General finite-law fact. |
| same | `oneStepHistory` | definition | retired | canonical Protocol history generated by the runner | D6 | No second history constructor. |
| same | `toFOSG_runDist_one` | theorem | adapt | `runFor_chooserOfProfile_one`; `historyChooser_policyProfile` | EXP-042 | Uses the actual Protocol/Information runner. |
| same | `toFOSG_oneStepHistory_utility` | theorem | subsumed | outcome preservation plus utility mapping | D4 | Utilities do not belong in execution syntax. |
| same | `toFOSG_udist_eq` | theorem | adapt | `toProtocolForm_play_policyProfile`; `toProtocolForm_utilityLaw_policyProfile` | D0/T4/EXP-042 | Exact equality for canonical finite outcome laws and every external utility. |
| same | `toFOSG_morphism` | certificate wrapper | retired | direct named theorems | D7/D15 | The wrapper adds no composition consumer; T4 credits the named equalities. |

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
