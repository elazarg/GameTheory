module

/-
# Weak perfect Bayesian equilibrium need not be subgame perfect

A player exits before a fair hidden bit is drawn. At the unreached guessing
site, a belief concentrated on false justifies guessing false. The entered
chance continuation is nevertheless a proper subgame where guessing true is
strictly better. All payoffs are nonpositive, so exiting is optimal even
against whole-policy replacements.
-/

public import GameTheory.Protocol.WeakPBE
public import GameTheory.Protocol.SubgamePerfect
public import GameTheory.Math.Probability.Mixture
public import GameTheory.Math.Probability.ExpectationMixture

@[expose] public section

noncomputable section

namespace GameTheory.Tests.WeakPBESeparation

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

inductive Stage
  | root | chance | guess | terminal
  deriving DecidableEq

inductive State
  | root | chance | guess (latent : Bool) | exited | done (latent action : Bool)
  deriving DecidableEq

def State.stage : State → Stage
  | .root => .root
  | .chance => .chance
  | .guess _ => .guess
  | .exited | .done _ _ => .terminal

def State.terminal : State → Prop
  | .exited | .done _ _ => True
  | _ => False

def State.active : State → Prop
  | .root | .guess _ => True
  | _ => False

def coin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

theorem mem_support_coin (bit : Bool) : bit ∈ coin.support := by
  cases bit
  · exact mem_support_mix_left (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by simp)
  · exact mem_support_mix_right (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by simp)

def action (joint : Unit → Option Bool) : Bool := (joint ()).getD false

@[reducible]
def arena : ExecutionProtocol Unit where
  State := State
  Action _ := Bool
  init := .root
  active state _ := state.active
  available _ _ := Set.univ
  terminal := State.terminal
  step state joint := match state with
    | .root => PMF.pure (if action joint.1 then .chance else .exited)
    | .chance => coin.map State.guess
    | .guess latent => PMF.pure (.done latent (action joint.1))
    | .exited => PMF.pure .exited
    | .done latent chosen => PMF.pure (.done latent chosen)
  progress := by
    intro state running
    cases state with
    | root => exact ⟨fun _ => some false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
    | chance => exact ⟨fun _ => none, fun _ => by simp [State.active]⟩
    | guess latent => exact ⟨fun _ => some false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
    | exited => exact False.elim (running trivial)
    | done latent chosen => exact False.elim (running trivial)

@[reducible]
def signals : InfoSignals arena where
  PublicSignal := Stage
  PrivateSignal _ := Unit
  initialPublic := .root
  initialPrivate _ := ()
  publicSignal event := event.target.stage
  privateSignal _ _ := ()
  InfoState _ := Stage
  initInfo _ _ stage := stage
  pushInfo _ _ _ _ stage := stage

theorem infoOf_stage : ∀ {state : State} (trace : arena.Trace state),
    signals.infoOf () trace = state.stage
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def menu : Stage → Set (Option Bool)
  | .root | .guess => {choice | ∃ bit, choice = some bit}
  | .chance | .terminal => {none}

@[reducible]
def model : InformationModel arena where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate := by
    intro who state trace choice
    cases who
    rw [infoOf_stage]
    cases state <;> cases choice <;>
      simp [menu, State.stage, LegalOption, State.active]

def move (bit : Bool) : Unit → Option Bool := fun _ => some bit

theorem root_move_legal (bit : Bool) : arena.Legal .root (move bit) := by
  exact ⟨by simp [State.terminal], fun _ => ⟨trivial, Set.mem_univ _⟩⟩

@[reducible]
def chanceHistory : arena.History :=
  ⟨.chance, .extend .start (move true) (root_move_legal true)
    (by simp [arena, action, move])⟩

theorem chance_noop_legal : arena.Legal .chance arena.noop := by
  exact ⟨by simp [State.terminal], fun _ => by simp [ExecutionProtocol.noop, State.active]⟩

@[reducible]
def guessHistory (bit : Bool) : arena.History :=
  ⟨.guess bit, chanceHistory.trace.extend arena.noop chance_noop_legal
    (by change State.guess bit ∈ (coin.map State.guess).support
        rw [PMF.support_map]; exact ⟨bit, mem_support_coin bit, rfl⟩)⟩

def policy : model.Policy ()
  | .root | .guess => ⟨some false, by simp [menu]⟩
  | .chance | .terminal => ⟨none, by simp [menu]⟩

def profile : Profile model.strategicSignature := fun _ => policy

def payoff (_ : Unit) (history : arena.History) : ℝ :=
  match history.state with
  | .done false true => -1
  | .done true false => -2
  | _ => 0

theorem payoff_nonpos (history : arena.History) : payoff () history ≤ 0 := by
  rcases history with ⟨state, trace⟩
  cases state <;> try rfl
  case done latent chosen => cases latent <;> cases chosen <;> norm_num [payoff]

theorem payoff_bound (history : arena.History) : |payoff () history| ≤ 2 := by
  rcases history with ⟨state, trace⟩
  cases state <;> try norm_num [payoff]
  case done latent chosen => cases latent <;> cases chosen <;> norm_num [payoff]

def State.depth : State → ℕ
  | .root => 0
  | .chance | .exited => 1
  | .guess _ => 2
  | .done _ _ => 3

theorem step_depth {source target : State} {joint : Unit → Option Bool}
    (legal : arena.Legal source joint)
    (realized : target ∈ (arena.step source ⟨joint, legal⟩).support) :
    target.depth = source.depth + 1 := by
  cases source with
  | root =>
      simp only [arena, PMF.mem_support_pure_iff] at realized
      subst target
      cases action joint <;> rfl
  | chance =>
      rw [PMF.support_map] at realized
      obtain ⟨bit, _, rfl⟩ := realized
      rfl
  | guess bit =>
      simp only [arena, PMF.mem_support_pure_iff] at realized
      subst target
      rfl
  | exited => exact False.elim (legal.1 trivial)
  | done bit chosen => exact False.elim (legal.1 trivial)

theorem trace_depth : ∀ {state : State} (trace : arena.Trace state),
    trace.length = state.depth
  | _, .start => rfl
  | _, .extend prior _ legal realized => by
      rw [ExecutionProtocol.Trace.length, trace_depth prior, step_depth legal realized]

theorem wellFoundedHistories : arena.WellFoundedHistories :=
  (wellFoundedPlay_of_rank (E := arena) (fun state : State => 3 - state.depth) (by
    intro source target successor
    obtain ⟨joint, legal, realized⟩ := successor
    have hstep := step_depth legal realized
    cases source <;> cases target <;>
      simp_all [State.depth])).wellFoundedHistories

theorem site_cases (site : model.InformationSite ()) :
    site.1 = .root ∨ site.1 = .guess := by
  obtain ⟨history, _, bit, legal⟩ := site.2
  cases hsite : site.1 <;> simp_all [menu]

theorem information_antichain : model.DecisionInformationAntichain := by
  intro who site first second joint legal target realized fuel reached
  cases who
  have hequal : first.1.state.stage = second.1.state.stage := by
    rw [← infoOf_stage first.1.trace, ← infoOf_stage second.1.trace]
    exact first.2.trans second.2.symm
  have hdepth : first.1.trace.length = second.1.trace.length := by
    rw [trace_depth, trace_depth]
    rcases site_cases site with hsite | hsite
    all_goals
      have hfirst : first.1.state.stage = _ := (infoOf_stage first.1.trace).symm.trans
        (first.2.trans hsite)
      have hsecond : second.1.state.stage = _ := hequal.symm.trans hfirst
      cases hs : first.1.state <;> cases ht : second.1.state <;>
        simp_all [State.stage, State.depth]
  have hle := reached.trace_length_le
  simp only [ExecutionProtocol.History.extend, ExecutionProtocol.Trace.length] at hle
  omega

theorem root_history_unique (history : arena.History) (atRoot : history.state = .root) :
    history = arena.initHistory := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start => rfl
  | extend prior joint legal realized =>
      have hdepth := step_depth legal realized
      change state = .root at atRoot
      rw [atRoot] at hdepth
      simp [State.depth] at hdepth

theorem chance_history_unique (history : arena.History) (atChance : history.state = .chance) :
    history = chanceHistory := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start => contradiction
  | @extend source _ prior joint legal realized =>
      subst atChance
      have hdepth := step_depth legal realized
      cases source <;> simp only [State.depth] at hdepth
      all_goals try omega
      have hprior := root_history_unique ⟨.root, prior⟩ rfl
      have hprior' : prior = .start := by
        cases hprior
        rfl
      subst hprior'
      have haction : action joint = true := by
        cases hbit : action joint <;> simp_all [arena]
      have hjoint : joint = move true := by
        funext who
        cases who
        cases hchoice : joint () with
        | none => simp [action, hchoice] at haction
        | some bit =>
            have : bit = true := by simpa [action, hchoice] using haction
            subst bit
            rfl
      subst hjoint
      rfl

theorem guess_reaches_from_chance (history : arena.History)
    (atGuess : history.state.stage = .guess) :
    arena.HistoryReaches chanceHistory history := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start => contradiction
  | @extend source _ prior joint legal realized =>
      change state.stage = .guess at atGuess
      cases state <;> simp only [State.stage] at atGuess
      all_goals try contradiction
      case guess bit =>
        have hdepth := step_depth legal realized
        cases source <;> simp only [State.depth] at hdepth
        all_goals try omega
        · have hprior := chance_history_unique ⟨.chance, prior⟩ rfl
          have hprior' : prior = chanceHistory.trace := by
            cases hprior
            rfl
          subst hprior'
          exact ⟨1, .step joint legal realized (.refl _ _)⟩
        · exact False.elim (legal.1 trivial)

theorem chance_isSubgameRoot : model.IsSubgameRoot chanceHistory := by
  intro who inside outside reachable running active outsideRunning outsideActive sameInfo
  cases who
  have hstage : inside.state.stage = outside.state.stage := by
    exact (infoOf_stage inside.trace).symm.trans (sameInfo.trans (infoOf_stage outside.trace))
  have hinsideGuess : inside.state.stage = .guess := by
    obtain ⟨fuel, hreach⟩ := reachable
    have hle := hreach.trace_length_le
    rw [trace_depth, trace_depth] at hle
    change (1 : ℕ) ≤ inside.state.depth at hle
    cases hstate : inside.state with
    | root => simp only [hstate, State.depth] at hle; omega
    | chance => simp only [hstate, arena, State.active] at active
    | guess bit => rfl
    | exited => exact False.elim (running (by simp only [hstate, arena, State.terminal]))
    | done bit chosen => exact False.elim (running (by simp only [hstate, arena, State.terminal]))
  exact guess_reaches_from_chance outside (hstage.symm.trans hinsideGuess)

def behavioralProfile : Profile model.behavioralSignature :=
  fun who => (profile who).toBehavioral

def selectedHistory (site : model.InformationSite ()) : model.InformationHistory () site.1 :=
  if atRoot : site.1 = .root then ⟨arena.initHistory, atRoot.symm⟩
  else ⟨guessHistory false, (site_cases site).resolve_left atRoot |>.symm⟩

def assessment : model.BehavioralAssessment where
  strategy := behavioralProfile
  belief who site := by
    cases who
    exact PMF.pure (selectedHistory site)

theorem payoff_integrable (law : PMF arena.History) :
    PayoffIntegrable law (payoff ()) :=
  payoffIntegrable_of_bounded law _ payoff_bound

theorem backwardValue_constant_successors (chooser : arena.HistoryChooser)
    (history : arena.History) (running : ¬ arena.terminal history.state) (value : ℝ)
    (constant : ∀ target
      (realized : target ∈ (arena.step history.state (chooser history running)).support),
      arena.historyBackwardValue wellFoundedHistories chooser (payoff ())
        (history.extend (chooser history running).2 realized) = value) :
    arena.historyBackwardValue wellFoundedHistories chooser (payoff ()) history = value := by
  obtain ⟨_, equation⟩ := arena.historyBackwardValue_of_not_terminal running
    (payoff_integrable _) (fun _ => value)
    (fun target realized _ => (constant target realized).symm)
  simpa only [expect_constant] using equation

theorem incumbent_root_value :
    arena.historyBackwardValue wellFoundedHistories (model.historyChooser profile)
      (payoff ()) arena.initHistory = 0 := by
  apply backwardValue_constant_successors _ _ (by simp [State.terminal]) 0
  intro target realized
  have target_exited : target = .exited := by
    change target ∈ (PMF.pure State.exited).support at realized
    exact (PMF.mem_support_pure_iff _ _).mp realized
  subst target
  rw [arena.historyBackwardValue_of_terminal (by trivial)]
  rfl

theorem incumbent_false_guess_value :
    arena.historyBackwardValue wellFoundedHistories (model.historyChooser profile)
      (payoff ()) (guessHistory false) = 0 := by
  apply backwardValue_constant_successors _ _ (by simp [State.terminal]) 0
  intro target realized
  have target_done : target = .done false false := by
    change target ∈ (PMF.pure (State.done false false)).support at realized
    exact (PMF.mem_support_pure_iff _ _).mp realized
  subst target
  rw [arena.historyBackwardValue_of_terminal (by trivial)]
  rfl

theorem incumbent_context_value (site : model.InformationSite ()) :
    (assessment.continuationContext wellFoundedHistories site (payoff ())).value
      (assessment.strategy ()) = 0 := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value]
  change expect ((PMF.pure (selectedHistory site)).bind _) _ = 0
  rw [PMF.pure_bind]
  have updated : Profile.update (sig := model.behavioralSignature)
      assessment.strategy () (assessment.strategy ()) = behavioralProfile :=
    Profile.update_eq_self _ _
  rw [updated]
  calc
    _ = arena.historyBackwardValue wellFoundedHistories (model.historyChooser profile)
        (payoff ()) (selectedHistory site).1 :=
      congrArg (fun law => expect law (payoff ()))
        (model.runBehavioralTerminalFrom_toBehavioral wellFoundedHistories profile _)
    _ = 0 := by
      unfold selectedHistory
      split
      · exact incumbent_root_value
      · exact incumbent_false_guess_value

theorem assessment_rational :
    assessment.IsSequentiallyRational wellFoundedHistories payoff := by
  intro who site
  cases who
  have integrable (alternative : model.BehavioralPolicy ()) :
      (assessment.continuationContext wellFoundedHistories site (payoff ())).IntegrableAt
        alternative := payoff_integrable _
  apply (Context.isLocallyOptimal_iff_of_integrable (integrable _)
    (fun alternative _ => integrable alternative)).mpr
  intro alternative _
  rw [incumbent_context_value]
  exact expect_le_const _ _ (integrable alternative) 0 (fun history _ => payoff_nonpos history)

@[reducible]
def exitedHistory : arena.History :=
  ⟨.exited, .extend .start (move false) (root_move_legal false)
    (by simp [arena, action, move])⟩

set_option backward.isDefEq.respectTransparency false in
theorem incumbent_run_succ (fuel : ℕ) :
    model.run profile (fuel + 1) = PMF.pure exitedHistory := by
  rw [InformationModel.run, InformationModel.runFrom,
    arena.runHistoryFor_succ_of_not_terminal _ fuel (by simp [State.terminal])]
  change (PMF.pure State.exited).bindOnSupport _ = PMF.pure exitedHistory
  rw [PMF.pure_bindOnSupport]
  exact arena.runHistoryFor_of_terminal _ _ (by trivial)

theorem root_reachWeight :
    model.historyReachWeight behavioralProfile arena.initHistory = 1 := by
  change (PMF.pure arena.initHistory) arena.initHistory = 1
  simp

theorem guess_reachWeight_zero (history : arena.History)
    (atGuess : history.state.stage = .guess) :
    model.historyReachWeight behavioralProfile history = 0 := by
  have depth : history.trace.length = 2 := by
    rw [trace_depth]
    cases hstate : history.state <;> simp_all [State.stage, State.depth]
  have different : history ≠ exitedHistory := by
    intro equal
    have := congrArg (fun history : arena.History => history.state.stage) equal
    rw [atGuess] at this
    contradiction
  unfold InformationModel.historyReachWeight
  rw [depth]
  have run_eq : model.runBehavioral behavioralProfile 2 = model.run profile 2 :=
    model.runBehavioralFrom_toBehavioral profile 2 arena.initHistory
  rw [run_eq, incumbent_run_succ 1]
  simp [PMF.pure_apply, different]

theorem root_fiber_unique (site : model.InformationSite ()) (atRoot : site.1 = .root)
    (history : model.InformationHistory () site.1) :
    history = selectedHistory site := by
  apply Subtype.ext
  have history_root : history.1.state = .root := by
    have stage_eq : history.1.state.stage = .root :=
      (infoOf_stage history.1.trace).symm.trans (history.2.trans atRoot)
    cases hstate : history.1.state <;> simp_all [State.stage]
  rw [root_history_unique history.1 history_root]
  simp [selectedHistory, atRoot]

theorem root_informationMass (site : model.InformationSite ()) (atRoot : site.1 = .root) :
    model.informationMass behavioralProfile () site = 1 := by
  classical
  unfold InformationModel.informationMass
  rw [tsum_eq_single (selectedHistory site)]
  · have selected_eq : (selectedHistory site).1 = arena.initHistory := by
      simp [selectedHistory, atRoot]
    rw [selected_eq, root_reachWeight]
  · intro history different
    exact False.elim (different (root_fiber_unique site atRoot history))

theorem guess_informationMass (site : model.InformationSite ()) (atGuess : site.1 = .guess) :
    model.informationMass behavioralProfile () site = 0 := by
  unfold InformationModel.informationMass
  apply ENNReal.tsum_eq_zero.mpr
  intro history
  apply guess_reachWeight_zero
  exact (infoOf_stage history.1.trace).symm.trans (history.2.trans atGuess)

theorem assessment_bayes :
    InformationModel.BehavioralAssessment.IsBayesConsistent model assessment
      information_antichain := by
  intro who site positive history
  cases who
  rcases site_cases site with atRoot | atGuess
  · have same := root_fiber_unique site atRoot history
    have selected_eq : (selectedHistory site).1 = arena.initHistory := by
      simp [selectedHistory, atRoot]
    change (PMF.pure (selectedHistory site)) history =
      model.historyReachWeight behavioralProfile history.1 /
        model.informationMass behavioralProfile () site
    rw [same, selected_eq, root_reachWeight, root_informationMass site atRoot]
    simp
  · have mass := guess_informationMass site atGuess
    change 0 < model.informationMass behavioralProfile () site at positive
    rw [mass] at positive
    exact False.elim (lt_irrefl _ positive)

/-- Arbitrary off-path beliefs still have to justify every continuation policy. -/
theorem assessment_isWeakPBE :
    assessment.IsWeakPBE information_antichain wellFoundedHistories payoff :=
  ⟨assessment_rational, assessment_bayes⟩

def alternative : model.Policy ()
  | .root => ⟨some false, by simp [menu]⟩
  | .guess => ⟨some true, by simp [menu]⟩
  | .chance | .terminal => ⟨none, by simp [menu]⟩

def respondingProfile (respond : Bool) : Profile model.strategicSignature :=
  if respond then Profile.update profile () alternative else profile

def guessPayoff (latent respond : Bool) : ℝ :=
  if latent then (if respond then 0 else -2) else (if respond then -1 else 0)

theorem responding_guess_value (latent respond : Bool) :
    arena.historyBackwardValue wellFoundedHistories
      (model.historyChooser (respondingProfile respond)) (payoff ())
      (guessHistory latent) = guessPayoff latent respond := by
  cases respond <;> cases latent
  all_goals
    apply backwardValue_constant_successors _ _ (by simp [State.terminal])
    intro target realized
    change target ∈ (PMF.pure _).support at realized
    rw [PMF.mem_support_pure_iff] at realized
    subst target
    rw [arena.historyBackwardValue_of_terminal (by trivial)]
    rfl

theorem expect_coin (f : Bool → ℝ) : expect coin f = (f false + f true) / 2 := by
  rw [coin, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
    expect_pure, expect_pure]
  ring

theorem responding_chance_value (respond : Bool) :
    arena.historyBackwardValue wellFoundedHistories
      (model.historyChooser (respondingProfile respond)) (payoff ()) chanceHistory =
        (guessPayoff false respond + guessPayoff true respond) / 2 := by
  let value : State → ℝ := fun state => match state with
    | .guess latent => guessPayoff latent respond
    | _ => 0
  obtain ⟨_, equation⟩ := arena.historyBackwardValue_of_not_terminal
    (chooser := model.historyChooser (respondingProfile respond))
    (history := chanceHistory) (by simp [State.terminal]) (payoff_integrable _) value (by
      intro target realized _
      change target ∈ (coin.map State.guess).support at realized
      rw [PMF.support_map] at realized
      obtain ⟨latent, _, rfl⟩ := realized
      change guessPayoff latent respond = _
      cases respond
      · exact (responding_guess_value latent false).symm
      · exact (responding_guess_value latent true).symm)
  change _ = expect (coin.map State.guess) value at equation
  rw [expect_map, expect_coin] at equation
  exact equation

/-- The entered continuation is a proper subgame, but the dogmatic off-path
belief assigns probability zero to a chance branch that actually has mass one
half in that subgame. Guessing true raises expected payoff from `-1` to `-1/2`. -/
theorem profile_not_subgamePerfect :
    ¬ model.IsSubgamePerfect wellFoundedHistories profile
      (fun history who => payoff who history) := by
  intro perfect
  have comparison := (perfect chanceHistory chance_isSubgameRoot () alternative).2.2
  rw [arena.historyBackwardExtendedValue_le_iff (payoff_integrable _)
    (payoff_integrable _)] at comparison
  have incumbent : arena.historyBackwardValue wellFoundedHistories
      (model.historyChooser profile) (payoff ()) chanceHistory = -1 := by
    have equation := responding_chance_value false
    norm_num [respondingProfile, guessPayoff] at equation
    exact equation
  have deviating : arena.historyBackwardValue wellFoundedHistories
      (model.historyChooser (Profile.update profile () alternative)) (payoff ()) chanceHistory =
        -(1 / 2) := by
    have equation := responding_chance_value true
    norm_num [respondingProfile, guessPayoff] at equation
    exact equation
  rw [incumbent, deviating] at comparison
  norm_num at comparison

/-- A single assessment witnesses weak PBE while its prescribed pure strategy
fails proper-subgame perfection. -/
theorem weakPBE_not_subgamePerfect :
    assessment.IsWeakPBE information_antichain wellFoundedHistories payoff ∧
      assessment.strategy = (fun who => (profile who).toBehavioral) ∧
      ¬ model.IsSubgamePerfect wellFoundedHistories profile
        (fun history who => payoff who history) :=
  ⟨assessment_isWeakPBE, rfl, profile_not_subgamePerfect⟩

end GameTheory.Tests.WeakPBESeparation
