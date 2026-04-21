import Mathlib.Algebra.BigOperators.Ring.Finset
import GameTheory.Languages.FOSG.Strategy
import GameTheory.Languages.FOSG.Values

/-!
# GameTheory.Languages.FOSG.Execution

Profile-induced execution weights for realized FOSG histories.
-/

namespace GameTheory

open Math.Probability
open scoped BigOperators

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

namespace History

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Extend a realized prefix history by a chained list of realized steps. -/
def extendBySteps (pref : G.History) :
    (es : List G.Step) → G.StepChainFrom pref.lastState es → G.History
  | [], _ => pref
  | e :: es, hchain =>
      extendBySteps (pref.appendStep e hchain.1) es (by
        simpa using hchain.2)

@[simp] theorem extendBySteps_nil
    (pref : G.History) :
    extendBySteps pref [] trivial = pref := rfl

@[simp] theorem extendBySteps_cons
    (pref : G.History) (e : G.Step) (es : List G.Step)
    (hchain : G.StepChainFrom pref.lastState (e :: es)) :
    extendBySteps pref (e :: es) hchain =
      extendBySteps (pref.appendStep e hchain.1) es (by
        simpa using hchain.2) := rfl

@[simp] theorem steps_extendBySteps
    (pref : G.History) (es : List G.Step)
    (hchain : G.StepChainFrom pref.lastState es) :
    (extendBySteps pref es hchain).steps = pref.steps ++ es := by
  induction es generalizing pref with
  | nil =>
      simp [extendBySteps]
  | cons e es ih =>
      rcases hchain with ⟨hsrc, htail⟩
      simpa [extendBySteps, List.append_assoc] using
        ih (pref := pref.appendStep e hsrc) (hchain := by
          simpa using htail)

@[simp] theorem lastState_extendBySteps
    (pref : G.History) (es : List G.Step)
    (hchain : G.StepChainFrom pref.lastState es) :
    (extendBySteps pref es hchain).lastState = G.lastStateFrom pref.lastState es := by
  induction es generalizing pref with
  | nil =>
      simp [extendBySteps, History.lastState, FOSG.lastStateFrom]
  | cons e es ih =>
      rcases hchain with ⟨hsrc, htail⟩
      simpa [extendBySteps, FOSG.lastStateFrom, hsrc] using
        ih (pref := pref.appendStep e hsrc) (hchain := by
          simpa using htail)

@[simp] theorem extendBySteps_eq
    (h : G.History) :
    extendBySteps (History.nil G) h.steps (by
      simpa [History.lastState, History.nil] using h.chain) = h := by
  apply History.ext
  simp [steps_extendBySteps]

end History

variable [Fintype ι]

/-- Two behavioral profiles agree off player `i` if all other players have the
same behavioral strategy. -/
def AgreeOff
    (G : FOSG ι W Act PrivObs PubObs)
    (σ τ : BehavioralProfile G) (i : ι) : Prop :=
  ∀ j, j ≠ i → σ j = τ j

/-- Probability of the strategic action choices taken in a realized step from a
given realized prefix history. -/
noncomputable def stepActionProb
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (pref : G.History) (e : G.Step) : ENNReal :=
  ∏ i, match e.ownAction? i with
    | some ai => (σ i (pref.playerView i)) ai
    | none => 1

/-- Player `i`'s own strategic contribution to the realized step weight. -/
noncomputable def playerStepActionProb
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (pref : G.History) (e : G.Step) (i : ι) : ENNReal :=
  match e.ownAction? i with
  | some ai => (σ i (pref.playerView i)) ai
  | none => 1

/-- The contribution of every player except `i` to the realized step's
strategic action weight. -/
noncomputable def othersStepActionProb
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (pref : G.History) (e : G.Step) (i : ι) : ENNReal :=
  Finset.prod (Finset.univ.erase i) fun j =>
    match e.ownAction? j with
    | some aj => (σ j (pref.playerView j)) aj
    | none => 1

/-- Probability weight of a realized step: strategic action weight times the
transition kernel weight. -/
noncomputable def stepProb
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (pref : G.History) (e : G.Step) : ENNReal :=
  G.stepActionProb σ pref e * (G.transition e.src e.act) e.dst

@[simp] theorem stepProb_eq_stepActionProb_mul_transition
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (pref : G.History) (e : G.Step) :
    G.stepProb σ pref e =
      G.stepActionProb σ pref e * (G.transition e.src e.act) e.dst := rfl

theorem stepProb_eq_transition_mul_stepActionProb
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (pref : G.History) (e : G.Step) :
    G.stepProb σ pref e =
      (G.transition e.src e.act) e.dst * G.stepActionProb σ pref e := by
  simp [stepProb, mul_comm]

theorem stepActionProb_eq_player_mul_others
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (pref : G.History) (e : G.Step) (i : ι) :
    G.stepActionProb σ pref e =
      G.playerStepActionProb σ pref e i * G.othersStepActionProb σ pref e i := by
  classical
  unfold stepActionProb playerStepActionProb othersStepActionProb
  rw [← Finset.insert_erase (s := Finset.univ) (a := i) (by simp)]
  rw [Finset.prod_insert]
  · simp [mul_comm]
  · simp

theorem stepActionProb_eq_others_mul_player
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (pref : G.History) (e : G.Step) (i : ι) :
    G.stepActionProb σ pref e =
      G.othersStepActionProb σ pref e i * G.playerStepActionProb σ pref e i := by
  rw [G.stepActionProb_eq_player_mul_others σ pref e i, mul_comm]

theorem othersStepActionProb_eq_of_agreeOff
    (G : FOSG ι W Act PrivObs PubObs)
    {σ τ : BehavioralProfile G} {i : ι}
    (hag : G.AgreeOff σ τ i) (pref : G.History) (e : G.Step) :
    G.othersStepActionProb σ pref e i = G.othersStepActionProb τ pref e i := by
  classical
  unfold othersStepActionProb
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [hag j hji]

/-- The continuation factor for counterfactual-style reach: everyone except
player `i`, together with the stochastic transition. -/
noncomputable def counterfactualStepProb
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (i : ι) (pref : G.History) (e : G.Step) : ENNReal :=
  G.othersStepActionProb σ pref e i * (G.transition e.src e.act) e.dst

theorem stepProb_eq_player_mul_counterfactual
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (i : ι) (pref : G.History) (e : G.Step) :
    G.stepProb σ pref e =
      G.playerStepActionProb σ pref e i * G.counterfactualStepProb σ i pref e := by
  calc
    G.stepProb σ pref e
      = (G.playerStepActionProb σ pref e i * G.othersStepActionProb σ pref e i) *
          (G.transition e.src e.act) e.dst := by
            rw [stepProb, G.stepActionProb_eq_player_mul_others]
    _ = G.playerStepActionProb σ pref e i * G.counterfactualStepProb σ i pref e := by
          simp [counterfactualStepProb, mul_assoc]

theorem stepProb_eq_counterfactual_mul_player
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) (i : ι) (pref : G.History) (e : G.Step) :
    G.stepProb σ pref e =
      G.counterfactualStepProb σ i pref e * G.playerStepActionProb σ pref e i := by
  rw [G.stepProb_eq_player_mul_counterfactual σ i pref e, mul_comm]

theorem counterfactualStepProb_eq_of_agreeOff
    (G : FOSG ι W Act PrivObs PubObs)
    {σ τ : BehavioralProfile G} {i : ι}
    (hag : G.AgreeOff σ τ i) (pref : G.History) (e : G.Step) :
    G.counterfactualStepProb σ i pref e = G.counterfactualStepProb τ i pref e := by
  simp [counterfactualStepProb, G.othersStepActionProb_eq_of_agreeOff hag pref e]

namespace History

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Profile-induced weight of a chained suffix of realized steps extending a
realized prefix history. -/
noncomputable def probFrom
    (σ : BehavioralProfile G) (pref : G.History) :
    (es : List G.Step) → G.StepChainFrom pref.lastState es → ENNReal
  | [], _ => 1
  | e :: es, hchain =>
      G.stepProb σ pref e *
        probFrom σ (pref.appendStep e hchain.1) es (by
          simpa using hchain.2)

/-- Player `i`'s own multiplicative contribution to a realized continuation
weight from a given prefix history. -/
noncomputable def playerProbFrom
    (σ : BehavioralProfile G) (i : ι) (pref : G.History) :
    (es : List G.Step) → G.StepChainFrom pref.lastState es → ENNReal
  | [], _ => 1
  | e :: es, hchain =>
      G.playerStepActionProb σ pref e i *
        playerProbFrom σ i (pref.appendStep e hchain.1) es (by
          simpa using hchain.2)

/-- Counterfactual-style continuation weight from a given prefix history:
everyone except player `i`, together with transition probabilities. -/
noncomputable def counterfactualProbFrom
    (σ : BehavioralProfile G) (i : ι) (pref : G.History) :
    (es : List G.Step) → G.StepChainFrom pref.lastState es → ENNReal
  | [], _ => 1
  | e :: es, hchain =>
      G.counterfactualStepProb σ i pref e *
        counterfactualProbFrom σ i (pref.appendStep e hchain.1) es (by
          simpa using hchain.2)

@[simp] theorem probFrom_nil
    (σ : BehavioralProfile G) (pref : G.History) :
    probFrom σ pref [] trivial = 1 := rfl

@[simp] theorem probFrom_cons
    (σ : BehavioralProfile G) (pref : G.History)
    (e : G.Step) (es : List G.Step)
    (hchain : G.StepChainFrom pref.lastState (e :: es)) :
    probFrom σ pref (e :: es) hchain =
      G.stepProb σ pref e *
        probFrom σ (pref.appendStep e hchain.1) es (by
          simpa using hchain.2) := rfl

omit [Fintype ι] in
@[simp] theorem playerProbFrom_nil
    (σ : BehavioralProfile G) (i : ι) (pref : G.History) :
    playerProbFrom σ i pref [] trivial = 1 := rfl

omit [Fintype ι] in
@[simp] theorem playerProbFrom_cons
    (σ : BehavioralProfile G) (i : ι) (pref : G.History)
    (e : G.Step) (es : List G.Step)
    (hchain : G.StepChainFrom pref.lastState (e :: es)) :
    playerProbFrom σ i pref (e :: es) hchain =
      G.playerStepActionProb σ pref e i *
        playerProbFrom σ i (pref.appendStep e hchain.1) es (by
          simpa using hchain.2) := rfl

@[simp] theorem counterfactualProbFrom_nil
    (σ : BehavioralProfile G) (i : ι) (pref : G.History) :
    counterfactualProbFrom σ i pref [] trivial = 1 := rfl

@[simp] theorem counterfactualProbFrom_cons
    (σ : BehavioralProfile G) (i : ι) (pref : G.History)
    (e : G.Step) (es : List G.Step)
    (hchain : G.StepChainFrom pref.lastState (e :: es)) :
    counterfactualProbFrom σ i pref (e :: es) hchain =
      G.counterfactualStepProb σ i pref e *
        counterfactualProbFrom σ i (pref.appendStep e hchain.1) es (by
          simpa using hchain.2) := rfl

theorem counterfactualProbFrom_eq_of_agreeOff
    {σ τ : BehavioralProfile G} {i : ι}
    (hag : G.AgreeOff σ τ i) (pref : G.History)
    (es : List G.Step) (hchain : G.StepChainFrom pref.lastState es) :
    counterfactualProbFrom σ i pref es hchain =
      counterfactualProbFrom τ i pref es hchain := by
  induction es generalizing pref with
  | nil =>
      simp [counterfactualProbFrom]
  | cons e es ih =>
      rw [counterfactualProbFrom_cons, counterfactualProbFrom_cons]
      rw [G.counterfactualStepProb_eq_of_agreeOff hag]
      have htail : G.StepChainFrom (pref.appendStep e hchain.1).lastState es := by
        simpa using hchain.2
      have hrec := ih (pref := pref.appendStep e hchain.1) (hchain := htail)
      simpa [mul_assoc] using
        congrArg (fun x => G.counterfactualStepProb τ i pref e * x) hrec

/-- Profile-induced weight of a realized history. -/
noncomputable def prob
    (σ : BehavioralProfile G) (h : G.History) : ENNReal :=
  probFrom σ (History.nil G) h.steps (by
    simpa [History.lastState, History.nil] using h.chain)

@[simp] theorem prob_nil
    (σ : BehavioralProfile G) :
    prob σ (History.nil G) = 1 := rfl

theorem probFrom_eq_playerProbFrom_mul_counterfactualProbFrom
    (σ : BehavioralProfile G) (i : ι) (pref : G.History)
    (es : List G.Step) (hchain : G.StepChainFrom pref.lastState es) :
    probFrom σ pref es hchain =
      playerProbFrom σ i pref es hchain *
        counterfactualProbFrom σ i pref es hchain := by
  induction es generalizing pref with
  | nil =>
      simp [probFrom, playerProbFrom, counterfactualProbFrom]
  | cons e es ih =>
      rcases hchain with ⟨hsrc, hrest⟩
      have htail : G.StepChainFrom (pref.appendStep e hsrc).lastState es := by
        simpa using hrest
      have hrec := ih (pref := pref.appendStep e hsrc) (hchain := htail)
      rw [probFrom_cons, playerProbFrom_cons, counterfactualProbFrom_cons]
      rw [G.stepProb_eq_player_mul_counterfactual]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        congrArg
          (fun x =>
            G.playerStepActionProb σ pref e i *
              (G.counterfactualStepProb σ i pref e * x))
          hrec

theorem probFrom_append
    (σ : BehavioralProfile G) (pref : G.History)
    (es₁ es₂ : List G.Step)
    (h₁ : G.StepChainFrom pref.lastState es₁)
    (h₂ : G.StepChainFrom (pref.extendBySteps es₁ h₁).lastState es₂) :
    probFrom σ pref (es₁ ++ es₂)
      (FOSG.StepChainFrom.append h₁ (by
        simpa [History.lastState_extendBySteps] using h₂)) =
      probFrom σ pref es₁ h₁ *
        probFrom σ (pref.extendBySteps es₁ h₁) es₂ h₂ := by
  induction es₁ generalizing pref with
  | nil =>
      simp [probFrom, History.extendBySteps]
  | cons e es ih =>
      rcases h₁ with ⟨hsrc, htail⟩
      rw [probFrom_cons]
      have hrec :=
        ih (pref := pref.appendStep e hsrc)
          (h₁ := by simpa using htail)
          (h₂ := h₂)
      simpa [probFrom, History.extendBySteps, hsrc, mul_assoc] using
        congrArg (fun x => G.stepProb σ pref e * x) hrec

theorem probFrom_append_singleton
    (σ : BehavioralProfile G) (pref : G.History)
    (es : List G.Step) (hchain : G.StepChainFrom pref.lastState es)
    (e : G.Step) (hsrc : e.src = G.lastStateFrom pref.lastState es) :
    probFrom σ pref (es ++ [e]) (FOSG.StepChainFrom.snoc hchain e hsrc) =
      probFrom σ pref es hchain * G.stepProb σ (pref.extendBySteps es hchain) e := by
  let htail : G.StepChainFrom (pref.extendBySteps es hchain).lastState [e] := by
    refine And.intro ?_ trivial
    simpa [History.lastState_extendBySteps] using hsrc
  have happend :=
    probFrom_append (G := G) (σ := σ) (pref := pref)
      (es₁ := es) (es₂ := [e]) hchain htail
  simpa [probFrom, History.extendBySteps, mul_comm] using happend

@[simp] theorem prob_snoc
    (σ : BehavioralProfile G)
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    prob σ (h.snoc a dst support) =
      History.prob σ h * G.stepProb σ h ⟨h.lastState, a, dst, support⟩ := by
  simpa [prob, History.snoc] using
    (probFrom_append_singleton (G := G) (σ := σ) (pref := History.nil G)
      (es := h.steps)
      (hchain := by
        simpa [History.lastState, History.nil] using h.chain)
      (e := ⟨h.lastState, a, dst, support⟩)
      (hsrc := by
        simp [History.lastState, History.nil, FOSG.lastStateFrom]))

/-- Player `i`'s own contribution to the realized-history weight. -/
noncomputable def playerProb
    (σ : BehavioralProfile G) (i : ι) (h : G.History) : ENNReal :=
  playerProbFrom σ i (History.nil G) h.steps (by
    simpa [History.lastState, History.nil] using h.chain)

/-- Counterfactual-style realized-history weight for player `i`: everyone
except `i`, together with transition probabilities. -/
noncomputable def counterfactualProb
    (σ : BehavioralProfile G) (i : ι) (h : G.History) : ENNReal :=
  counterfactualProbFrom σ i (History.nil G) h.steps (by
    simpa [History.lastState, History.nil] using h.chain)

theorem counterfactualProb_eq_of_agreeOff
    {σ τ : BehavioralProfile G} {i : ι} (hag : G.AgreeOff σ τ i)
    (h : G.History) :
    History.counterfactualProb σ i h = History.counterfactualProb τ i h := by
  simpa [History.counterfactualProb] using
    counterfactualProbFrom_eq_of_agreeOff (G := G) hag (pref := History.nil G)
      (es := h.steps) (hchain := by
        simpa [History.lastState, History.nil] using h.chain)

theorem prob_eq_playerProb_mul_counterfactualProb
    (σ : BehavioralProfile G) (i : ι) (h : G.History) :
    History.prob σ h =
      History.playerProb σ i h * History.counterfactualProb σ i h := by
  simpa [History.prob, History.playerProb, History.counterfactualProb] using
    probFrom_eq_playerProbFrom_mul_counterfactualProbFrom
      (G := G) (σ := σ) (i := i) (pref := History.nil G)
      (es := h.steps) (hchain := by
        simpa [History.lastState, History.nil] using h.chain)

theorem prob_extendBySteps
    (σ : BehavioralProfile G) (pref : G.History)
    (es : List G.Step) (hchain : G.StepChainFrom pref.lastState es) :
    History.prob σ (pref.extendBySteps es hchain) =
      History.prob σ pref * probFrom σ pref es hchain := by
  simpa [History.prob, History.extendBySteps_eq] using
    (probFrom_append (G := G) (σ := σ) (pref := History.nil G)
      (es₁ := pref.steps) (es₂ := es)
      (h₁ := by
        simpa [History.lastState, History.nil] using pref.chain)
      (h₂ := by
        simpa [History.lastState_extendBySteps, History.lastState, History.nil] using hchain))

theorem prob_appendStep
    (σ : BehavioralProfile G) (h : G.History)
    (e : G.Step) (hsrc : e.src = h.lastState) :
    History.prob σ (h.appendStep e hsrc) =
      History.prob σ h * G.stepProb σ h e := by
  let htail : G.StepChainFrom h.lastState [e] := by
    exact And.intro hsrc trivial
  simpa [History.appendStep, History.extendBySteps, mul_comm] using
    (prob_extendBySteps (G := G) (σ := σ) (pref := h)
      (es := [e]) (hchain := htail))

/-- Terminal-history weight induced by a behavioral profile. This is the
unnormalized terminal-history mass function on realized histories. -/
noncomputable def terminalWeight
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) (h : G.History) : ENNReal :=
  if G.terminal h.lastState then History.prob σ h else 0

@[simp] theorem terminalWeight_of_terminal
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) {h : G.History}
    (hterm : History.IsTerminal h) :
    terminalWeight (G := G) σ h = History.prob σ h := by
  exact if_pos hterm

@[simp] theorem terminalWeight_of_not_terminal
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) {h : G.History}
    (hterm : ¬ History.IsTerminal h) :
    terminalWeight (G := G) σ h = 0 := by
  exact if_neg hterm

/-- Terminal-history mass assigned by a behavioral profile to a finite event of
realized histories. -/
noncomputable def terminalMassOn
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) (hs : Finset G.History) : ENNReal :=
  Finset.sum hs (fun h => terminalWeight (G := G) σ h)

/-- Terminal-history event-mass functional induced by a behavioral profile. -/
noncomputable def terminalLaw
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) : Finset G.History → ENNReal :=
  terminalMassOn (G := G) σ

@[simp] theorem terminalMassOn_empty
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) :
    terminalMassOn (G := G) σ ∅ = 0 := by
  rw [terminalMassOn]
  simp

@[simp] theorem terminalMassOn_singleton
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) (h : G.History) :
    terminalMassOn (G := G) σ {h} = terminalWeight (G := G) σ h := by
  rw [terminalMassOn]
  simp

@[simp] theorem terminalLaw_apply
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) (hs : Finset G.History) :
    terminalLaw (G := G) σ hs = terminalMassOn (G := G) σ hs := rfl

noncomputable def expectedUtility [Fintype G.History]
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) (i : ι) : ℝ :=
  ∑ h : G.History, (terminalWeight (G := G) σ h).toReal * History.utility h i

theorem expectedUtility_def [Fintype G.History]
    [DecidablePred G.terminal]
    (σ : BehavioralProfile G) (i : ι) :
    expectedUtility (G := G) σ i =
      ∑ h : G.History,
        if G.terminal h.lastState then
          (History.prob σ h).toReal * History.utility h i
        else
          0 := by
  unfold expectedUtility
  classical
  refine Finset.sum_congr rfl ?_
  intro h _
  by_cases hterm : G.terminal h.lastState
  · simp [terminalWeight, hterm]
  · simp [terminalWeight, hterm]

end History

end FOSG

end GameTheory
