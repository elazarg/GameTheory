import GameTheory.Languages.FOSG.Information

/-!
# GameTheory.Languages.FOSG.Strategy

Strategy objects for FOSGs.

This file follows the paper's strategy shape up to a Lean-friendly adaptation:

- a player's legal moves are derived from the current history endpoint
- legality at an information state is expressed via an explicit invariance
  predicate `LegalObservable`
- behavioral strategies are functions from information states to `PMF (Act i)`
  together with a support constraint, rather than dependent codomains

The final section keeps a state-based legal-joint policy semantics as an
explicitly auxiliary construction.
-/

namespace GameTheory

open Math.Probability

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- The set of actions available to player `i` at world state `w`. -/
def availableActionsAtState
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (i : ι) : Set (Act i) :=
  { ai | ∃ a : G.LegalAction w, a.1 i = some ai }

theorem mem_availableActionsAtState_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {w : W} {i : ι} {ai : Act i} :
    ai ∈ G.availableActionsAtState w i ↔
      ∃ a : G.LegalAction w, a.1 i = some ai := by
  rfl

/-- Local legality of one player's optional action at world state `w`. -/
def locallyLegalAtState
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (i : ι) : Option (Act i) → Prop
  | some ai => ai ∈ G.availableActionsAtState w i
  | none => i ∉ G.active w

theorem locallyLegalAtState_of_legal
    {G : FOSG ι W Act PrivObs PubObs}
    {w : W} {a : G.LegalAction w} (i : ι) :
    G.locallyLegalAtState w i (a.1 i) := by
  cases h : a.1 i with
  | none =>
      exact by
        intro hi
        rcases G.active_has_some (a := a) hi with ⟨ai, hai⟩
        simp [h] at hai
  | some ai =>
      exact ⟨a, h⟩

/-- Paper-facing factorization condition: a joint action is legal whenever each
player's local component is legal at the current world state. -/
def LegalityFactorizes
    (G : FOSG ι W Act PrivObs PubObs) : Prop :=
  ∀ {w : W} {a : JointAction Act},
    (∀ i, G.locallyLegalAtState w i (a i)) →
    G.legal w a

/-- The set of actions available to player `i` at the endpoint of history `h`. -/
def availableActions
    (G : FOSG ι W Act PrivObs PubObs)
    (h : G.History) (i : ι) : Set (Act i) :=
  { ai | ∃ a : G.LegalAction h.lastState, a.1 i = some ai }

theorem mem_availableActions_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {h : G.History} {i : ι} {ai : Act i} :
    ai ∈ G.availableActions h i ↔
      ∃ a : G.LegalAction h.lastState, a.1 i = some ai := by
  rfl

theorem availableActions_eq_availableActionsAtState
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) (i : ι) :
    G.availableActions h i = G.availableActionsAtState h.lastState i := by
  rfl

theorem not_mem_availableActions_of_not_mem_active
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) {i : ι} (hi : i ∉ G.active h.lastState) :
    G.availableActions h i = ∅ := by
  ext ai
  constructor
  · intro hai
    rcases hai with ⟨a, ha⟩
    have hnone : a.1 i = none := G.inactive_eq_none (a := a) hi
    simp [hnone] at ha
  · intro hai
    simp at hai

/-- Lean-facing form of the paper's assumption that legal actions are
deducible from the player's information state. -/
def LegalObservable (G : FOSG ι W Act PrivObs PubObs) : Prop :=
  ∀ (i : ι) {h h' : G.History},
    h.playerView i = h'.playerView i →
    G.availableActions h i = G.availableActions h' i

theorem availableActions_eq_of_playerView_eq
    {G : FOSG ι W Act PrivObs PubObs}
    (hLeg : G.LegalObservable) (i : ι)
    {h h' : G.History}
    (hInfo : h.playerView i = h'.playerView i) :
    G.availableActions h i = G.availableActions h' i :=
  hLeg i hInfo

/-- The legal actions associated with an information state, defined as the
common action set across all realizing histories when `LegalObservable` holds. -/
def availableActionsAtInfoState
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (s : G.InfoState i) : Set (Act i) :=
  { ai | ∃ h : G.History, h.playerView i = s ∧ ai ∈ G.availableActions h i }

theorem mem_availableActionsAtInfoState_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {i : ι} {s : G.InfoState i} {ai : Act i} :
    ai ∈ G.availableActionsAtInfoState i s ↔
      ∃ h : G.History, h.playerView i = s ∧ ai ∈ G.availableActions h i := by
  rfl

theorem mem_availableActionsAtInfoState_of_history
    {G : FOSG ι W Act PrivObs PubObs}
    {i : ι} (h : G.History) {ai : Act i}
    (hai : ai ∈ G.availableActions h i) :
    ai ∈ G.availableActionsAtInfoState i (h.playerView i) := by
  exact ⟨h, rfl, hai⟩

theorem availableActionsAtInfoState_eq_of_history
    {G : FOSG ι W Act PrivObs PubObs}
    (hLeg : G.LegalObservable) (i : ι) (h : G.History) :
    G.availableActionsAtInfoState i (h.playerView i) = G.availableActions h i := by
  ext ai
  constructor
  · intro hai
    rcases hai with ⟨h', hh', hai'⟩
    have hEq : G.availableActions h' i = G.availableActions h i :=
      G.availableActions_eq_of_playerView_eq hLeg i hh'
    exact hEq ▸ hai'
  · intro hai
    exact G.mem_availableActionsAtInfoState_of_history h hai

/-- Pure strategy for player `i`: choose an action from each information state. -/
abbrev PureStrategy (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  G.InfoState i → Act i

/-- Behavioral strategy for player `i`: a distribution over actions from each
information state. -/
abbrev BehavioralStrategy (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  G.InfoState i → PMF (Act i)

/-- Joint pure strategy profile. -/
abbrev PureProfile (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, PureStrategy G i

/-- Joint behavioral strategy profile. -/
abbrev BehavioralProfile (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, BehavioralStrategy G i

/-- A pure strategy is legal if at every realized history it chooses an
available action. -/
def IsLegalPureStrategy
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (σ : PureStrategy G i) : Prop :=
  ∀ h : G.History, σ (h.playerView i) ∈ G.availableActions h i

/-- A behavioral strategy is legal if its support stays within the available
action set at every realized history. -/
def IsLegalBehavioralStrategy
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (σ : BehavioralStrategy G i) : Prop :=
  ∀ (h : G.History) {ai : Act i},
    ai ∈ (σ (h.playerView i)).support →
    ai ∈ G.availableActions h i

/-- A pure profile is legal if every player's strategy is legal. -/
def IsLegalPureProfile
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : PureProfile G) : Prop :=
  ∀ i, G.IsLegalPureStrategy i (σ i)

/-- A behavioral profile is legal if every player's strategy is legal. -/
def IsLegalBehavioralProfile
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) : Prop :=
  ∀ i, G.IsLegalBehavioralStrategy i (σ i)

/-- Lift a pure profile to a behavioral one. -/
noncomputable def pureToBehavioral
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : PureProfile G) : BehavioralProfile G :=
  fun i s => PMF.pure (σ i s)

@[simp] theorem pureToBehavioral_apply
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : PureProfile G) (i : ι) (s : G.InfoState i) :
    G.pureToBehavioral σ i s = PMF.pure (σ i s) := rfl

theorem legalBehavioral_of_legalPure
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : PureProfile G)
    (hσ : G.IsLegalPureProfile σ) :
    G.IsLegalBehavioralProfile (G.pureToBehavioral σ) := by
  intro i h ai hai
  rw [pureToBehavioral_apply] at hai
  rw [PMF.support_pure, Set.mem_singleton_iff] at hai
  subst hai
  exact hσ i h

namespace Auxiliary

/-- Auxiliary state-based legal joint-action policy. This is not the paper's
main strategy notion; it is kept only as a simple execution gadget. -/
abbrev MarkovJointPolicy (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ w, PMF (G.LegalAction w)

/-- Deterministic auxiliary state-based legal joint-action policy. -/
abbrev PureMarkovJointPolicy (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ w, G.LegalAction w

/-- Lift a pure legal-joint policy to a stochastic one. -/
noncomputable def pureMarkovToBehavioral
    (G : FOSG ι W Act PrivObs PubObs)
    (π : PureMarkovJointPolicy G) : MarkovJointPolicy G :=
  fun w => PMF.pure (π w)

@[simp] theorem pureMarkovToBehavioral_apply
    (G : FOSG ι W Act PrivObs PubObs)
    (π : PureMarkovJointPolicy G) (w : W) :
    pureMarkovToBehavioral G π w = PMF.pure (π w) := rfl

/-- Probability of a realized step under an auxiliary state-based policy. -/
noncomputable def stepProb
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) (e : G.Step) : ENNReal :=
  (π e.src) e.act * (G.transition e.src e.act) e.dst

/-- Path probability of a list of realized steps under an auxiliary policy. -/
noncomputable def pathProb
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) : List G.Step → ENNReal
  | [] => 1
  | e :: es => stepProb π e * pathProb π es

/-- Path probability of a realized history under an auxiliary policy. -/
noncomputable def prob
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) (h : G.History) : ENNReal :=
  pathProb π h.steps

@[simp] theorem pathProb_nil
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) :
    pathProb π [] = 1 := rfl

@[simp] theorem pathProb_cons
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) (e : G.Step) (es : List G.Step) :
    pathProb π (e :: es) = stepProb π e * pathProb π es := rfl

@[simp] theorem prob_nil
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) :
    prob π (History.nil G) = 1 := rfl

theorem pathProb_append_singleton
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) (es : List G.Step) (e : G.Step) :
    pathProb π (es ++ [e]) = pathProb π es * stepProb π e := by
  induction es with
  | nil =>
      simp [pathProb, stepProb]
  | cons e₀ es ih =>
      simp [pathProb, stepProb, ih, mul_assoc]

@[simp] theorem prob_snoc
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G)
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    prob π (h.snoc a dst support) =
      prob π h * stepProb π ⟨h.lastState, a, dst, support⟩ := by
  simpa [prob, History.snoc] using
    pathProb_append_singleton π h.steps ⟨h.lastState, a, dst, support⟩

end Auxiliary

end FOSG

end GameTheory
