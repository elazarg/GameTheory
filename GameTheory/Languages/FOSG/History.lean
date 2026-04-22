import GameTheory.Languages.FOSG.Basic

/-!
# GameTheory.Languages.FOSG.History

Finite histories for FOSGs.

Histories are stored as unindexed lists of transition records together with a
simple chaining predicate from the initial world state.
-/

namespace GameTheory

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- One realized transition step in a FOSG history. -/
structure Step (G : FOSG ι W Act PrivObs PubObs) where
  src : W
  act : G.LegalAction src
  dst : W
  support : G.transition src act dst ≠ 0

namespace Step

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Player `i`'s realized local action, if any, in a step. -/
abbrev ownAction? (e : G.Step) (i : ι) : Option (Act i) :=
  e.act.1 i

/-- Public observation emitted by a step. -/
abbrev publicObs (e : G.Step) : PubObs :=
  G.pubObs e.src e.act e.dst

/-- Private observation for player `i` emitted by a step. -/
abbrev privateObs (e : G.Step) (i : ι) : PrivObs i :=
  G.privObs i e.src e.act e.dst

theorem ownAction?_eq_none_of_not_mem_active
    (e : G.Step) {i : ι} (hi : i ∉ G.active e.src) :
    e.ownAction? i = none :=
  G.inactive_eq_none (a := e.act) hi

theorem exists_ownAction_of_mem_active
    (e : G.Step) {i : ι} (hi : i ∈ G.active e.src) :
    ∃ ai : Act i, e.ownAction? i = some ai :=
  G.active_has_some (a := e.act) hi

end Step

/-- Chaining predicate for a list of steps starting from a given world state. -/
def StepChainFrom (G : FOSG ι W Act PrivObs PubObs) :
    W → List G.Step → Prop
  | _, [] => True
  | w, e :: es => e.src = w ∧ G.StepChainFrom e.dst es

/-- Last world state reached by a list of chained steps from a given start. -/
def lastStateFrom (G : FOSG ι W Act PrivObs PubObs) :
    W → List G.Step → W
  | w, [] => w
  | _, e :: es => G.lastStateFrom e.dst es

/-- State trace induced by a list of steps from a given start. -/
def stateTraceFrom (G : FOSG ι W Act PrivObs PubObs) :
    W → List G.Step → List W
  | w, [] => [w]
  | _, e :: es => e.src :: G.stateTraceFrom e.dst es

theorem lastStateFrom_nil
    (G : FOSG ι W Act PrivObs PubObs) (w : W) :
    G.lastStateFrom w [] = w := rfl

theorem lastStateFrom_cons
    (G : FOSG ι W Act PrivObs PubObs) (w : W) (e : G.Step) (es : List G.Step) :
    G.lastStateFrom w (e :: es) = G.lastStateFrom e.dst es := rfl

theorem stateTraceFrom_nil
    (G : FOSG ι W Act PrivObs PubObs) (w : W) :
    G.stateTraceFrom w [] = [w] := rfl

theorem stateTraceFrom_cons
    (G : FOSG ι W Act PrivObs PubObs) (w : W) (e : G.Step) (es : List G.Step) :
    G.stateTraceFrom w (e :: es) = e.src :: G.stateTraceFrom e.dst es := rfl

theorem stateTraceFrom_length
    (G : FOSG ι W Act PrivObs PubObs) (w : W) (es : List G.Step) :
    (G.stateTraceFrom w es).length = es.length + 1 := by
  induction es generalizing w with
  | nil =>
      simp [stateTraceFrom]
  | cons e es ih =>
      simp [stateTraceFrom, ih]

theorem lastStateFrom_append_singleton
    (G : FOSG ι W Act PrivObs PubObs) (w : W) (es : List G.Step) (e : G.Step) :
    G.lastStateFrom w (es ++ [e]) = e.dst := by
  induction es generalizing w with
  | nil =>
      simp [lastStateFrom]
  | cons e₀ es ih =>
      simp [lastStateFrom, ih]

theorem lastStateFrom_append
    (G : FOSG ι W Act PrivObs PubObs) (w : W)
    (es₁ es₂ : List G.Step) :
    G.lastStateFrom w (es₁ ++ es₂) = G.lastStateFrom (G.lastStateFrom w es₁) es₂ := by
  induction es₁ generalizing w with
  | nil =>
      simp [lastStateFrom]
  | cons e es ih =>
      simp [lastStateFrom, ih]

theorem stateTraceFrom_append_singleton
    (G : FOSG ι W Act PrivObs PubObs) (w : W) (es : List G.Step) (e : G.Step)
    (hsrc : e.src = G.lastStateFrom w es) :
    G.stateTraceFrom w (es ++ [e]) = G.stateTraceFrom w es ++ [e.dst] := by
  induction es generalizing w with
  | nil =>
      simp [stateTraceFrom, lastStateFrom] at hsrc ⊢
      simp [hsrc]
  | cons e₀ es ih =>
      simpa [stateTraceFrom, List.cons_append] using
        congrArg (List.cons e₀.src) (ih (w := e₀.dst) hsrc)

theorem StepChainFrom.snoc
    {G : FOSG ι W Act PrivObs PubObs} {w : W} {es : List G.Step}
    (hchain : G.StepChainFrom w es)
    (e : G.Step)
    (hsrc : e.src = G.lastStateFrom w es) :
    G.StepChainFrom w (es ++ [e]) := by
  induction es generalizing w with
  | nil =>
      simp [StepChainFrom, lastStateFrom] at hsrc ⊢
      simpa using And.intro hsrc trivial
  | cons e₀ es ih =>
      rcases hchain with ⟨hsrc₀, htail⟩
      simpa [StepChainFrom, List.cons_append] using
        And.intro hsrc₀ (ih (w := e₀.dst) htail hsrc)

theorem StepChainFrom.append
    {G : FOSG ι W Act PrivObs PubObs} {w : W}
    {es₁ es₂ : List G.Step}
    (h₁ : G.StepChainFrom w es₁)
    (h₂ : G.StepChainFrom (G.lastStateFrom w es₁) es₂) :
    G.StepChainFrom w (es₁ ++ es₂) := by
  induction es₁ generalizing w with
  | nil =>
      simpa [StepChainFrom, lastStateFrom] using h₂
  | cons e es ih =>
      rcases h₁ with ⟨hsrc, htail⟩
      simpa [StepChainFrom, List.cons_append] using
        And.intro hsrc (ih (w := e.dst) htail h₂)

theorem StepChainFrom.left
    {G : FOSG ι W Act PrivObs PubObs} {w : W}
    {es₁ es₂ : List G.Step}
    (h : G.StepChainFrom w (es₁ ++ es₂)) :
    G.StepChainFrom w es₁ := by
  induction es₁ generalizing w with
  | nil =>
      simp [StepChainFrom]
  | cons e es ih =>
      rcases h with ⟨hsrc, htail⟩
      simpa [StepChainFrom, List.cons_append] using
        And.intro hsrc (ih (w := e.dst) htail)

theorem StepChainFrom.right
    {G : FOSG ι W Act PrivObs PubObs} {w : W}
    {es₁ es₂ : List G.Step}
    (h : G.StepChainFrom w (es₁ ++ es₂)) :
    G.StepChainFrom (G.lastStateFrom w es₁) es₂ := by
  induction es₁ generalizing w with
  | nil =>
      simpa [StepChainFrom, lastStateFrom] using h
  | cons e es ih =>
      rcases h with ⟨hsrc, htail⟩
      simpa [StepChainFrom, lastStateFrom, List.cons_append] using
        ih (w := e.dst) htail

/-- Bundled finite history of realized transitions from the initial world state. -/
structure History (G : FOSG ι W Act PrivObs PubObs) where
  steps : List G.Step
  chain : G.StepChainFrom G.init steps

namespace History

variable {G : FOSG ι W Act PrivObs PubObs}

@[ext] theorem ext
    {h h' : G.History} (hsteps : h.steps = h'.steps) :
    h = h' := by
  cases h
  cases h'
  cases hsteps
  rfl

/-- Empty history at the initial state. -/
def nil (G : FOSG ι W Act PrivObs PubObs) : G.History :=
  ⟨[], trivial⟩

/-- Last world state of a history. -/
def lastState (h : G.History) : W :=
  G.lastStateFrom G.init h.steps

/-- Underlying state trace of a history, including the initial world state. -/
def stateTrace (h : G.History) : List W :=
  G.stateTraceFrom G.init h.steps

/-- Underlying legal-action trace of a history. -/
def actionTrace (h : G.History) : List (Σ w : W, G.LegalAction w) :=
  h.steps.map (fun e => ⟨e.src, e.act⟩)

/-- Append one realized step to a history. -/
def snoc (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    G.History :=
  { steps := h.steps ++ [⟨h.lastState, a, dst, support⟩]
    chain := FOSG.StepChainFrom.snoc h.chain ⟨h.lastState, a, dst, support⟩ rfl }

/-- Append a concrete realized step whose source matches the current endpoint. -/
def appendStep (h : G.History) (e : G.Step)
    (hsrc : e.src = h.lastState) :
    G.History :=
  { steps := h.steps ++ [e]
    chain := FOSG.StepChainFrom.snoc h.chain e hsrc }

@[simp] theorem steps_nil :
    (History.nil G).steps = [] := rfl

@[simp] theorem lastState_nil :
    (History.nil G).lastState = G.init := rfl

@[simp] theorem stateTrace_nil :
    (History.nil G).stateTrace = [G.init] := rfl

@[simp] theorem actionTrace_nil :
    (History.nil G).actionTrace = [] := rfl

@[simp] theorem steps_snoc
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    (h.snoc a dst support).steps = h.steps ++ [⟨h.lastState, a, dst, support⟩] := rfl

@[simp] theorem steps_appendStep
    (h : G.History) (e : G.Step) (hsrc : e.src = h.lastState) :
    (h.appendStep e hsrc).steps = h.steps ++ [e] := rfl

@[simp] theorem lastState_snoc
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    (h.snoc a dst support).lastState = dst := by
  simpa [History.lastState, History.snoc] using
    G.lastStateFrom_append_singleton G.init h.steps ⟨h.lastState, a, dst, support⟩

@[simp] theorem stateTrace_snoc
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    (h.snoc a dst support).stateTrace = h.stateTrace ++ [dst] := by
  simpa [History.stateTrace, History.snoc] using
    G.stateTraceFrom_append_singleton G.init h.steps ⟨h.lastState, a, dst, support⟩ rfl

@[simp] theorem actionTrace_snoc
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    (h.snoc a dst support).actionTrace = h.actionTrace ++ [⟨h.lastState, a⟩] := by
  simp [History.actionTrace, History.snoc, List.map_append]

theorem stateTrace_length
    (h : G.History) :
    h.stateTrace.length = h.steps.length + 1 := by
  simpa [History.stateTrace] using G.stateTraceFrom_length G.init h.steps

@[simp] theorem lastState_appendStep
    (h : G.History) (e : G.Step) (hsrc : e.src = h.lastState) :
    (h.appendStep e hsrc).lastState = e.dst := by
  simpa [History.lastState, History.appendStep] using
    G.lastStateFrom_append_singleton G.init h.steps e

@[simp] theorem stateTrace_appendStep
    (h : G.History) (e : G.Step) (hsrc : e.src = h.lastState) :
    (h.appendStep e hsrc).stateTrace = h.stateTrace ++ [e.dst] := by
  simpa [History.stateTrace, History.appendStep] using
    G.stateTraceFrom_append_singleton G.init h.steps e hsrc

theorem appendStep_eq_snoc
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    h.appendStep ⟨h.lastState, a, dst, support⟩ rfl = h.snoc a dst support := rfl

theorem length_states_eq_actions_succ
    (h : G.History) :
    h.stateTrace.length = h.actionTrace.length + 1 := by
  simpa [History.actionTrace] using h.stateTrace_length

/-- Prefix relation on realized histories. -/
def IsPrefix (h h' : G.History) : Prop :=
  ∃ suffix : List G.Step, h'.steps = h.steps ++ suffix

/-- Descendant relation on realized histories. -/
def IsDescendant (h h' : G.History) : Prop :=
  h'.IsPrefix h

/-- Terminality of the current endpoint of a history. -/
def IsTerminal (h : G.History) : Prop :=
  G.terminal h.lastState

/-- The set of terminal realized histories. -/
def terminalHistories : Set G.History :=
  { h | h.IsTerminal }

theorem isPrefix_iff
    {h h' : G.History} :
    h.IsPrefix h' ↔ ∃ suffix : List G.Step, h'.steps = h.steps ++ suffix := by
  rfl

theorem isDescendant_iff
    {h h' : G.History} :
    h.IsDescendant h' ↔ h'.IsPrefix h := by
  rfl

theorem prefix_refl
    (h : G.History) :
    h.IsPrefix h := by
  exact ⟨[], by simp⟩

theorem nil_prefix
    (h : G.History) :
    (History.nil G).IsPrefix h := by
  exact ⟨h.steps, by simp [History.nil]⟩

theorem prefix_of_eq
    {h h' : G.History} (heq : h = h') :
    h.IsPrefix h' := by
  subst heq
  exact h.prefix_refl

theorem prefix_snoc
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    h.IsPrefix (h.snoc a dst support) := by
  refine ⟨[⟨h.lastState, a, dst, support⟩], ?_⟩
  simp [History.snoc]

theorem prefix_trans
    {h₁ h₂ h₃ : G.History}
    (h₁₂ : h₁.IsPrefix h₂) (h₂₃ : h₂.IsPrefix h₃) :
    h₁.IsPrefix h₃ := by
  rcases h₁₂ with ⟨s₁₂, hs₁₂⟩
  rcases h₂₃ with ⟨s₂₃, hs₂₃⟩
  refine ⟨s₁₂ ++ s₂₃, ?_⟩
  rw [hs₂₃, hs₁₂, List.append_assoc]

theorem descendant_refl
    (h : G.History) :
    h.IsDescendant h := by
  exact h.prefix_refl

theorem descendant_trans
    {h₁ h₂ h₃ : G.History}
    (h₁₂ : h₁.IsDescendant h₂) (h₂₃ : h₂.IsDescendant h₃) :
    h₁.IsDescendant h₃ := by
  exact prefix_trans h₂₃ h₁₂

theorem mem_terminalHistories_iff
    {h : G.History} :
    h ∈ terminalHistories (G := G) ↔ h.IsTerminal := by
  rfl

theorem not_isTerminal_of_legalAction
    (h : G.History) (a : G.LegalAction h.lastState) :
    ¬ h.IsTerminal := by
  intro hterm
  exact G.not_legal_of_terminal (w := h.lastState) (a := a.1) hterm a.2

theorem exists_legalAction_of_not_terminal
    (h : G.History) (hterm : ¬ h.IsTerminal) :
    Nonempty (G.LegalAction h.lastState) := by
  rcases G.exists_legal_of_not_terminal (w := h.lastState) hterm with ⟨a, ha⟩
  exact ⟨⟨a, ha⟩⟩

end History

end FOSG

end GameTheory
