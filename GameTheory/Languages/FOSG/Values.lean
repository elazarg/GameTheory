import GameTheory.Languages.FOSG.History

/-!
# GameTheory.Languages.FOSG.Values

Cumulative rewards and utilities for FOSG histories.
-/

namespace GameTheory

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

namespace Step

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Player `i`'s realized reward on a single transition step. -/
abbrev reward (e : G.Step) (i : ι) : ℝ :=
  G.reward e.src e.act e.dst i

end Step

namespace History

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Cumulative reward for player `i` across a list of realized steps. -/
def rewardSumFrom (G : FOSG ι W Act PrivObs PubObs) (i : ι) :
    List G.Step → ℝ
  | [] => 0
  | e :: es => e.reward i + rewardSumFrom G i es

/-- Cumulative reward for player `i` along a realized history. -/
def rewardSum (h : G.History) (i : ι) : ℝ :=
  rewardSumFrom G i h.steps

/-- Utility of player `i` along a realized history. -/
abbrev utility (h : G.History) (i : ι) : ℝ :=
  h.rewardSum i

@[simp] theorem rewardSumFrom_nil
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) :
    rewardSumFrom G i [] = 0 := rfl

@[simp] theorem rewardSumFrom_cons
    (G : FOSG ι W Act PrivObs PubObs) (i : ι)
    (e : G.Step) (es : List G.Step) :
    rewardSumFrom G i (e :: es) = e.reward i + rewardSumFrom G i es := rfl

theorem rewardSumFrom_append_singleton
    (G : FOSG ι W Act PrivObs PubObs) (i : ι)
    (es : List G.Step) (e : G.Step) :
    rewardSumFrom G i (es ++ [e]) = rewardSumFrom G i es + e.reward i := by
  induction es with
  | nil =>
      simp [rewardSumFrom]
  | cons e₀ es ih =>
      simp [rewardSumFrom, ih, add_assoc]

theorem rewardSumFrom_append
    (G : FOSG ι W Act PrivObs PubObs) (i : ι)
    (es₁ es₂ : List G.Step) :
    rewardSumFrom G i (es₁ ++ es₂) =
      rewardSumFrom G i es₁ + rewardSumFrom G i es₂ := by
  induction es₁ with
  | nil =>
      simp [rewardSumFrom]
  | cons e es ih =>
      simp [rewardSumFrom, ih, add_assoc, add_comm]

@[simp] theorem rewardSum_nil
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) :
    (History.nil G).rewardSum i = 0 := rfl

@[simp] theorem utility_nil
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) :
    (History.nil G).utility i = 0 := rfl

@[simp] theorem rewardSum_snoc
    (h : G.History) (i : ι) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    (h.snoc a dst support).rewardSum i =
      h.rewardSum i + G.reward h.lastState a dst i := by
  simpa [rewardSum, History.snoc, Step.reward] using
    rewardSumFrom_append_singleton G i h.steps ⟨h.lastState, a, dst, support⟩

@[simp] theorem utility_snoc
    (h : G.History) (i : ι) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    (h.snoc a dst support).utility i =
      h.utility i + G.reward h.lastState a dst i := by
  change (h.snoc a dst support).rewardSum i =
      h.rewardSum i + G.reward h.lastState a dst i
  exact h.rewardSum_snoc i a dst support

theorem utility_def
    (h : G.History) (i : ι) :
    h.utility i = h.rewardSum i := rfl

end History

end FOSG

end GameTheory
