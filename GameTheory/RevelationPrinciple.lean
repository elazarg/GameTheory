import GameTheory.MechanismDesign

/-!
# The Revelation Principle

The revelation principle states that for any mechanism and any
Bayesian Nash equilibrium of that mechanism, there exists an equivalent
direct mechanism in which truthful reporting is an equilibrium.

## Main definitions

* `GeneralMechanism` — a mechanism with separate type and action spaces
* `GeneralMechanism.toDirect` — the direct mechanism induced by a strategy

## Main results

* `revelation_principle` — the toDirect mechanism with the equilibrium
    strategy is incentive compatible (BIC)
-/

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- A general mechanism: players have types (private info) and actions
    (what they report/do). The outcome depends on actions, not types directly. -/
structure GeneralMechanism (ι : Type) [Fintype ι] where
  /-- Type space for each player (private information). -/
  Θ : ι → Type
  [instFintypeΘ : ∀ i, Fintype (Θ i)]
  [instNonemptyΘ : ∀ i, Nonempty (Θ i)]
  /-- Action space for each player. -/
  Act : ι → Type
  [instFintypeAct : ∀ i, Fintype (Act i)]
  [instNonemptyAct : ∀ i, Nonempty (Act i)]
  /-- Outcome rule: maps actions to per-player payoff. -/
  outcome : (∀ i, Act i) → ι → ℝ

attribute [instance] GeneralMechanism.instFintypeΘ GeneralMechanism.instNonemptyΘ
  GeneralMechanism.instFintypeAct GeneralMechanism.instNonemptyAct

namespace GeneralMechanism

variable {ι : Type} [Fintype ι]

/-- A strategy profile: each player maps their type to an action. -/
def StrategyProfile (M : GeneralMechanism ι) := ∀ i, M.Θ i → M.Act i

/-- Payoff for player `who` under strategy profile `σ` when types are `θ`. -/
noncomputable def payoff (M : GeneralMechanism ι) (σ : M.StrategyProfile)
    (θ : ∀ i, M.Θ i) (who : ι) : ℝ :=
  M.outcome (fun i => σ i (θ i)) who

open Classical in
/-- A strategy profile is a Bayesian Nash equilibrium (ex-ante) w.r.t. prior `μ`
    if no player can improve their expected payoff by deviating. -/
def IsBNE (M : GeneralMechanism ι) (μ : PMF (∀ i, M.Θ i))
    (σ : M.StrategyProfile) : Prop :=
  ∀ (who : ι) (σ'_who : M.Θ who → M.Act who),
    expect μ (fun θ => M.payoff σ θ who) ≥
    expect μ (fun θ => M.outcome (Function.update (fun i => σ i (θ i)) who (σ'_who (θ who))) who)

/-- The direct mechanism induced by composing the general mechanism
    with a strategy profile: players "report" types, and the mechanism
    applies the strategy before computing the outcome. -/
noncomputable def toDirect (M : GeneralMechanism ι) (σ : M.StrategyProfile) :
    Mechanism ι where
  Θ := M.Θ
  outcome := fun θ i => M.outcome (fun j => σ j (θ j)) i

open Classical in
/-- **The Revelation Principle**: if `σ` is a BNE of the general mechanism `M`,
    then the direct mechanism `M.toDirect σ` is Bayesian incentive compatible.

    Proof: In the direct mechanism, truthful reporting gives the same payoff
    as playing `σ` in `M`. Any deviation `θ'_who` in the direct mechanism
    corresponds to a deviation `σ_who ∘ (fun _ => θ'_who)` in `M`, which
    cannot improve payoff since `σ` is a BNE. -/
theorem revelation_principle (M : GeneralMechanism ι)
    (μ : PMF (∀ i, M.Θ i))
    (σ : M.StrategyProfile)
    (hBNE : M.IsBNE μ σ) :
    (M.toDirect σ).isBIC μ := by
  intro who θ'
  simp only [toDirect]
  -- The deviation in the direct mechanism: reporting θ' instead of θ_who
  -- corresponds to action σ_who(θ') in the general mechanism
  -- We need: E[outcome(σ(θ))] ≥ E[outcome(update σ(θ) who (σ_who(θ')))]
  -- This follows from BNE with the deviation σ'_who = fun _ => σ_who(θ')
  have h := hBNE who (fun _ => σ who θ')
  simp only [payoff] at h
  convert h using 2
  ext θ; congr 1; ext i
  simp only [Function.update]
  split_ifs with hi
  · subst hi; rfl
  · rfl

end GeneralMechanism

end GameTheory
