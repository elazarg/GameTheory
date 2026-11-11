module

public import GameTheory.Tests.Potential
public import GameTheory.Math.GuardedOptimality

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.DynamicChoice

open GameTheory.Math GameTheory.Math.Probability GameTheory.Tests

/-- This total ranking evaluates the whole law nonlinearly. -/
def score (law : PMF Bool) : ℝ := ((law true).toReal - 2 / 5) ^ 2

def lawPreference (preferred alternative : PMF Bool) : Prop := score alternative ≤ score preferred

theorem lawPreference_reflexive : Rank.Reflexive lawPreference := fun _ => le_rfl

theorem lawPreference_transitive : Rank.Transitive lawPreference :=
  fun _ _ _ first second => second.trans first

theorem lawPreference_total : Rank.Total lawPreference := fun _ _ => le_total _ _

def prior : PMF Bool := Potential.supportFairLaw

/-- Both branches have a genuine strict choice. The alternative at the false
signal is itself a lottery, rather than a forced or tied action. -/
def branch : Bool → Bool → PMF Bool
  | true, true => PMF.pure true
  | true, false => PMF.pure false
  | false, true => PMF.pure false
  | false, false => prior

def chosenPolicy : Bool → Bool := fun _ => true

def alternativePolicy : Bool → Bool := fun _ => false

def play (policy : Bool → Bool) : PMF Bool :=
  prior.bind fun hidden => branch hidden (policy hidden)

def menu (_hidden : Bool) : Set Bool := Set.univ

def policyFeasible (policy : Bool → Bool) : Prop := ∀ hidden, policy hidden ∈ menu hidden

theorem chosenPolicy_feasible : policyFeasible chosenPolicy := by
  intro hidden
  cases hidden <;> simp [chosenPolicy, menu]

theorem alternativePolicy_feasible : policyFeasible alternativePolicy := by
  intro hidden
  cases hidden <;> simp [alternativePolicy, menu]

theorem play_chosen : play chosenPolicy = prior := by
  have kernel : (fun hidden => branch hidden (chosenPolicy hidden)) = PMF.pure := by
    funext hidden
    cases hidden <;> rfl
  rw [play, kernel]
  exact PMF.bind_pure prior

theorem play_alternative : play alternativePolicy =
    mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) prior := by
  simp [play, prior, Potential.supportFairLaw, mix_bind, branch, alternativePolicy]

theorem alternative_true_mass : ((play alternativePolicy) true).toReal = 1 / 4 := by
  rw [play_alternative]
  norm_num [prior, Potential.supportFairLaw, mix_apply]

/-- Conditioning on the true branch strictly favors the prescribed action. -/
theorem conditional_true_strict :
    Rank.strict lawPreference (branch true true) (branch true false) := by
  norm_num [Rank.strict, lawPreference, score, branch]

/-- The false branch also strictly favors its prescribed action. -/
theorem conditional_false_strict :
    Rank.strict lawPreference (branch false true) (branch false false) := by
  norm_num [Rank.strict, lawPreference, score, branch, prior,
    Potential.supportFairLaw, mix_apply]

/-- Every conditional menu is optimized under the same total law ranking. -/
theorem chosen_conditionally_optimal (hidden : Bool) :
    IsOptimalOn (fun _ : Bool => True)
      (fun chosen alternative => lawPreference (branch hidden chosen) (branch hidden alternative))
      (menu hidden) (chosenPolicy hidden) := by
  refine ⟨trivial, fun _ _ => trivial, ?_⟩
  intro alternative _
  cases hidden <;> cases alternative <;>
    norm_num [lawPreference, score, branch, chosenPolicy, prior,
      Potential.supportFairLaw, mix_apply]

/-- Before conditioning, the fair prescribed law loses to the alternative
whose true-outcome probability is one quarter. Each branch strictly favors the
prescribed action, but totality and transitivity do not supply bind monotonicity. -/
theorem whole_policy_strict_reversal :
    Rank.strict lawPreference (play alternativePolicy) (play chosenPolicy) := by
  rw [play_chosen, play_alternative]
  norm_num [Rank.strict, lawPreference, score, prior, Potential.supportFairLaw, mix_apply]

theorem chosen_not_whole_policy_optimal :
    ¬ IsOptimalOn policyFeasible
      (fun chosen alternative => lawPreference (play chosen) (play alternative))
      {policy | policyFeasible policy} chosenPolicy := by
  intro optimal
  have impossible := optimal.2.2 alternativePolicy alternativePolicy_feasible
  exact whole_policy_strict_reversal.2 impossible

/-- Possibility preferences do compose through bind, for arbitrary supported
kernels and without an expected-utility representation. -/
theorem supportPreference_bind {α : Type*} (law : PMF α)
    (preferred alternative : α → PMF Bool)
    (comparisons : ∀ a ∈ law.support,
      Potential.supportPreference () (preferred a) (alternative a)) :
    Potential.supportPreference () (law.bind preferred) (law.bind alternative) := by
  classical
  by_cases supported : true ∈ (law.bind preferred).support
  · exact Or.inl supported
  · apply Or.inr
    intro alternativeSupported
    obtain ⟨a, sourceSupported, targetSupported⟩ :=
      (PMF.mem_support_bind_iff law alternative true).mp alternativeSupported
    rcases comparisons a sourceSupported with preferredSupported | notSupported
    · exact supported ((PMF.mem_support_bind_iff law preferred true).mpr
        ⟨a, sourceSupported, preferredSupported⟩)
    · exact notSupported targetSupported

theorem supportPreference_upper_bind {α : Type*} (law : PMF α)
    (kernel : α → PMF Bool) (base : PMF Bool)
    (comparisons : ∀ a ∈ law.support, Potential.supportPreference () base (kernel a)) :
    Potential.supportPreference () base (law.bind kernel) := by
  simpa only [PMF.bind_const] using
    supportPreference_bind law (fun _ => base) kernel comparisons

theorem supportPreference_lower_bind {α : Type*} (law : PMF α)
    (kernel : α → PMF Bool) (base : PMF Bool)
    (comparisons : ∀ a ∈ law.support, Potential.supportPreference () (kernel a) base) :
    Potential.supportPreference () (law.bind kernel) base := by
  simpa only [PMF.bind_const] using
    supportPreference_bind law kernel (fun _ => base) comparisons

end GameTheory.Experimental.DynamicChoice
