/-
# Mixture certificates for incentive preservation

On an infinite outcome carrier the exact cone criterion is unavailable, but a
utility-independent certificate still transfers incentives for every utility
integrable against the laws involved. The certificates are laws only; the
integrability they need is supplied where they are used, and finitely supported
mixtures provide it automatically.

A law-pair simulation represents each target comparison by one mixture of
source comparisons, matching both outcome laws with the same weights. Such
simulations compose and push forward along observations.

Only the incentive difference matters, so a weaker balance certificate
suffices: a mixture of source comparisons and a positive factor make the
target's prescribed-minus-alternative mass equal to that factor times the mixed
source differences. Every law-pair simulation is a balance, and a target
whose difference is twice a source difference is a balance that no law-pair
simulation represents. On a finite carrier a balance puts the target in the
source cone.
-/

import GameTheory.Analysis.IncentiveHierarchy
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι uo us ut ur uv

/-! ## Balance -/

namespace IncentiveComparison

variable {Outcome : Type uo} {Index : Type us}

/-- `target` balances against a mixture of `source` comparisons: mixing
its alternative law with the mixed source prescribed laws gives the same law as
mixing its prescribed law with the mixed source alternatives. Equivalently, its
incentive difference is a nonnegative multiple of the mixed source differences. -/
def IsBalanced (source : Index → IncentiveComparison Outcome)
    (target : IncentiveComparison Outcome) : Prop :=
  ∃ (mixing : PMF Index) (weight : ℝ) (h0 : 0 < weight) (h1 : weight ≤ 1),
    mix weight h0.le h1 target.alternative (mixing.bind fun index => (source index).prescribed) =
      mix weight h0.le h1 target.prescribed (mixing.bind fun index => (source index).alternative)

/-- **A balance transfers incentives** for every utility integrable against the
source, mixed, and target laws, on any outcome carrier. -/
theorem IsBalanced.holds {source : Index → IncentiveComparison Outcome}
    {target : IncentiveComparison Outcome} {mixing : PMF Index} {weight : ℝ}
    (h0 : 0 < weight) (h1 : weight ≤ 1)
    (hbalance : mix weight h0.le h1 target.alternative
        (mixing.bind fun index => (source index).prescribed) =
      mix weight h0.le h1 target.prescribed
        (mixing.bind fun index => (source index).alternative))
    (utility : Outcome → ℝ) (respected : ∀ index, (source index).Holds utility)
    (integrable : ∀ index, PayoffIntegrable (source index).prescribed utility ∧
      PayoffIntegrable (source index).alternative utility)
    (hmixedPrescribed : PayoffIntegrable
      (mixing.bind fun index => (source index).prescribed) utility)
    (hmixedAlternative : PayoffIntegrable
      (mixing.bind fun index => (source index).alternative) utility)
    (hprescribed : PayoffIntegrable target.prescribed utility)
    (halternative : PayoffIntegrable target.alternative utility) :
    target.Holds utility := by
  have hvalues := congrArg (fun law => expect law utility) hbalance
  rw [expect_mix _ _ _ _ _ _ halternative hmixedPrescribed,
    expect_mix _ _ _ _ _ _ hprescribed hmixedAlternative] at hvalues
  have hmixed : expect (mixing.bind fun index => (source index).alternative) utility ≤
      expect (mixing.bind fun index => (source index).prescribed) utility := by
    rw [expect_bind_tower _ _ _ hmixedPrescribed, expect_bind_tower _ _ _ hmixedAlternative]
    exact expect_mono (fun index _ => (holds_iff_of_integrable _ utility
        (integrable index).1 (integrable index).2).mp (respected index))
      (payoffIntegrable_bind_conditionalExpectation _ _ _ hmixedAlternative)
      (payoffIntegrable_bind_conditionalExpectation _ _ _ hmixedPrescribed)
  rw [holds_iff_of_integrable _ _ hprescribed halternative]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hmixed)]

/-- On a finite carrier a balance puts the target difference in the source
cone. -/
theorem IsBalanced.difference_mem_cone [Fintype Outcome]
    {source : Index → IncentiveComparison Outcome} {target : IncentiveComparison Outcome}
    (hbalanced : target.IsBalanced source) :
    target.difference ∈ cone source := by
  obtain ⟨mixing, weight, h0, h1, hbalance⟩ := hbalanced
  rw [mem_cone_iff]
  intro utility respected
  exact IsBalanced.holds h0 h1 hbalance utility respected
    (fun _ => ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _⟩)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

end IncentiveComparison

/-! ## Law-pair simulation -/

/-- A law-pair simulation represents each target comparison by one mixture of
source comparisons of the same unit, using the same weights for the prescribed
and the alternative laws. -/
structure IncentiveSimulation {ι : Type uι} {Outcome : Type uo}
    {Source : ι → Type us} {Target : ι → Type ut}
    (source : ∀ who, Source who → IncentiveComparison Outcome)
    (target : ∀ who, Target who → IncentiveComparison Outcome) where
  /-- The source comparisons mixed into each target comparison. -/
  mixing : ∀ who, Target who → PMF (Source who)
  prescribed : ∀ who deviation, (target who deviation).prescribed =
    (mixing who deviation).bind fun original => (source who original).prescribed
  alternative : ∀ who deviation, (target who deviation).alternative =
    (mixing who deviation).bind fun original => (source who original).alternative

namespace IncentiveSimulation

variable {ι : Type uι} {Outcome : Type uo}
  {Source : ι → Type us} {Target : ι → Type ut} {Third : ι → Type ur}
  {source : ∀ who, Source who → IncentiveComparison Outcome}
  {target : ∀ who, Target who → IncentiveComparison Outcome}
  {third : ∀ who, Third who → IncentiveComparison Outcome}

/-- A map of deviations matching both laws is the point-mass case. -/
def ofMap (decode : ∀ who, Target who → Source who)
    (prescribed : ∀ who deviation, (target who deviation).prescribed =
      (source who (decode who deviation)).prescribed)
    (alternative : ∀ who deviation, (target who deviation).alternative =
      (source who (decode who deviation)).alternative) :
    IncentiveSimulation source target where
  mixing who deviation := PMF.pure (decode who deviation)
  prescribed who deviation := by rw [PMF.pure_bind]; exact prescribed who deviation
  alternative who deviation := by rw [PMF.pure_bind]; exact alternative who deviation

/-- Every family simulates itself. -/
def refl (source : ∀ who, Source who → IncentiveComparison Outcome) :
    IncentiveSimulation source source :=
  ofMap (fun _ => id) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Simulations compose by expanding intermediate mixtures. -/
def trans (first : IncentiveSimulation source target)
    (second : IncentiveSimulation target third) :
    IncentiveSimulation source third where
  mixing who deviation := (second.mixing who deviation).bind (first.mixing who)
  prescribed who deviation := by
    rw [second.prescribed, PMF.bind_bind]
    exact congrArg _ (funext fun middle => first.prescribed who middle)
  alternative who deviation := by
    rw [second.alternative, PMF.bind_bind]
    exact congrArg _ (funext fun middle => first.alternative who middle)

/-- The observation of a comparison pushes both laws forward. -/
def observeComparison {Observed : Type uv} (observe : Outcome → Observed)
    (comparison : IncentiveComparison Outcome) : IncentiveComparison Observed :=
  ⟨comparison.prescribed.map observe, comparison.alternative.map observe⟩

/-- Simulations survive observation of outcomes. -/
def map {Observed : Type uv} (simulation : IncentiveSimulation source target)
    (observe : Outcome → Observed) :
    IncentiveSimulation (fun who original => observeComparison observe (source who original))
      (fun who deviation => observeComparison observe (target who deviation)) where
  mixing := simulation.mixing
  prescribed who deviation := by
    simp only [observeComparison]
    rw [simulation.prescribed, PMF.map_bind]
  alternative who deviation := by
    simp only [observeComparison]
    rw [simulation.alternative, PMF.map_bind]

/-- Every law-pair simulation is a balance with weight one half. -/
theorem isBalanced (simulation : IncentiveSimulation source target) (who : ι)
    (deviation : Target who) :
    (target who deviation).IsBalanced (source who) := by
  refine ⟨simulation.mixing who deviation, 1 / 2, by norm_num, by norm_num, ?_⟩
  rw [simulation.prescribed, simulation.alternative]
  ext outcome
  rw [mix_apply, mix_apply, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, add_comm]

/-- **A simulation transfers incentives** for every utility integrable against
the source and target laws, on any outcome carrier. -/
theorem holds (simulation : IncentiveSimulation source target) (who : ι)
    (utility : Outcome → ℝ) (respected : ∀ original, (source who original).Holds utility)
    (integrable : ∀ original, PayoffIntegrable (source who original).prescribed utility ∧
      PayoffIntegrable (source who original).alternative utility)
    (deviation : Target who)
    (targetIntegrable : PayoffIntegrable (target who deviation).prescribed utility ∧
      PayoffIntegrable (target who deviation).alternative utility) :
    (target who deviation).Holds utility := by
  refine IncentiveComparison.IsBalanced.holds (mixing := simulation.mixing who deviation)
    (weight := 1 / 2) (by norm_num) (by norm_num) ?_ utility respected integrable ?_ ?_
    targetIntegrable.1 targetIntegrable.2
  · rw [simulation.prescribed, simulation.alternative]
    ext outcome
    rw [mix_apply, mix_apply, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, add_comm]
  · rw [← simulation.prescribed]
    exact targetIntegrable.1
  · rw [← simulation.alternative]
    exact targetIntegrable.2

/-- A finitely supported mixture of integrable source laws is integrable, so
finite simulations need integrability of the source laws only. -/
theorem holds_of_finite (simulation : IncentiveSimulation source target) (who : ι)
    (utility : Outcome → ℝ) (respected : ∀ original, (source who original).Holds utility)
    (integrable : ∀ original, PayoffIntegrable (source who original).prescribed utility ∧
      PayoffIntegrable (source who original).alternative utility)
    (deviation : Target who) (finite : (simulation.mixing who deviation).support.Finite) :
    (target who deviation).Holds utility := by
  refine simulation.holds who utility respected integrable deviation ⟨?_, ?_⟩
  · rw [simulation.prescribed]
    exact payoffIntegrable_bind_of_finite_support _ _ _ finite
      fun original _ => (integrable original).1
  · rw [simulation.alternative]
    exact payoffIntegrable_bind_of_finite_support _ _ _ finite
      fun original _ => (integrable original).2

/-- Every source incentive inequality implies every simulated target inequality. -/
theorem preserves (simulation : IncentiveSimulation source target)
    (utility : Outcome → ι → ℝ)
    (respected : ∀ who original, (source who original).Holds (utility · who))
    (integrable : ∀ who original,
      PayoffIntegrable (source who original).prescribed (utility · who) ∧
        PayoffIntegrable (source who original).alternative (utility · who))
    (targetIntegrable : ∀ who deviation,
      PayoffIntegrable (target who deviation).prescribed (utility · who) ∧
        PayoffIntegrable (target who deviation).alternative (utility · who)) :
    ∀ who deviation, (target who deviation).Holds (utility · who) :=
  fun who deviation => simulation.holds who (utility · who) (respected who) (integrable who)
    deviation (targetIntegrable who deviation)

/-- On a finite carrier a simulation is an implication between the families. -/
theorem implies [Fintype Outcome] (simulation : IncentiveSimulation source target) :
    IncentiveComparison.Implies source target :=
  fun utility respected => simulation.preserves utility respected
    (fun _ _ => ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _⟩)
    (fun _ _ => ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _⟩)

end IncentiveSimulation

/-! ## Balance is strictly weaker than simulation -/

namespace BalanceSeparation

open IncentiveComparison

/-- A source comparison: keep the `true` outcome rather than a fair lottery. -/
def source (_ : Unit) : IncentiveComparison Bool :=
  ⟨PMF.pure true, mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)⟩

/-- A target comparison with twice the source difference. -/
def target : IncentiveComparison Bool :=
  ⟨PMF.pure true, PMF.pure false⟩

/-- The target balances against the source with weight one third. -/
theorem target_isBalanced : target.IsBalanced source := by
  refine ⟨PMF.pure (), 1 / 3, by norm_num, by norm_num, ?_⟩
  ext outcome
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [mix_apply_toReal, mix_apply_toReal]
  cases outcome <;> simp [target, source] <;> norm_num

/-- No law-pair simulation represents the target: any mixture over the single
source comparison reproduces its lottery, not the target's certain `false`. -/
theorem not_simulated :
    IsEmpty (IncentiveSimulation (fun (_ : Unit) => source)
      fun (_ : Unit) (_ : Unit) => target) := by
  refine ⟨fun simulation => ?_⟩
  have hunit : simulation.mixing () () = PMF.pure () := by
    ext index
    cases index
    rw [PMF.pure_apply_self, PMF.apply_eq_one_iff]
    exact Set.eq_singleton_iff_unique_mem.mpr
      ⟨(simulation.mixing () ()).support_nonempty.some_mem, fun index _ => rfl⟩
  have halternative := simulation.alternative () ()
  rw [hunit, PMF.pure_bind] at halternative
  have hmass := congrArg (fun law : PMF Bool => (law true).toReal) halternative
  simp [target, source] at hmass

/-- **Balance is strictly weaker than law-pair simulation.** -/
theorem balance_strictly_weaker :
    target.IsBalanced source ∧
      IsEmpty (IncentiveSimulation (fun (_ : Unit) => source)
        fun (_ : Unit) (_ : Unit) => target) :=
  ⟨target_isBalanced, not_simulated⟩

end BalanceSeparation

end GameTheory
