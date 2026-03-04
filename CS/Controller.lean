import Math.Projection
import Math.ProbabilityMassFunction
import Math.SetReachability

set_option autoImplicit false

namespace CS
namespace Controller

open Math

variable {X Ω β γ : Type*}

/-- `Obs` is an alias for the projection/readout map abstraction. -/
abbrev Obs (X Ω : Type*) := Math.Projection.Map X Ω

/-- A randomized controller: choose a control token from an observation. -/
abbrev Stochastic (Ω β : Type*) := Ω → PMF β

/-- A deterministic controller (special case). -/
abbrev Deterministic (Ω β : Type*) := Ω → β

/-- Context-indexed action distribution induced by observation + controller. -/
def choose (obs : Obs X Ω) (ctrl : Stochastic Ω β) : X → PMF β :=
  fun x => ctrl (obs x)

/-- Context-indexed deterministic action induced by observation + controller. -/
def chooseDet (obs : Obs X Ω) (ctrl : Deterministic Ω β) : X → β :=
  fun x => ctrl (obs x)

/-- Closed-loop one-step kernel by composing observe -> control -> plant kernel. -/
noncomputable def closedLoop
    (obs : Obs X Ω)
    (ctrl : Stochastic Ω β)
    (plant : β → X → PMF γ) :
    X → PMF γ :=
  fun x => (ctrl (obs x)).bind (fun b => plant b x)

/-- Observation-indistinguishable points are equivalent for `f`. -/
def ObsInvariant (obs : Obs X Ω) (f : X → γ) : Prop :=
  ∀ ⦃x y : X⦄, obs x = obs y → f x = f y

/-- Reachability-local observation invariance. -/
def ObsInvariantOn (obs : Obs X Ω) (f : X → γ) (R : Set X) : Prop :=
  ∀ ⦃x y : X⦄, x ∈ R → y ∈ R → obs x = obs y → f x = f y

/-- Observation fibers are unique on `R` iff `obs` is injective on `R`. -/
abbrev ObsFiberUniqueOn (obs : Obs X Ω) (R : Set X) : Prop :=
  Set.InjOn obs R

/-- If two contexts have the same observation, `choose` agrees. -/
theorem choose_eq_of_obs_eq
    (obs : Obs X Ω) (ctrl : Stochastic Ω β)
    {x y : X} (hxy : obs x = obs y) :
    choose obs ctrl x = choose obs ctrl y := by
  simp [choose, hxy]

/-- Deterministic counterpart of `choose_eq_of_obs_eq`. -/
theorem chooseDet_eq_of_obs_eq
    (obs : Obs X Ω) (ctrl : Deterministic Ω β)
    {x y : X} (hxy : obs x = obs y) :
    chooseDet obs ctrl x = chooseDet obs ctrl y := by
  simp [chooseDet, hxy]

/-- If `f` factors through `obs`, then `f` is observation-invariant. -/
theorem obsInvariant_of_factorsThrough
    (obs : Obs X Ω) (f : X → γ)
    (hf : Math.Projection.FactorsThrough obs f) :
    ObsInvariant obs f := by
  intro x y hxy
  exact Math.Projection.eq_of_factorsThrough hf hxy

/-- Equality of observations on `R` implies equality of induced choices on `R`. -/
theorem choose_eqOn_of_obs_eqOn
    (obs₁ obs₂ : Obs X Ω) (ctrl : Stochastic Ω β) (R : Set X)
    (hobs : Set.EqOn obs₁ obs₂ R) :
    Set.EqOn (choose obs₁ ctrl) (choose obs₂ ctrl) R := by
  intro x hx
  simpa [choose] using congrArg ctrl (hobs hx)

/-- Equality of observations on `R` implies equality of deterministic choices on `R`. -/
theorem chooseDet_eqOn_of_obs_eqOn
    (obs₁ obs₂ : Obs X Ω) (ctrl : Deterministic Ω β) (R : Set X)
    (hobs : Set.EqOn obs₁ obs₂ R) :
    Set.EqOn (chooseDet obs₁ ctrl) (chooseDet obs₂ ctrl) R := by
  intro x hx
  simpa [chooseDet] using congrArg ctrl (hobs hx)

/-- Fiber-uniqueness schema on reachable domain (set-level form). -/
theorem eq_of_obs_eq_on_reachable
    (obs : Obs X Ω) (R : Set X)
    (hinj : ObsFiberUniqueOn obs R)
    {x y : X} (hx : x ∈ R) (hy : y ∈ R)
    (hxy : obs x = obs y) :
    x = y := by
  exact hinj hx hy hxy

/-- Fiber-uniqueness schema on PMF support (distribution form). -/
theorem eq_of_obs_eq_on_support
    (μ : PMF X) (obs : Obs X Ω)
    (hinj : ObsFiberUniqueOn obs μ.support)
    {x y : X} (hx : μ x ≠ 0) (hy : μ y ≠ 0)
    (hxy : obs x = obs y) :
    x = y := by
  exact hinj (by simpa [PMF.mem_support_iff] using hx)
    (by simpa [PMF.mem_support_iff] using hy) hxy

/-- Reachability-restricted congruence for induced choices (PMF bind form). -/
theorem bind_choose_eq_of_obs_eqOn_reachable
    (μ : PMF X)
    (obs₁ obs₂ : Obs X Ω)
    (ctrl : Stochastic Ω β)
    (R : Set X)
    (hsupp : μ.support ⊆ R)
    (hobs : Set.EqOn obs₁ obs₂ R) :
    μ.bind (choose obs₁ ctrl) = μ.bind (choose obs₂ ctrl) := by
  exact Math.Set.Reachability.bind_eq_of_eqOn_reachable
    μ R (choose obs₁ ctrl) (choose obs₂ ctrl) hsupp
    (choose_eqOn_of_obs_eqOn obs₁ obs₂ ctrl R hobs)

end Controller
end CS
